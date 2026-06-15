use std_shims::{vec, String};
use thiserror::Error;

use crate::core::air::{Component, Components};
use crate::core::channel::{Channel, MerkleChannel};
use crate::core::circle::CirclePoint;
use crate::core::fields::qm31::{SecureField, SECURE_EXTENSION_DEGREE};
use crate::core::fri::FriVerificationError;
use crate::core::pcs::utils::try_get_lifting_log_size;
use crate::core::pcs::CommitmentSchemeVerifier;
use crate::core::proof::StarkProof;
use crate::core::vcs_lifted::verifier::MerkleVerificationError;
pub const PREPROCESSED_TRACE_IDX: usize = 0;

// TODO(Leo): remove this once the composition poly split can be dependant on a config instead of
// being hardcoded.
pub const COMPOSITION_LOG_SPLIT: u32 = 1;

pub fn verify<MC: MerkleChannel>(
    components: &[&dyn Component],
    channel: &mut MC::C,
    commitment_scheme: &mut CommitmentSchemeVerifier<MC>,
    proof: StarkProof<MC::H>,
) -> Result<(), VerificationError> {
    let include_all_preprocessed_columns = false;
    verify_ex(
        components,
        channel,
        commitment_scheme,
        proof,
        include_all_preprocessed_columns,
    )
}

pub fn verify_ex<MC: MerkleChannel>(
    components: &[&dyn Component],
    channel: &mut MC::C,
    commitment_scheme: &mut CommitmentSchemeVerifier<MC>,
    proof: StarkProof<MC::H>,
    include_all_preprocessed_columns: bool,
) -> Result<(), VerificationError> {
    let n_preprocessed_columns = commitment_scheme.trees[PREPROCESSED_TRACE_IDX]
        .column_log_sizes
        .len();

    let components = Components {
        components: components.to_vec(),
        n_preprocessed_columns,
    };
    let split_composition_log_degree_bound =
        components.composition_log_degree_bound() - COMPOSITION_LOG_SPLIT;
    tracing::info!(
        "Split composition polynomial log degree bound: {}",
        split_composition_log_degree_bound
    );

    // If `self.config.lifting_log_size` is None, the lifting size is the length of the split
    // composition polynomials' domain.
    let lifting_log_size = try_get_lifting_log_size(
        &commitment_scheme.config,
        split_composition_log_degree_bound + commitment_scheme.config.fri_config.log_blowup_factor,
    )?;
    if include_all_preprocessed_columns {
        let preprocessed_trace_height = commitment_scheme.trees[PREPROCESSED_TRACE_IDX].height;
        if lifting_log_size < preprocessed_trace_height {
            Err(crate::core::pcs::utils::InvalidLiftingLogSizeError {
                lifting_log_size,
                min_log_size: preprocessed_trace_height,
            })?;
        }
    }

    // The max degree of a committed polynomial. If `lifting_log_size` is not set,
    // the largest degree is attained by the splits of the composition polynomial.
    let max_log_degree_bound =
        lifting_log_size - commitment_scheme.config.fri_config.log_blowup_factor;

    let random_coeff = channel.draw_secure_felt();

    // Read composition polynomial commitment.
    commitment_scheme.commit(
        *proof.commitments.last().unwrap(),
        &[max_log_degree_bound; 2 * SECURE_EXTENSION_DEGREE],
        channel,
    );

    // Draw OODS point.
    let oods_point = CirclePoint::<SecureField>::get_random_point(channel);
    // Get mask sample points relative to oods point.
    let mut sample_points = components.mask_points(
        oods_point,
        max_log_degree_bound,
        include_all_preprocessed_columns,
    );
    // Add the composition polynomial mask points.
    sample_points.push(vec![vec![oods_point]; 2 * SECURE_EXTENSION_DEGREE]);

    let sample_points_by_column = sample_points.as_cols_ref().flatten();
    tracing::info!("Sampling {} columns.", sample_points_by_column.len());
    tracing::info!(
        "Total sample points: {}.",
        sample_points_by_column.into_iter().flatten().count()
    );

    let composition_oods_eval = proof
        .extract_composition_oods_eval(oods_point, max_log_degree_bound)
        .ok_or(VerificationError::InvalidStructure(
            std_shims::ToString::to_string(&"Unexpected sampled_values structure"),
        ))?;

    if composition_oods_eval
        != components.eval_composition_polynomial_at_point(
            oods_point,
            &proof.sampled_values,
            random_coeff,
            max_log_degree_bound,
        )
    {
        return Err(VerificationError::OodsNotMatching);
    }
    commitment_scheme.verify_values(sample_points, proof.0, channel)
}

/// Statistical zero-knowledge verifier path.
///
/// Mirrors [`verify_ex`] but reads two composition-side commitments: the split
/// halves of the masked composition `q'` (second-to-last commitment) and the
/// unsplit composition randomizer `t` (last commitment). The DEEP-ALI check
/// compares `q'(ζ) - t(ζ)` against the trace-derived composition value.
#[cfg(feature = "statistical-zk")]
pub fn verify_zk<MC: MerkleChannel>(
    components: &[&dyn Component],
    channel: &mut MC::C,
    commitment_scheme: &mut CommitmentSchemeVerifier<MC>,
    proof: StarkProof<MC::H>,
    include_all_preprocessed_columns: bool,
) -> Result<(), VerificationError> {
    let n_preprocessed_columns = commitment_scheme.trees[PREPROCESSED_TRACE_IDX]
        .column_log_sizes
        .len();

    let components = Components {
        components: components.to_vec(),
        n_preprocessed_columns,
    };
    let split_composition_log_degree_bound =
        components.composition_log_degree_bound() - COMPOSITION_LOG_SPLIT;
    tracing::info!(
        "Split composition polynomial log degree bound: {}",
        split_composition_log_degree_bound
    );

    // The global lifting pins every committed tree to the height of the tallest
    // tree, the unsplit randomizer at one log size above the split composition
    // chunks. `max_log_degree_bound` follows that lifting (matching the prover), so
    // mask-point translation, chunk recombination and constraint evaluation share
    // the subdomain fold the chunks undergo.
    let lifting_log_size = try_get_lifting_log_size(
        &commitment_scheme.config,
        split_composition_log_degree_bound + commitment_scheme.config.fri_config.log_blowup_factor,
    )?;
    if include_all_preprocessed_columns {
        let preprocessed_trace_height = commitment_scheme.trees[PREPROCESSED_TRACE_IDX].height;
        if lifting_log_size < preprocessed_trace_height {
            Err(crate::core::pcs::utils::InvalidLiftingLogSizeError {
                lifting_log_size,
                min_log_size: preprocessed_trace_height,
            })?;
        }
    }
    let max_log_degree_bound =
        lifting_log_size - commitment_scheme.config.fri_config.log_blowup_factor;

    let random_coeff = channel.draw_secure_felt();

    // Read masked composition polynomial commitment (second-to-last commitment).
    // The split chunks are committed at the split composition degree bound; the
    // global lifting pins their tree height to the taller randomizer tree.
    let composition_commitment_index = proof.commitments.len() - 2;
    commitment_scheme.commit(
        proof.commitments[composition_commitment_index],
        &[split_composition_log_degree_bound; 2 * SECURE_EXTENSION_DEGREE],
        channel,
    );

    // Read composition randomizer commitment (last commitment). Its unsplit
    // coordinate columns live at the full composition log size, one above the
    // split chunks.
    commitment_scheme.commit(
        *proof.commitments.last().unwrap(),
        &[split_composition_log_degree_bound + COMPOSITION_LOG_SPLIT; SECURE_EXTENSION_DEGREE],
        channel,
    );

    // Draw OODS point.
    let oods_point = CirclePoint::<SecureField>::get_random_point(channel);
    // Get mask sample points relative to oods point.
    let mut sample_points = components.mask_points(
        oods_point,
        max_log_degree_bound,
        include_all_preprocessed_columns,
    );
    // Add the composition polynomial mask points.
    sample_points.push(vec![vec![oods_point]; 2 * SECURE_EXTENSION_DEGREE]);
    // Add the composition randomizer mask points. The randomizer lives one log size
    // above the split composition chunks, so to open it at the same effective point
    // the chunks fold to, its sample point is pre-folded by the split depth.
    let randomizer_oods_point = oods_point.repeated_double(COMPOSITION_LOG_SPLIT);
    sample_points.push(vec![vec![randomizer_oods_point]; SECURE_EXTENSION_DEGREE]);

    let composition_oods_eval = proof
        .extract_composition_oods_eval_zk(oods_point, max_log_degree_bound)
        .ok_or(VerificationError::InvalidStructure(
            std_shims::ToString::to_string(&"Unexpected sampled_values structure"),
        ))?;
    let t_oods_eval =
        proof
            .extract_t_oods_eval()
            .ok_or(VerificationError::InvalidStructure(
                std_shims::ToString::to_string(&"Unexpected sampled_values structure"),
            ))?;

    if composition_oods_eval - t_oods_eval
        != components.eval_composition_polynomial_at_point(
            oods_point,
            &proof.sampled_values,
            random_coeff,
            max_log_degree_bound,
        )
    {
        return Err(VerificationError::OodsNotMatching);
    }
    commitment_scheme.verify_values(sample_points, proof.0, channel)
}

#[derive(Clone, Debug, Error)]
pub enum VerificationError {
    #[error("Proof has invalid structure: {0}.")]
    InvalidStructure(String),
    #[error(transparent)]
    Merkle(#[from] MerkleVerificationError),
    #[error(
        "The composition polynomial OODS value does not match the trace OODS values
    (DEEP-ALI failure)."
    )]
    OodsNotMatching,
    #[error(transparent)]
    Fri(#[from] FriVerificationError),
    #[error("Proof of work verification failed.")]
    ProofOfWork,
    #[error(transparent)]
    InvalidLiftingLogSize(#[from] crate::core::pcs::utils::InvalidLiftingLogSizeError),
    #[error(transparent)]
    InvalidCanonicCosetLogSize(#[from] crate::core::poly::circle::InvalidCanonicCosetLogSize),
}
