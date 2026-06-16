use thiserror::Error;
use tracing::{info, instrument, span, Level};

use crate::core::channel::{Channel, MerkleChannel};
use crate::core::circle::CirclePoint;
use crate::core::fields::qm31::{SecureField, SECURE_EXTENSION_DEGREE};
use crate::core::pcs::utils::{try_get_lifting_log_size, InvalidLiftingLogSizeError};
use crate::core::proof::{ExtendedStarkProof, StarkProof};
use crate::core::verifier::PREPROCESSED_TRACE_IDX;
use crate::prover::backend::BackendForChannel;

mod air;
pub use air::component_prover::{ComponentProver, ComponentProvers, Poly, Trace};
pub use air::{AccumulationOps, ColumnAccumulator, DomainEvaluationAccumulator, EvaluationMode};
pub mod pcs;
pub use pcs::quotient_ops::QuotientOps;
pub use pcs::{CommitmentSchemeProver, CommitmentTreeProver, TreeBuilder};
pub mod backend;
pub mod channel;
pub mod fri;
pub mod line;
pub mod lookups;
pub mod mempool;
pub mod poly;
pub mod secure_column;
#[cfg(feature = "statistical-zk")]
pub mod statistical_zk;
#[cfg(all(test, feature = "statistical-zk"))]
mod statistical_zk_rank_check;
pub mod vcs;
pub mod vcs_lifted;

pub fn prove<B: BackendForChannel<MC>, MC: MerkleChannel>(
    components: &[&dyn ComponentProver<B>],
    channel: &mut MC::C,
    commitment_scheme: CommitmentSchemeProver<'_, B, MC>,
) -> Result<StarkProof<MC::H>, ProvingError> {
    Ok(prove_ex(components, channel, commitment_scheme, false)?.proof)
}

#[instrument(skip_all)]
pub fn prove_ex<B: BackendForChannel<MC>, MC: MerkleChannel>(
    components: &[&dyn ComponentProver<B>],
    channel: &mut MC::C,
    mut commitment_scheme: CommitmentSchemeProver<'_, B, MC>,
    include_all_preprocessed_columns: bool,
) -> Result<ExtendedStarkProof<MC::H>, ProvingError> {
    let n_preprocessed_columns = commitment_scheme.trees[PREPROCESSED_TRACE_IDX]
        .polynomials
        .len();
    let component_provers = ComponentProvers {
        components: components.to_vec(),
        n_preprocessed_columns,
    };
    let trace = commitment_scheme.trace();

    // Evaluate and commit on composition polynomial.
    let random_coeff = channel.draw_secure_felt();

    let span = span!(Level::INFO, "Composition", class = "Composition").entered();
    let span1 = span!(
        Level::INFO,
        "Generation",
        class = "CompositionPolynomialGeneration"
    )
    .entered();

    let composition_poly = component_provers.compute_composition_polynomial(
        random_coeff,
        &trace,
        commitment_scheme.twiddles,
        commitment_scheme.config.fri_config.log_blowup_factor,
    );
    span1.exit();

    // Commit on the Composition Polynomial by splitting its coeffs to two polynomialsof degree
    // half the size of the original polynomial, and commit on each half separately.
    let mut tree_builder = commitment_scheme.tree_builder();
    let (left_comp_poly_half, right_comp_poly_half) = composition_poly.split_at_mid();

    tree_builder.extend_polys(left_comp_poly_half.into_coordinate_polys());
    tree_builder.extend_polys(right_comp_poly_half.into_coordinate_polys());
    tree_builder.commit(channel);
    span.exit();

    // Draw OODS point.
    let oods_point = CirclePoint::<SecureField>::get_random_point(channel);

    let split_composition_log_size = commitment_scheme
        .trees
        .last()
        .unwrap()
        .commitment
        .layers
        .len() as u32
        - 1;

    // If `self.config.lifting_log_size` is None, the lifting size is the length of the split
    // composition polynomials' domain.
    let lifting_log_size =
        try_get_lifting_log_size(&commitment_scheme.config, split_composition_log_size)?;
    if include_all_preprocessed_columns {
        // If all the preprocessed columns are included, the lifting log size must be greater than
        // or equal to the preprocessed log size.
        let preprocessed_log_size = commitment_scheme.trees[PREPROCESSED_TRACE_IDX]
            .commitment
            .layers
            .len() as u32
            - 1;
        if lifting_log_size < preprocessed_log_size {
            Err(InvalidLiftingLogSizeError {
                lifting_log_size,
                min_log_size: preprocessed_log_size,
            })?;
        }
    }
    let max_log_degree_bound =
        lifting_log_size - commitment_scheme.config.fri_config.log_blowup_factor;

    // Get mask sample points relative to oods point.
    let mut sample_points = component_provers.components().mask_points(
        oods_point,
        max_log_degree_bound,
        include_all_preprocessed_columns,
    );

    // Add the composition polynomial mask points.
    sample_points.push(vec![vec![oods_point]; 2 * SECURE_EXTENSION_DEGREE]);

    // Prove the trace and composition OODS values, and retrieve them.
    let commitment_scheme_proof = commitment_scheme.prove_values(sample_points, channel);
    let proof = StarkProof(commitment_scheme_proof.proof);
    info!(proof_size_estimate = proof.size_estimate());

    // Evaluate composition polynomial at OODS point and check that it matches the trace OODS
    // values. This is a sanity check.
    if proof
        .extract_composition_oods_eval(oods_point, max_log_degree_bound)
        .unwrap()
        != component_provers
            .components()
            .eval_composition_polynomial_at_point(
                oods_point,
                &proof.sampled_values,
                random_coeff,
                max_log_degree_bound,
            )
    {
        return Err(ProvingError::ConstraintsNotSatisfied);
    }

    Ok(ExtendedStarkProof {
        proof,
        aux: commitment_scheme_proof.aux,
    })
}

/// Statistical zero-knowledge prover path.
///
/// Masks the committed composition quotient `q` by an independent random secure
/// polynomial `t`: it commits the split halves of `q' = q + t` as the transparent
/// path does, then commits `t` unsplit as a separate tree last. The verifier
/// reconstructs `q'(ζ)` and `t(ζ)` from their openings and checks
/// `q'(ζ) - t(ζ)` against the trace-derived composition value.
///
/// `randomizer_dimension` controls how many independent base-field coefficients
/// each of `t`'s four coordinate polynomials carries. This path does not mask the
/// trace columns.
#[cfg(feature = "statistical-zk")]
#[instrument(skip_all)]
pub fn prove_zk<B: BackendForChannel<MC>, MC: MerkleChannel>(
    components: &[&dyn ComponentProver<B>],
    channel: &mut MC::C,
    mut commitment_scheme: CommitmentSchemeProver<'_, B, MC>,
    rng: &mut (impl rand::RngCore + rand::CryptoRng),
    randomizer_dimension: usize,
) -> Result<ExtendedStarkProof<MC::H>, ProvingError> {
    use crate::prover::statistical_zk::{
        add_composition_randomizer, required_composition_randomizer_dimension,
        sample_composition_randomizer, sample_salt_column, WitnessMaskError,
    };

    // Fail closed if the composition randomizer `t` is below the reconstruction-
    // resistance budget derived from the real opening counts: the composition is
    // OODS-sampled at ζ only (n_F^comp = 1) and queried at n_D positions, so
    // `h_t` must exceed `n_F^comp + n_D` (equivalently `4·h_t > e·(n_F^comp + n_D)`)
    // or the verifier could interpolate `t`, split it, and strip the mask.
    let required_t_dimension =
        required_composition_randomizer_dimension(1, commitment_scheme.config.fri_config.n_queries);
    if randomizer_dimension < required_t_dimension {
        Err(WitnessMaskError::CompositionRandomizerBudgetTooSmall {
            dimension: randomizer_dimension,
            required: required_t_dimension,
        })?;
    }

    let include_all_preprocessed_columns = false;
    let n_preprocessed_columns = commitment_scheme.trees[PREPROCESSED_TRACE_IDX]
        .polynomials
        .len();
    let component_provers = ComponentProvers {
        components: components.to_vec(),
        n_preprocessed_columns,
    };
    let trace = commitment_scheme.trace();

    // Evaluate and commit on composition polynomial.
    let random_coeff = channel.draw_secure_felt();

    let span = span!(Level::INFO, "Composition", class = "Composition").entered();
    let span1 = span!(
        Level::INFO,
        "Generation",
        class = "CompositionPolynomialGeneration"
    )
    .entered();

    let composition_poly = component_provers.compute_composition_polynomial(
        random_coeff,
        &trace,
        commitment_scheme.twiddles,
        commitment_scheme.config.fri_config.log_blowup_factor,
    );
    span1.exit();

    // Draw the composition randomizer `t` and mask the composition: q' = q + t.
    let composition_log_size = composition_poly.log_size();
    let t = sample_composition_randomizer::<B, _>(composition_log_size, randomizer_dimension, rng)?;
    let composition_poly = add_composition_randomizer(composition_poly, &t)?;

    // Compute the global lifting up front (before committing) so the Layer-0 salt
    // columns can be sized at leaf size (`lifting - log_blowup`); at leaf size a
    // salt value is not replicated across leaves, so opening one leaf never reveals
    // an unopened leaf's salt. The lifting must pin every committed tree to one
    // height so the taller randomizer tree does not introduce a per-tree fold
    // mismatch in FRI decommitment.
    let log_blowup = commitment_scheme.config.fri_config.log_blowup_factor;
    let split_composition_log_size =
        composition_log_size - crate::core::verifier::COMPOSITION_LOG_SPLIT + log_blowup;
    let lifting_log_size =
        try_get_lifting_log_size(&commitment_scheme.config, split_composition_log_size)?;
    let max_log_degree_bound = lifting_log_size - log_blowup;

    // Fail closed unless the configured lifting already accommodates the unsplit
    // randomizer tree (one log size above the split chunks) AND the salt columns
    // land exactly at leaf size. Without this, committed trees would have
    // mismatched heights / FRI decommitment positions, or salt values would be
    // replicated across leaves.
    let randomizer_lifting_log_size = composition_log_size + log_blowup;
    if lifting_log_size != randomizer_lifting_log_size {
        Err(crate::core::pcs::utils::InvalidLiftingLogSizeError {
            lifting_log_size,
            min_log_size: randomizer_lifting_log_size,
        })?;
    }

    // Commit on the masked composition polynomial by splitting its coeffs to two polynomials of
    // degree half the size of the original polynomial, and commit on each half separately. A
    // leaf-size Layer-0 salt column (no OODS sample) is appended so the tree's leaf hashes hide.
    let mut tree_builder = commitment_scheme.tree_builder();
    let (left_comp_poly_half, right_comp_poly_half) = composition_poly.split_at_mid();

    tree_builder.extend_polys(left_comp_poly_half.into_coordinate_polys());
    tree_builder.extend_polys(right_comp_poly_half.into_coordinate_polys());
    tree_builder.extend_polys(vec![sample_salt_column::<B, _>(max_log_degree_bound, rng)]);
    tree_builder.commit(channel);
    span.exit();

    // Commit on the composition randomizer `t` unsplit, as a separate tree committed last, with
    // its own leaf-size Layer-0 salt column. Its four coordinate polynomials live at the full
    // composition log size.
    let mut t_tree_builder = commitment_scheme.tree_builder();
    t_tree_builder.extend_polys(t.into_coordinate_polys());
    t_tree_builder.extend_polys(vec![sample_salt_column::<B, _>(max_log_degree_bound, rng)]);
    t_tree_builder.commit(channel);

    // Draw OODS point.
    let oods_point = CirclePoint::<SecureField>::get_random_point(channel);

    // Get mask sample points relative to oods point.
    let mut sample_points = component_provers.components().mask_points(
        oods_point,
        max_log_degree_bound,
        include_all_preprocessed_columns,
    );

    // Add the composition polynomial mask points; the trailing Layer-0 salt column
    // gets no OODS sample (empty), so it never enters the FRI quotient.
    let mut composition_sample_points = vec![vec![oods_point]; 2 * SECURE_EXTENSION_DEGREE];
    composition_sample_points.push(vec![]);
    sample_points.push(composition_sample_points);
    // Add the composition randomizer mask points. The randomizer lives one log
    // size above the split composition chunks, so to open it at the same effective
    // point the chunks fold to, its sample point is pre-folded by the split depth.
    // Its trailing Layer-0 salt column also gets no OODS sample.
    let randomizer_oods_point =
        oods_point.repeated_double(crate::core::verifier::COMPOSITION_LOG_SPLIT);
    let mut t_sample_points = vec![vec![randomizer_oods_point]; SECURE_EXTENSION_DEGREE];
    t_sample_points.push(vec![]);
    sample_points.push(t_sample_points);

    // Prove the trace and composition OODS values, and retrieve them.
    let commitment_scheme_proof = commitment_scheme.prove_values(sample_points, channel);
    let proof = StarkProof(commitment_scheme_proof.proof);
    info!(proof_size_estimate = proof.size_estimate());

    // Evaluate the masked composition polynomial at the OODS point and check that
    // `q'(ζ) - t(ζ)` matches the trace OODS values. This is a sanity check.
    let q_prime_at = proof
        .extract_composition_oods_eval_zk(oods_point, max_log_degree_bound)
        .ok_or(ProvingError::ConstraintsNotSatisfied)?;
    let t_at = proof
        .extract_t_oods_eval()
        .ok_or(ProvingError::ConstraintsNotSatisfied)?;
    if q_prime_at - t_at
        != component_provers
            .components()
            .eval_composition_polynomial_at_point(
                oods_point,
                &proof.sampled_values,
                random_coeff,
                max_log_degree_bound,
            )
    {
        return Err(ProvingError::ConstraintsNotSatisfied);
    }

    Ok(ExtendedStarkProof {
        proof,
        aux: commitment_scheme_proof.aux,
    })
}

#[derive(Clone, Copy, Debug, Error)]
pub enum ProvingError {
    #[error("Constraints not satisfied.")]
    ConstraintsNotSatisfied,
    #[error(transparent)]
    InvalidLiftingLogSize(#[from] crate::core::pcs::utils::InvalidLiftingLogSizeError),
    #[error(transparent)]
    InvalidCanonicCosetLogSize(#[from] crate::core::poly::circle::InvalidCanonicCosetLogSize),
    #[cfg(feature = "statistical-zk")]
    #[error(transparent)]
    WitnessMask(#[from] crate::prover::statistical_zk::WitnessMaskError),
}
