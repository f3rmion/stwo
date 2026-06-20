use core::mem;
use core::ops::Deref;

use serde::{Deserialize, Serialize};
use std_shims::Vec;

use crate::core::circle::CirclePoint;
use crate::core::fields::m31::BaseField;
use crate::core::fields::qm31::{SecureField, SECURE_EXTENSION_DEGREE};
use crate::core::fri::{FriLayerProof, FriProof};
use crate::core::pcs::quotients::{CommitmentSchemeProof, CommitmentSchemeProofAux};
use crate::core::vcs::hash::Hash;
use crate::core::vcs_lifted::merkle_hasher::MerkleHasherLifted;
use crate::core::vcs_lifted::verifier::MerkleDecommitmentLifted;

/// Recombines the `2^k` composition chunk evaluations (in split order) into the
/// composition's evaluation at `point`.
///
/// `chunk_log_degree_bound` is the chunks' committed log degree bound
/// (`composition_log_degree_bound - k`, i.e. `max_log_degree_bound`). The fold runs
/// deepest level first with multipliers `point.repeated_double(chunk_log_degree_bound
/// - 1 + i).x` for `i = 0..k`. With `k = 1` it is
/// `evals[0] + point.repeated_double(chunk_log_degree_bound - 1).x · evals[1]` — the
/// single `split_at_mid` recombination. Mirrors `SecureCirclePoly::split_k`.
pub(crate) fn recombine_split_evals(
    chunk_evals: &[SecureField],
    point: CirclePoint<SecureField>,
    chunk_log_degree_bound: u32,
    k: u32,
) -> SecureField {
    debug_assert_eq!(chunk_evals.len(), 1 << k);
    let mut level = chunk_evals.to_vec();
    for i in 0..k {
        let m = point.repeated_double(chunk_log_degree_bound - 1 + i).x;
        level = level.chunks(2).map(|pair| pair[0] + m * pair[1]).collect();
    }
    level[0]
}

#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct StarkProof<H: MerkleHasherLifted>(pub CommitmentSchemeProof<H>);

#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct ExtendedStarkProof<H: MerkleHasherLifted> {
    pub proof: StarkProof<H>,
    pub aux: CommitmentSchemeProofAux<H>,
}

impl<H: MerkleHasherLifted> StarkProof<H> {
    /// Extracts the composition trace Out-Of-Domain-Sample evaluation from the mask.
    ///
    /// The composition is committed as `2^composition_log_split` chunks (each
    /// `SECURE_EXTENSION_DEGREE` coordinate columns), produced by splitting the
    /// composition `composition_log_split` times (`k = composition_log_degree_bound
    /// - max_log_degree_bound`). The chunk evaluations recombine via
    /// [`recombine_split_evals`]. With `composition_log_split = 1` this is the
    /// `left + π·right` single split.
    pub(crate) fn extract_composition_oods_eval(
        &self,
        oods_point: CirclePoint<SecureField>,
        max_log_degree_bound: u32,
        composition_log_split: u32,
    ) -> Option<SecureField> {
        let [.., composition_mask] = &**self.sampled_values else {
            return None;
        };
        let n_cols = (1usize << composition_log_split) * SECURE_EXTENSION_DEGREE;
        if composition_mask.len() != n_cols {
            return None;
        }
        let coord_evals = composition_mask
            .iter()
            .map(|columns| match &columns[..] {
                &[eval] => Some(eval),
                _ => None,
            })
            .collect::<Option<Vec<_>>>()?;
        let chunk_evals: Vec<SecureField> = coord_evals
            .chunks(SECURE_EXTENSION_DEGREE)
            .map(|coords| SecureField::from_partial_evals(coords.try_into().unwrap()))
            .collect();
        Some(recombine_split_evals(
            &chunk_evals,
            oods_point,
            max_log_degree_bound,
            composition_log_split,
        ))
    }

    /// Extracts the masked composition trace OODS evaluation `q'(ζ)` from the mask.
    ///
    /// Mirrors [`Self::extract_composition_oods_eval`] (same `2^composition_log_split`
    /// chunk recombination) but reads the chunk columns from the SECOND-TO-LAST
    /// sampled-values tree — the last tree holds the unsplit composition randomizer
    /// `t` — and skips that tree's trailing Layer-0 salt column. `max_log_degree_bound`
    /// is the lifted degree bound (the forced randomizer lifting), so the recombination
    /// runs in the lifted frame, matching `t` opened at `repeated_double(k)`.
    #[cfg(feature = "statistical-zk")]
    pub(crate) fn extract_composition_oods_eval_zk(
        &self,
        oods_point: CirclePoint<SecureField>,
        max_log_degree_bound: u32,
        composition_log_split: u32,
    ) -> Option<SecureField> {
        let [.., composition_mask, _t_mask] = &**self.sampled_values else {
            return None;
        };
        let n_cols = (1usize << composition_log_split) * SECURE_EXTENSION_DEGREE;
        // The composition tree carries a trailing Layer-0 salt column with no OODS
        // sample; take only the `2^k` split-chunk coordinate columns.
        let coord_evals = composition_mask
            .iter()
            .take(n_cols)
            .map(|columns| match &columns[..] {
                &[eval] => Some(eval),
                _ => None,
            })
            .collect::<Option<Vec<_>>>()?;
        if coord_evals.len() != n_cols {
            return None;
        }
        let chunk_evals: Vec<SecureField> = coord_evals
            .chunks(SECURE_EXTENSION_DEGREE)
            .map(|coords| SecureField::from_partial_evals(coords.try_into().unwrap()))
            .collect();
        Some(recombine_split_evals(
            &chunk_evals,
            oods_point,
            max_log_degree_bound,
            composition_log_split,
        ))
    }

    /// Extracts the composition randomizer OODS evaluation `t(ζ)` from the mask.
    ///
    /// The randomizer is committed and opened unsplit as one secure polynomial:
    /// its four coordinate columns each hold a single evaluation at `ζ`, combined
    /// into the secure value `t(ζ)`.
    #[cfg(feature = "statistical-zk")]
    pub(crate) fn extract_t_oods_eval(&self) -> Option<SecureField> {
        let t_mask = self.sampled_values.last()?;
        // The t tree carries a trailing Layer-0 salt column with no OODS sample;
        // take only the unsplit randomizer coordinate columns.
        let coordinate_evals: [SecureField; SECURE_EXTENSION_DEGREE] = t_mask
            .iter()
            .take(SECURE_EXTENSION_DEGREE)
            .map(|columns| {
                let &[eval] = &columns[..] else {
                    return None;
                };
                Some(eval)
            })
            .collect::<Option<Vec<_>>>()?
            .try_into()
            .ok()?;
        Some(SecureField::from_partial_evals(coordinate_evals))
    }

    /// Returns the estimate size (in bytes) of the proof.
    pub fn size_estimate(&self) -> usize {
        SizeEstimate::size_estimate(self)
    }

    /// Returns size estimates (in bytes) for different parts of the proof.
    pub fn size_breakdown_estimate(&self) -> StarkProofSizeBreakdown {
        let Self(commitment_scheme_proof) = self;

        let CommitmentSchemeProof {
            commitments,
            sampled_values,
            decommitments,
            queried_values,
            proof_of_work: _,
            fri_proof,
            config: _,
        } = commitment_scheme_proof;

        let FriProof {
            first_layer,
            inner_layers,
            last_layer_poly,
        } = fri_proof;

        let mut inner_layers_samples_size = 0;
        let mut inner_layers_hashes_size = 0;

        for FriLayerProof {
            fri_witness,
            decommitment,
            commitment,
        } in inner_layers
        {
            inner_layers_samples_size += fri_witness.size_estimate();
            inner_layers_hashes_size += decommitment.size_estimate() + commitment.size_estimate();
        }

        StarkProofSizeBreakdown {
            oods_samples: sampled_values.size_estimate(),
            queries_values: queried_values.size_estimate(),
            fri_samples: last_layer_poly.size_estimate()
                + inner_layers_samples_size
                + first_layer.fri_witness.size_estimate(),
            fri_decommitments: inner_layers_hashes_size
                + first_layer.decommitment.size_estimate()
                + first_layer.commitment.size_estimate(),
            trace_decommitments: commitments.size_estimate() + decommitments.size_estimate(),
        }
    }
}

impl<H: MerkleHasherLifted> Deref for StarkProof<H> {
    type Target = CommitmentSchemeProof<H>;

    fn deref(&self) -> &CommitmentSchemeProof<H> {
        &self.0
    }
}

/// Size estimate (in bytes) for different parts of the proof.
#[derive(Debug)]
pub struct StarkProofSizeBreakdown {
    pub oods_samples: usize,
    pub queries_values: usize,
    pub fri_samples: usize,
    pub fri_decommitments: usize,
    pub trace_decommitments: usize,
}

trait SizeEstimate {
    fn size_estimate(&self) -> usize;
}

impl<T: SizeEstimate> SizeEstimate for [T] {
    fn size_estimate(&self) -> usize {
        self.iter().map(|v| v.size_estimate()).sum()
    }
}

impl<T: SizeEstimate> SizeEstimate for Vec<T> {
    fn size_estimate(&self) -> usize {
        self.iter().map(|v| v.size_estimate()).sum()
    }
}

impl<H: Hash> SizeEstimate for H {
    fn size_estimate(&self) -> usize {
        mem::size_of::<Self>()
    }
}

impl SizeEstimate for BaseField {
    fn size_estimate(&self) -> usize {
        mem::size_of::<Self>()
    }
}

impl SizeEstimate for SecureField {
    fn size_estimate(&self) -> usize {
        mem::size_of::<Self>()
    }
}

impl<H: MerkleHasherLifted> SizeEstimate for MerkleDecommitmentLifted<H> {
    fn size_estimate(&self) -> usize {
        let Self { hash_witness } = self;
        hash_witness.size_estimate()
    }
}

impl<H: MerkleHasherLifted> SizeEstimate for FriLayerProof<H> {
    fn size_estimate(&self) -> usize {
        let Self {
            fri_witness,
            decommitment,
            commitment,
        } = self;
        fri_witness.size_estimate() + decommitment.size_estimate() + commitment.size_estimate()
    }
}

impl<H: MerkleHasherLifted> SizeEstimate for FriProof<H> {
    fn size_estimate(&self) -> usize {
        let Self {
            first_layer,
            inner_layers,
            last_layer_poly,
        } = self;
        first_layer.size_estimate() + inner_layers.size_estimate() + last_layer_poly.size_estimate()
    }
}

impl<H: MerkleHasherLifted> SizeEstimate for CommitmentSchemeProof<H> {
    fn size_estimate(&self) -> usize {
        let Self {
            commitments,
            sampled_values,
            decommitments,
            queried_values,
            proof_of_work,
            fri_proof,
            config,
        } = self;
        commitments.size_estimate()
            + sampled_values.size_estimate()
            + decommitments.size_estimate()
            + queried_values.size_estimate()
            + mem::size_of_val(proof_of_work)
            + fri_proof.size_estimate()
            + mem::size_of_val(config)
    }
}

impl<H: MerkleHasherLifted> SizeEstimate for StarkProof<H> {
    fn size_estimate(&self) -> usize {
        let Self(commitment_scheme_proof) = self;
        commitment_scheme_proof.size_estimate()
    }
}

#[cfg(test)]
mod tests {
    use num_traits::One;

    use crate::core::fields::m31::BaseField;
    use crate::core::fields::qm31::{SecureField, SECURE_EXTENSION_DEGREE};
    use crate::core::proof::SizeEstimate;

    #[test]
    fn test_base_field_size_estimate() {
        assert_eq!(BaseField::one().size_estimate(), 4);
    }

    #[test]
    fn test_secure_field_size_estimate() {
        assert_eq!(
            SecureField::one().size_estimate(),
            4 * SECURE_EXTENSION_DEGREE
        );
    }
}
