//! Balanced LogUp fixture: a permutation argument whose `claimed_sum` is `0`.
//!
//! Two base-trace columns `A` and `B` hold the same multiset (`A = 0..n`,
//! `B = A` reversed). The single LogUp relation adds `+[A]` and removes `−[B]`,
//! so the total `Σ 1/q_A − Σ 1/q_B` cancels to `0` for every witness. Unlike the
//! fibonacci PLONK fixture (deliberately unbalanced, `claimed_sum` a nonzero
//! functional of the private multiplicities), this fixture is the sound shape a
//! dark-pool circuit must take: a balanced `claimed_sum` leaks nothing, so the
//! verifier can enforce `claimed_sum == 0` via `assert_lookup_balanced`.

use num_traits::{One, Zero};
use stwo::core::channel::Blake2sChannel;
use stwo::core::fields::m31::BaseField;
use stwo::core::fields::qm31::SecureField;
use stwo::core::pcs::PcsConfig;
use stwo::core::poly::circle::CanonicCoset;
use stwo::core::vcs_lifted::blake2_merkle::{Blake2sMerkleChannel, Blake2sMerkleHasher};
use stwo::core::ColumnVec;
use stwo::prover::backend::simd::column::BaseColumn;
use stwo::prover::backend::simd::m31::LOG_N_LANES;
use stwo::prover::backend::simd::qm31::PackedSecureField;
use stwo::prover::backend::simd::SimdBackend;
use stwo::prover::poly::circle::{CircleEvaluation, PolyOps};
use stwo::prover::poly::BitReversedOrder;
use stwo_constraint_framework::logup::LookupElements;
use stwo_constraint_framework::{
    relation, EvalAtRow, FrameworkComponent, FrameworkEval, LogupTraceGenerator, RelationEntry,
    TraceLocationAllocator,
};

pub type BalancedComponent = FrameworkComponent<BalancedEval>;

relation!(BalancedElements, 1);

#[derive(Clone)]
pub struct BalancedEval {
    pub log_n_rows: u32,
    pub lookup_elements: BalancedElements,
    pub claimed_sum: SecureField,
}

impl FrameworkEval for BalancedEval {
    fn log_size(&self) -> u32 {
        self.log_n_rows
    }

    fn max_constraint_log_degree_bound(&self) -> u32 {
        self.log_n_rows + 1
    }

    fn evaluate<E: EvalAtRow>(&self, mut eval: E) -> E {
        let a = eval.next_trace_mask();
        let b = eval.next_trace_mask();

        // Add the value on column A, remove the value on column B. Balanced
        // because {A} == {B} as multisets.
        eval.add_to_relation(RelationEntry::new(&self.lookup_elements, E::EF::one(), &[a]));
        eval.add_to_relation(RelationEntry::new(&self.lookup_elements, -E::EF::one(), &[b]));

        eval.finalize_logup_in_pairs();
        eval
    }
}

/// Build the two balanced base-trace columns: `A = 0..n`, `B = A` reversed. The
/// per-row pairing depends on the (bit-reversed) row order, but the *sum* over
/// all rows does not, so `claimed_sum == 0` regardless of ordering.
fn balanced_columns(log_n_rows: u32) -> (BaseColumn, BaseColumn) {
    let n = 1usize << log_n_rows;
    let a = (0..n)
        .map(|i| BaseField::from_u32_unchecked(i as u32))
        .collect();
    let b = (0..n)
        .map(|i| BaseField::from_u32_unchecked((n - 1 - i) as u32))
        .collect();
    (a, b)
}

fn gen_interaction_trace(
    log_size: u32,
    a: &BaseColumn,
    b: &BaseColumn,
    lookup_elements: &LookupElements<1>,
) -> (
    ColumnVec<CircleEvaluation<SimdBackend, BaseField, BitReversedOrder>>,
    SecureField,
) {
    let mut logup_gen = LogupTraceGenerator::new(log_size);
    let mut col_gen = logup_gen.new_col();
    for vec_row in 0..(1 << (log_size - LOG_N_LANES)) {
        let qa: PackedSecureField = lookup_elements.combine(&[a.data[vec_row]]);
        let qb: PackedSecureField = lookup_elements.combine(&[b.data[vec_row]]);
        // +1/qa − 1/qb = (qb − qa) / (qa·qb).
        col_gen.write_frac(vec_row, qb - qa, qa * qb);
    }
    col_gen.finalize_col();
    logup_gen.finalize_last()
}

/// Statistical-ZK prover for the balanced LogUp fixture. Mirrors the PLONK ZK
/// harness (empty preprocessed tree, masked composition via `prove_zk`) but with
/// a `claimed_sum` that is provably `0`.
#[cfg(feature = "statistical-zk")]
pub fn prove_balanced_logup_zk(
    log_n_rows: u32,
    config: PcsConfig,
    rng: &mut (impl rand::RngCore + rand::CryptoRng),
    randomizer_dimension: usize,
) -> (
    BalancedComponent,
    stwo::core::proof::ExtendedStarkProof<Blake2sMerkleHasher>,
) {
    use itertools::Itertools;
    use stwo::prover::{prove_zk, CommitmentSchemeProver};

    assert!(log_n_rows >= LOG_N_LANES);
    let log_blowup = config.fri_config.log_blowup_factor;
    assert_eq!(
        config.lifting_log_size,
        Some(log_n_rows + 1 + log_blowup),
        "ZK path requires lifting forced to log_n_rows + 1 + log_blowup_factor"
    );

    let (a, b) = balanced_columns(log_n_rows);

    let twiddles = SimdBackend::precompute_twiddles(
        CanonicCoset::new(log_n_rows + 1 + log_blowup)
            .circle_domain()
            .half_coset,
    );

    let channel = &mut Blake2sChannel::default();
    let mut commitment_scheme =
        CommitmentSchemeProver::<_, Blake2sMerkleChannel>::new(config, &twiddles);
    commitment_scheme.set_store_polynomials_coefficients();

    // Empty preprocessed tree (no public columns).
    let tree_builder = commitment_scheme.tree_builder();
    tree_builder.commit(channel);

    // Base trace: columns A and B.
    let domain = CanonicCoset::new(log_n_rows).circle_domain();
    let trace = [&a, &b]
        .into_iter()
        .map(|col| {
            CircleEvaluation::<SimdBackend, BaseField, BitReversedOrder>::new(domain, col.clone())
        })
        .collect_vec();
    let mut tree_builder = commitment_scheme.tree_builder();
    tree_builder.extend_evals(trace);
    tree_builder.commit(channel);

    // Draw lookup element.
    let lookup_elements = BalancedElements::draw(channel);

    // Interaction trace.
    let (interaction_trace, claimed_sum) =
        gen_interaction_trace(log_n_rows, &a, &b, &lookup_elements.0);
    assert!(
        claimed_sum.is_zero(),
        "balanced LogUp fixture must have claimed_sum == 0"
    );
    let mut tree_builder = commitment_scheme.tree_builder();
    tree_builder.extend_evals(interaction_trace);
    tree_builder.commit(channel);

    let component = BalancedComponent::new(
        &mut TraceLocationAllocator::default(),
        BalancedEval {
            log_n_rows,
            lookup_elements,
            claimed_sum,
        },
        claimed_sum,
    );

    let proof = prove_zk::<SimdBackend, Blake2sMerkleChannel>(
        &[&component],
        channel,
        commitment_scheme,
        rng,
        randomizer_dimension,
    )
    .unwrap();

    (component, proof)
}

#[cfg(all(test, feature = "statistical-zk"))]
mod zk_tests {
    use num_traits::Zero;
    use rand::rngs::StdRng;
    use rand::SeedableRng;
    use stwo::core::air::Component;
    use stwo::core::channel::Blake2sChannel;
    use stwo::core::fri::FriConfig;
    use stwo::core::pcs::{CommitmentSchemeVerifier, PcsConfig};
    use stwo::core::vcs_lifted::blake2_merkle::{Blake2sMerkleChannel, Blake2sMerkleHasher};
    use stwo::core::verifier::verify_zk;
    use stwo::prover::statistical_zk::assert_lookup_balanced;

    use crate::logup_balanced::{prove_balanced_logup_zk, BalancedComponent, BalancedElements};

    /// PLONK-style ZK config: FRI lifting forced to accommodate the taller
    /// unsplit composition-randomizer tree (`log_n_rows + 1 + log_blowup`).
    fn zk_config(log_n_rows: u32) -> PcsConfig {
        let log_blowup = 1;
        PcsConfig {
            pow_bits: 10,
            fri_config: FriConfig::new(5, log_blowup, 64, 1),
            lifting_log_size: Some(log_n_rows + 1 + log_blowup),
        }
    }

    fn verify_balanced_logup_zk(
        component: &BalancedComponent,
        proof: stwo::core::proof::StarkProof<Blake2sMerkleHasher>,
        config: PcsConfig,
    ) {
        let channel = &mut Blake2sChannel::default();
        let commitment_scheme = &mut CommitmentSchemeVerifier::<Blake2sMerkleChannel>::new(config);

        let sizes = component.trace_log_degree_bounds();

        // Preprocessed (empty), trace, interaction.
        commitment_scheme.commit(proof.commitments[0], &sizes[0], channel);
        commitment_scheme.commit(proof.commitments[1], &sizes[1], channel);
        let lookup_elements = BalancedElements::draw(channel);
        assert_eq!(lookup_elements, component.lookup_elements);
        commitment_scheme.commit(proof.commitments[2], &sizes[2], channel);

        // Enforced balanced gate: a sound balanced LogUp must have claimed_sum == 0.
        assert_lookup_balanced(component.claimed_sum())
            .expect("balanced LogUp must have claimed_sum == 0");

        // Composition (commitments[3]) and t (commitments[4]) are committed inside
        // verify_zk.
        verify_zk(&[component], channel, commitment_scheme, proof, false).unwrap();
    }

    #[test]
    fn test_balanced_logup_prove_zk() {
        for log_n_rows in 6..=7 {
            let config = zk_config(log_n_rows);
            let mut rng = StdRng::seed_from_u64(2024);
            let randomizer_dimension = 128;

            let (component, extended_proof) =
                prove_balanced_logup_zk(log_n_rows, config, &mut rng, randomizer_dimension);

            assert!(
                component.claimed_sum().is_zero(),
                "fixture must be balanced (claimed_sum == 0)"
            );
            verify_balanced_logup_zk(&component, extended_proof.proof, config);
        }
    }
}
