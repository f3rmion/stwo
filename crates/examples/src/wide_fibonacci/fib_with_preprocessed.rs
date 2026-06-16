#![allow(unused)]
use itertools::Itertools;
use stwo::core::fields::m31::BaseField;
use stwo::core::fields::FieldExpOps;
use stwo::core::poly::circle::CanonicCoset;
use stwo::core::ColumnVec;
use stwo::prover::backend::{Backend, Col, Column};
use stwo::prover::poly::circle::CircleEvaluation;
use stwo::prover::poly::BitReversedOrder;
use stwo_constraint_framework::preprocessed_columns::PreProcessedColumnId;
use stwo_constraint_framework::{EvalAtRow, FrameworkComponent, FrameworkEval};

pub type WideFibWithPpComponent<const N: usize> = FrameworkComponent<WideFibWithPpEval<N>>;

pub struct FibInput {
    pub a: BaseField,
    pub b: BaseField,
}

pub fn generate_preprocessed_trace<B: Backend>(
    log_size: u32,
) -> CircleEvaluation<B, BaseField, BitReversedOrder> {
    let mut pp_col = Col::<B, BaseField>::zeros(1 << log_size);
    (0..1 << log_size).for_each(|i| pp_col.set(i, BaseField::from(i)));
    let domain = CanonicCoset::new(log_size).circle_domain();
    CircleEvaluation::<B, _, BitReversedOrder>::new(domain, pp_col)
}

pub fn generate_trace<const N: usize, B: Backend>(
    inputs: &[FibInput],
) -> ColumnVec<CircleEvaluation<B, BaseField, BitReversedOrder>> {
    assert!(inputs.len().is_power_of_two());
    let log_size = inputs.len().ilog2();
    let mut trace = (0..N)
        .map(|_| Col::<B, BaseField>::zeros(1 << log_size))
        .collect_vec();

    for (vec_index, input) in inputs.iter().enumerate() {
        let mut a = input.a;
        let mut b = input.b;
        trace[0].set(vec_index, a);
        trace[1].set(vec_index, b);
        trace.iter_mut().skip(2).for_each(|col| {
            (a, b) = (
                b,
                a.square() + b.square() + BaseField::from(vec_index).square(),
            );
            col.set(vec_index, b);
        });
    }
    let domain = CanonicCoset::new(log_size).circle_domain();
    trace
        .into_iter()
        .map(|eval| CircleEvaluation::<B, _, BitReversedOrder>::new(domain, eval))
        .collect_vec()
}

/// A component that at row n (starting from 0) enforces the sequence `aₙ = aₙ₋₁² + aₙ₋₂² + n²`.
#[derive(Clone)]
pub struct WideFibWithPpEval<const N: usize> {
    pub log_n_rows: u32,
}
impl<const N: usize> FrameworkEval for WideFibWithPpEval<N> {
    fn log_size(&self) -> u32 {
        self.log_n_rows
    }
    fn max_constraint_log_degree_bound(&self) -> u32 {
        self.log_n_rows + 1
    }
    fn evaluate<E: EvalAtRow>(&self, mut eval: E) -> E {
        let mut a = eval.next_trace_mask();
        let mut b = eval.next_trace_mask();
        let seq = eval.get_preprocessed_column(PreProcessedColumnId {
            id: String::from("seq"),
        });

        for _ in 2..N {
            let c = eval.next_trace_mask();
            eval.add_constraint(c.clone() - (a.square() + b.square() + seq.square()));
            a = b;
            b = c;
        }
        eval
    }
}

#[cfg(test)]
mod tests {
    use itertools::Itertools;
    use num_traits::{One, Zero};
    use stwo::core::air::Component;
    use stwo::core::channel::Blake2sM31Channel;
    use stwo::core::fields::m31::BaseField;
    use stwo::core::fields::qm31::SecureField;
    use stwo::core::pcs::{CommitmentSchemeVerifier, PcsConfig};
    use stwo::core::poly::circle::CanonicCoset;
    use stwo::core::vcs_lifted::blake2_merkle::Blake2sM31MerkleChannel;
    use stwo::core::verifier::verify;
    use stwo::prover::backend::simd::column::BaseColumn;
    use stwo::prover::backend::simd::SimdBackend;
    use stwo::prover::backend::Column;
    use stwo::prover::poly::circle::{CircleEvaluation, PolyOps};
    use stwo::prover::{prove, CommitmentSchemeProver};
    use stwo_constraint_framework::preprocessed_columns::PreProcessedColumnId;
    use stwo_constraint_framework::TraceLocationAllocator;

    use super::{generate_preprocessed_trace, generate_trace, FibInput, WideFibWithPpEval};
    use crate::wide_fibonacci::fib_with_preprocessed::WideFibWithPpComponent;

    const FIB_SEQUENCE_LENGTH: usize = 3;

    fn generate_test_inputs(log_n_instances: u32) -> Vec<FibInput> {
        (0..1 << log_n_instances)
            .map(|i| FibInput {
                a: BaseField::one(),
                b: BaseField::from_u32_unchecked(i as u32),
            })
            .collect_vec()
    }

    #[ignore]
    #[test_log::test]
    fn test_wide_fib_with_pp_prove_with_blake() {
        for log_n_instances in 4..=8 {
            let config = PcsConfig::default();
            // Precompute twiddles.
            let twiddles = SimdBackend::precompute_twiddles(
                CanonicCoset::new(log_n_instances + 1 + config.fri_config.log_blowup_factor)
                    .circle_domain()
                    .half_coset,
            );

            // Setup protocol.
            let prover_channel = &mut Blake2sM31Channel::default();
            let mut commitment_scheme = CommitmentSchemeProver::<
                SimdBackend,
                Blake2sM31MerkleChannel,
            >::new(config, &twiddles);

            // Preprocessed trace
            let mut tree_builder = commitment_scheme.tree_builder();
            let preprocessed_trace = generate_preprocessed_trace(log_n_instances);
            tree_builder.extend_evals(vec![preprocessed_trace]);
            tree_builder.commit(prover_channel);

            // Trace.
            let trace =
                generate_trace::<FIB_SEQUENCE_LENGTH, _>(&generate_test_inputs(log_n_instances));
            let mut tree_builder = commitment_scheme.tree_builder();
            tree_builder.extend_evals(trace);
            tree_builder.commit(prover_channel);

            // Prove constraints.
            let component = WideFibWithPpComponent::new(
                &mut TraceLocationAllocator::default(),
                WideFibWithPpEval::<FIB_SEQUENCE_LENGTH> {
                    log_n_rows: log_n_instances,
                },
                SecureField::zero(),
            );

            let proof = prove::<SimdBackend, Blake2sM31MerkleChannel>(
                &[&component],
                prover_channel,
                commitment_scheme,
            )
            .unwrap();

            // Verify.
            let verifier_channel = &mut Blake2sM31Channel::default();
            let commitment_scheme =
                &mut CommitmentSchemeVerifier::<Blake2sM31MerkleChannel>::new(config);

            // Retrieve the expected column sizes in each commitment interaction, from the AIR.
            let sizes = component.trace_log_degree_bounds();
            commitment_scheme.commit(proof.commitments[0], &sizes[0], verifier_channel);
            commitment_scheme.commit(proof.commitments[1], &sizes[1], verifier_channel);
            verify(&[&component], verifier_channel, commitment_scheme, proof).unwrap();
        }
    }

    #[cfg(feature = "statistical-zk")]
    #[test]
    fn test_wide_fib_with_pp_prove_zk_with_blake() {
        use rand::rngs::StdRng;
        use rand::SeedableRng;
        use stwo::core::verifier::verify_zk;
        use stwo::prover::prove_zk;

        for log_n_instances in 4..=8 {
            // The unsplit composition randomizer lives one log size above the split
            // composition chunks at log_n + 1 + log_blowup, making it the tallest
            // committed tree. Pin every tree to that lifting size so all committed
            // trees share a height and FRI queries decommit uniformly. A non-empty
            // preprocessed tree is required so its height tracks the lifting size.
            let mut config = PcsConfig::default();
            config.lifting_log_size =
                Some(log_n_instances + 1 + config.fri_config.log_blowup_factor);
            // Precompute twiddles covering the lifted domain.
            let twiddles = SimdBackend::precompute_twiddles(
                CanonicCoset::new(log_n_instances + 1 + config.fri_config.log_blowup_factor)
                    .circle_domain()
                    .half_coset,
            );

            // Setup protocol.
            let prover_channel = &mut Blake2sM31Channel::default();
            let mut commitment_scheme = CommitmentSchemeProver::<
                SimdBackend,
                Blake2sM31MerkleChannel,
            >::new(config, &twiddles);

            // Preprocessed trace.
            let mut tree_builder = commitment_scheme.tree_builder();
            let preprocessed_trace = generate_preprocessed_trace(log_n_instances);
            tree_builder.extend_evals(vec![preprocessed_trace]);
            tree_builder.commit(prover_channel);

            // Trace.
            let trace =
                generate_trace::<FIB_SEQUENCE_LENGTH, _>(&generate_test_inputs(log_n_instances));
            let mut tree_builder = commitment_scheme.tree_builder();
            tree_builder.extend_evals(trace);
            tree_builder.commit(prover_channel);

            // Prove constraints with the composition randomizer active.
            let component = WideFibWithPpComponent::new(
                &mut TraceLocationAllocator::default(),
                WideFibWithPpEval::<FIB_SEQUENCE_LENGTH> {
                    log_n_rows: log_n_instances,
                },
                SecureField::zero(),
            );

            let mut rng = StdRng::seed_from_u64(0);
            // The randomizer carries this many independent base-field coefficients
            // per coordinate. It must fit the composition coefficient space
            // (2^(log_n+1)); half that space is a nontrivial, always-valid choice.
            let randomizer_dimension = 1 << log_n_instances;
            let extended_proof = prove_zk::<SimdBackend, Blake2sM31MerkleChannel>(
                &[&component],
                prover_channel,
                commitment_scheme,
                &mut rng,
                randomizer_dimension,
            )
            .unwrap();
            let proof = extended_proof.proof;

            // Verify.
            let verifier_channel = &mut Blake2sM31Channel::default();
            let commitment_scheme =
                &mut CommitmentSchemeVerifier::<Blake2sM31MerkleChannel>::new(config);

            // Retrieve the expected column sizes in each commitment interaction, from the AIR.
            let sizes = component.trace_log_degree_bounds();
            commitment_scheme.commit(proof.commitments[0], &sizes[0], verifier_channel);
            commitment_scheme.commit(proof.commitments[1], &sizes[1], verifier_channel);
            verify_zk(&[&component], verifier_channel, commitment_scheme, proof, false).unwrap();
        }
    }

    /// Proves the WideFib-with-preprocessed AIR through the statistical-ZK path
    /// with Layer-1 base-trace masking active: each base-trace column is committed
    /// as `ŵ = w + v_H·r` (witness-hiding off `H`), the public preprocessed column
    /// is lifted (not masked) to the enlarged geometry, and the composition
    /// randomizer `t` masks the composition on top. `witness_seed` selects the
    /// witness inputs and `randomizer_seed` seeds the CSPRNG for the trace mask and
    /// composition randomizer, so the two can be varied independently.
    ///
    /// CANDIDATE: this wires the masking MECHANISM (prove_zk accepts the masked
    /// trace); it does NOT certify the absence of leakage.
    #[cfg(feature = "statistical-zk")]
    fn prove_wide_fib_pp_trace_masked(
        n: u32,
        witness_seed: u64,
        randomizer_seed: u64,
    ) -> (
        WideFibWithPpComponent<FIB_SEQUENCE_LENGTH>,
        PcsConfig,
        stwo::core::proof::ExtendedStarkProof<
            stwo::core::vcs_lifted::blake2_merkle::Blake2sM31MerkleHasher,
        >,
    ) {
        use rand::rngs::StdRng;
        use rand::SeedableRng;
        use stwo::prover::poly::circle::PolyOps;
        use stwo::prover::prove_zk;
        use stwo::prover::statistical_zk::{mask_column, sample_salt_column, WitnessMaskConfig};

        // [F : F_q] for QM31 over M31; an OODS opening of a secure value charges e.
        const E: usize = 4;

        let base = PcsConfig::default();
        let b = base.fri_config.log_blowup_factor;
        // Base columns are read at offset 0 only (n_F = 1); n_D = FRI queries.
        let n_f = 1usize;
        let n_d = base.fri_config.n_queries;
        let h_col = E * n_f + n_d;

        // Masked geometry: smallest log size above `n` that holds the trace plus
        // the randomizer coefficient space.
        let masked_log_size = {
            let need = (1usize << n) + h_col.next_power_of_two();
            let mut l = n + 1;
            while (1usize << l) < need {
                l += 1;
            }
            l
        };
        // The masked composition lives one log size above the masked trace; the
        // unsplit `t` tree is one above the split chunks, so force the lifting to
        // `(masked_log_size + 1) + log_blowup`.
        let comp_log = masked_log_size + 1;
        let mut config = base;
        config.lifting_log_size = Some(comp_log + b);

        let twiddles = SimdBackend::precompute_twiddles(
            CanonicCoset::new(comp_log + b).circle_domain().half_coset,
        );

        let prover_channel = &mut Blake2sM31Channel::default();
        let mut commitment_scheme =
            CommitmentSchemeProver::<SimdBackend, Blake2sM31MerkleChannel>::new(config, &twiddles);
        commitment_scheme.set_store_polynomials_coefficients();

        let mask_config = WitnessMaskConfig::new(n, masked_log_size, h_col).unwrap();
        mask_config.check_leakage_budget(h_col).unwrap();
        let mut rng = StdRng::seed_from_u64(randomizer_seed);

        // Preprocessed trace: public, so it is only LIFTED to the masked geometry
        // (low-degree extension), never masked.
        let mut tree_builder = commitment_scheme.tree_builder();
        let pp_lifted = generate_preprocessed_trace::<SimdBackend>(n)
            .interpolate_with_twiddles(&twiddles)
            .extend(masked_log_size);
        tree_builder.extend_polys(vec![pp_lifted]);
        tree_builder.commit(prover_channel);

        // Witness inputs vary with `witness_seed` so distinct witnesses can be proved.
        let inputs = (0..1 << n)
            .map(|i| FibInput {
                a: BaseField::one(),
                b: BaseField::from_u32_unchecked((i as u32).wrapping_add(witness_seed as u32)),
            })
            .collect_vec();

        // Base trace: masked column by column with independent randomizers, plus a
        // leaf-size Layer-0 salt column so the base-trace tree's leaf hashes hide.
        let mut masked_trace = generate_trace::<FIB_SEQUENCE_LENGTH, SimdBackend>(&inputs)
            .into_iter()
            .map(|eval| {
                let coeffs = eval.interpolate_with_twiddles(&twiddles);
                mask_column(&coeffs, mask_config, &mut rng).unwrap()
            })
            .collect_vec();
        masked_trace.push(sample_salt_column::<SimdBackend, _>(comp_log, &mut rng));
        let mut tree_builder = commitment_scheme.tree_builder();
        tree_builder.extend_polys(masked_trace);
        tree_builder.commit(prover_channel);

        // `eval.log_size()` stays `n` (the constraint vanishing domain); the
        // component declares the enlarged committed trace geometry and the one
        // Layer-0 salt column on the base-trace tree (tree 1; preprocessed tree 0
        // is public, no salt).
        let component = WideFibWithPpComponent::<FIB_SEQUENCE_LENGTH>::new(
            &mut TraceLocationAllocator::default(),
            WideFibWithPpEval::<FIB_SEQUENCE_LENGTH> { log_n_rows: n },
            SecureField::zero(),
        )
        .with_masked_trace_log_size(masked_log_size)
        .with_salt_columns_per_tree(vec![0, 1]);

        // `t` carries this many coefficients per coordinate; must fit the masked
        // composition coefficient space (2^comp_log).
        let randomizer_dimension = 1 << masked_log_size;
        let extended_proof = prove_zk::<SimdBackend, Blake2sM31MerkleChannel>(
            &[&component],
            prover_channel,
            commitment_scheme,
            &mut rng,
            randomizer_dimension,
        )
        .unwrap();

        (component, config, extended_proof)
    }

    #[cfg(feature = "statistical-zk")]
    fn verify_wide_fib_pp_trace_masked(
        component: &WideFibWithPpComponent<FIB_SEQUENCE_LENGTH>,
        config: PcsConfig,
        proof: stwo::core::proof::StarkProof<
            stwo::core::vcs_lifted::blake2_merkle::Blake2sM31MerkleHasher,
        >,
    ) {
        use stwo::core::verifier::verify_zk;

        let verifier_channel = &mut Blake2sM31Channel::default();
        let commitment_scheme =
            &mut CommitmentSchemeVerifier::<Blake2sM31MerkleChannel>::new(config);
        let sizes = component.trace_log_degree_bounds();
        commitment_scheme.commit(proof.commitments[0], &sizes[0], verifier_channel);
        commitment_scheme.commit(proof.commitments[1], &sizes[1], verifier_channel);
        verify_zk(&[component], verifier_channel, commitment_scheme, proof, false).unwrap();
    }

    /// Layer-1 trace masking end to end: prove_zk/verify_zk accept the masked
    /// trace across a range of sizes.
    #[cfg(feature = "statistical-zk")]
    #[test]
    fn test_wide_fib_with_pp_prove_zk_trace_masked_with_blake() {
        for log_n_instances in 4..=8 {
            let (component, config, extended_proof) =
                prove_wide_fib_pp_trace_masked(log_n_instances, 0, 0);
            verify_wide_fib_pp_trace_masked(&component, config, extended_proof.proof);
        }
    }

    /// Mask-isolating randomization check (mechanism evidence, NOT a no-leak
    /// certificate): proves the SAME witness twice, varying only the randomizer
    /// seed, and asserts the BASE-TRACE OODS openings (sampled-values tree index 1,
    /// not the composition randomizer `t`) differ. With the witness fixed, the
    /// openings can only differ because the trace mask `v_H·r` is actually applied —
    /// if masking were a no-op the two runs would commit the identical trace, draw
    /// the identical OODS point, and produce identical openings. This isolates the
    /// MASK's contribution (unlike varying the witness, which differs regardless).
    #[cfg(feature = "statistical-zk")]
    #[test]
    fn test_wide_fib_with_pp_trace_masking_randomizes_openings() {
        let n = 6;
        let witness_seed = 7;
        let (component_a, config_a, proof_a) =
            prove_wide_fib_pp_trace_masked(n, witness_seed, 1);
        let (component_b, config_b, proof_b) =
            prove_wide_fib_pp_trace_masked(n, witness_seed, 99999);

        // Tree 0 = preprocessed, tree 1 = base trace. Same witness, different
        // randomizer ⇒ masked base-trace OODS openings must differ.
        let base_trace_a = &proof_a.proof.sampled_values[1];
        let base_trace_b = &proof_b.proof.sampled_values[1];
        assert_ne!(
            base_trace_a, base_trace_b,
            "same witness, different randomizer: masked base-trace OODS openings \
             must differ (else the trace mask is a no-op)"
        );

        verify_wide_fib_pp_trace_masked(&component_a, config_a, proof_a.proof);
        verify_wide_fib_pp_trace_masked(&component_b, config_b, proof_b.proof);
    }

    /// Two distinct witnesses for the same AIR both prove and verify through the
    /// masked path (the acceptance criterion's two-witness robustness check). This
    /// does NOT isolate the mask — distinct witnesses produce distinct openings
    /// even without masking; mask randomization is covered by the test above and by
    /// the `mask_column` unit tests.
    #[cfg(feature = "statistical-zk")]
    #[test]
    fn test_wide_fib_with_pp_distinct_witnesses_both_verify() {
        let n = 6;
        let (component_a, config_a, proof_a) = prove_wide_fib_pp_trace_masked(n, 1, 1);
        let (component_b, config_b, proof_b) = prove_wide_fib_pp_trace_masked(n, 2, 1);
        verify_wide_fib_pp_trace_masked(&component_a, config_a, proof_a.proof);
        verify_wide_fib_pp_trace_masked(&component_b, config_b, proof_b.proof);
    }

    #[test_log::test]
    fn test_wide_fib_with_unused_pp_prove_with_blake() {
        for log_n_instances in 4..=8 {
            let config = PcsConfig::default();
            // Precompute twiddles.
            let twiddles = SimdBackend::precompute_twiddles(
                CanonicCoset::new(log_n_instances + 1 + config.fri_config.log_blowup_factor)
                    .circle_domain()
                    .half_coset,
            );

            // Setup protocol.
            let prover_channel = &mut Blake2sM31Channel::default();
            let mut commitment_scheme = CommitmentSchemeProver::<
                SimdBackend,
                Blake2sM31MerkleChannel,
            >::new(config, &twiddles);

            // Preprocessed trace
            let mut tree_builder = commitment_scheme.tree_builder();
            let mut preprocessed_trace = vec![generate_preprocessed_trace(log_n_instances)];
            // Build a long unused preprocessed column.
            let log_size_unused_pp = log_n_instances + 1;
            let domain = CanonicCoset::new(log_size_unused_pp).circle_domain();
            preprocessed_trace.push(CircleEvaluation::new(
                domain,
                BaseColumn::zeros(1 << log_size_unused_pp),
            ));
            tree_builder.extend_evals(preprocessed_trace);
            tree_builder.commit(prover_channel);

            // Trace.
            let trace =
                generate_trace::<FIB_SEQUENCE_LENGTH, _>(&generate_test_inputs(log_n_instances));
            let mut tree_builder = commitment_scheme.tree_builder();
            tree_builder.extend_evals(trace);
            tree_builder.commit(prover_channel);

            // Prove constraints.
            let mut allocator = TraceLocationAllocator::new_with_preprocessed_columns(&[
                PreProcessedColumnId {
                    id: String::from("seq"),
                },
                PreProcessedColumnId {
                    id: String::from("large_unused"),
                },
            ]);
            let component = WideFibWithPpComponent::new(
                &mut allocator,
                WideFibWithPpEval::<FIB_SEQUENCE_LENGTH> {
                    log_n_rows: log_n_instances,
                },
                SecureField::zero(),
            );

            let proof = prove::<SimdBackend, Blake2sM31MerkleChannel>(
                &[&component],
                prover_channel,
                commitment_scheme,
            )
            .unwrap();

            // Verify.
            let verifier_channel = &mut Blake2sM31Channel::default();
            let commitment_scheme =
                &mut CommitmentSchemeVerifier::<Blake2sM31MerkleChannel>::new(config);

            // Retrieve the expected column sizes in each commitment interaction, from the AIR.
            let sizes = component.trace_log_degree_bounds();
            commitment_scheme.commit(
                proof.commitments[0],
                &[log_n_instances, log_size_unused_pp],
                verifier_channel,
            );
            commitment_scheme.commit(proof.commitments[1], &sizes[1], verifier_channel);
            verify(&[&component], verifier_channel, commitment_scheme, proof).unwrap();
        }
    }

    #[test_log::test]
    /// This test is equal to the previous one except it tests the hardcoding of lifting size.
    fn test_wide_fib_with_unused_pp_and_hardcoded_lifting() {
        for log_n_instances in 4..=8 {
            let mut config = PcsConfig::default();
            let log_size_unused_pp = log_n_instances + 3;
            // Set lifting log size to the largest preprocessed column (after LDE).
            config.lifting_log_size =
                Some(log_size_unused_pp + config.fri_config.log_blowup_factor);
            // Precompute twiddles.
            let twiddles = SimdBackend::precompute_twiddles(
                CanonicCoset::new(log_size_unused_pp + 1 + config.fri_config.log_blowup_factor)
                    .circle_domain()
                    .half_coset,
            );

            // Setup protocol.
            let prover_channel = &mut Blake2sM31Channel::default();
            let mut commitment_scheme = CommitmentSchemeProver::<
                SimdBackend,
                Blake2sM31MerkleChannel,
            >::new(config, &twiddles);

            // Preprocessed trace
            let mut tree_builder = commitment_scheme.tree_builder();
            let mut preprocessed_trace = vec![generate_preprocessed_trace(log_n_instances)];
            // Build a long unused preprocessed column.
            let domain = CanonicCoset::new(log_size_unused_pp).circle_domain();
            preprocessed_trace.push(CircleEvaluation::new(
                domain,
                BaseColumn::zeros(1 << log_size_unused_pp),
            ));
            tree_builder.extend_evals(preprocessed_trace);
            tree_builder.commit(prover_channel);

            // Trace.
            let trace =
                generate_trace::<FIB_SEQUENCE_LENGTH, _>(&generate_test_inputs(log_n_instances));
            let mut tree_builder = commitment_scheme.tree_builder();
            tree_builder.extend_evals(trace);
            tree_builder.commit(prover_channel);

            // Prove constraints.
            let mut allocator = TraceLocationAllocator::new_with_preprocessed_columns(&[
                PreProcessedColumnId {
                    id: String::from("seq"),
                },
                PreProcessedColumnId {
                    id: String::from("large_unused"),
                },
            ]);
            let component = WideFibWithPpComponent::new(
                &mut allocator,
                WideFibWithPpEval::<FIB_SEQUENCE_LENGTH> {
                    log_n_rows: log_n_instances,
                },
                SecureField::zero(),
            );

            let proof = prove::<SimdBackend, Blake2sM31MerkleChannel>(
                &[&component],
                prover_channel,
                commitment_scheme,
            )
            .unwrap();

            // Verify.
            let verifier_channel = &mut Blake2sM31Channel::default();
            let commitment_scheme =
                &mut CommitmentSchemeVerifier::<Blake2sM31MerkleChannel>::new(config);

            // Retrieve the expected column sizes in each commitment interaction, from the AIR.
            let mut sizes = component.trace_log_degree_bounds();
            commitment_scheme.commit(
                proof.commitments[0],
                &[log_n_instances, log_size_unused_pp],
                verifier_channel,
            );
            commitment_scheme.commit(proof.commitments[1], &sizes[1], verifier_channel);
            verify(&[&component], verifier_channel, commitment_scheme, proof).unwrap();
        }
    }
}
