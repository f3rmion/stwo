use itertools::Itertools;
use num_traits::One;
use stwo::core::channel::Blake2sChannel;
use stwo::core::fields::m31::BaseField;
use stwo::core::fields::qm31::SecureField;
use stwo::core::pcs::{PcsConfig, TreeSubspan};
use stwo::core::poly::circle::CanonicCoset;
use stwo::core::proof::StarkProof;
use stwo::core::vcs_lifted::blake2_merkle::{Blake2sMerkleChannel, Blake2sMerkleHasher};
use stwo::core::ColumnVec;
use stwo::prover::backend::simd::column::BaseColumn;
use stwo::prover::backend::simd::m31::LOG_N_LANES;
use stwo::prover::backend::simd::qm31::PackedSecureField;
use stwo::prover::backend::simd::SimdBackend;
use stwo::prover::backend::Column;
use stwo::prover::poly::circle::{CircleEvaluation, PolyOps};
use stwo::prover::poly::BitReversedOrder;
use stwo::prover::{prove, CommitmentSchemeProver};
use stwo_constraint_framework::logup::LookupElements;
use stwo_constraint_framework::preprocessed_columns::PreProcessedColumnId;
use stwo_constraint_framework::{
    assert_constraints_on_polys, relation, EvalAtRow, FrameworkComponent, FrameworkEval,
    LogupTraceGenerator, RelationEntry, TraceLocationAllocator,
};
use tracing::{span, Level};

pub type PlonkComponent = FrameworkComponent<PlonkEval>;

// TODO(alont): Rename this and all other `LookupElements` types to `Relation`.
relation!(PlonkLookupElements, 2);

#[derive(Clone)]
pub struct PlonkEval {
    pub log_n_rows: u32,
    pub lookup_elements: PlonkLookupElements,
    pub claimed_sum: SecureField,
    pub base_trace_location: TreeSubspan,
    pub interaction_trace_location: TreeSubspan,
    pub constants_trace_location: TreeSubspan,
}

impl FrameworkEval for PlonkEval {
    fn log_size(&self) -> u32 {
        self.log_n_rows
    }

    fn max_constraint_log_degree_bound(&self) -> u32 {
        self.log_n_rows + 1
    }

    fn evaluate<E: EvalAtRow>(&self, mut eval: E) -> E {
        let a_wire = eval.get_preprocessed_column(Plonk::new("wire_a".to_string()).id());
        let b_wire = eval.get_preprocessed_column(Plonk::new("wire_b".to_string()).id());
        // Note: c_wire could also be implicit: (self.eval.point() - M31_CIRCLE_GEN.into_ef()).x.
        //   A constant column is easier though.
        let c_wire = eval.get_preprocessed_column(Plonk::new("wire_c".to_string()).id());
        let op = eval.get_preprocessed_column(Plonk::new("op".to_string()).id());

        let mult = eval.next_trace_mask();
        let a_val = eval.next_trace_mask();
        let b_val = eval.next_trace_mask();
        let c_val = eval.next_trace_mask();

        eval.add_constraint(
            c_val.clone() - op.clone() * (a_val.clone() + b_val.clone())
                + (E::F::one() - op) * a_val.clone() * b_val.clone(),
        );

        eval.add_to_relation(RelationEntry::new(
            &self.lookup_elements,
            E::EF::one(),
            &[a_wire, a_val],
        ));
        eval.add_to_relation(RelationEntry::new(
            &self.lookup_elements,
            E::EF::one(),
            &[b_wire, b_val],
        ));

        eval.add_to_relation(RelationEntry::new(
            &self.lookup_elements,
            (-mult).into(),
            &[c_wire, c_val],
        ));

        eval.finalize_logup_in_pairs();
        eval
    }
}

#[derive(Clone)]
pub struct PlonkCircuitTrace {
    pub mult: BaseColumn,
    pub a_wire: BaseColumn,
    pub b_wire: BaseColumn,
    pub c_wire: BaseColumn,
    pub op: BaseColumn,
    pub a_val: BaseColumn,
    pub b_val: BaseColumn,
    pub c_val: BaseColumn,
}
pub fn gen_trace(
    log_size: u32,
    circuit: &PlonkCircuitTrace,
) -> ColumnVec<CircleEvaluation<SimdBackend, BaseField, BitReversedOrder>> {
    let _span = span!(Level::INFO, "Generation").entered();

    let domain = CanonicCoset::new(log_size).circle_domain();
    [
        &circuit.mult,
        &circuit.a_val,
        &circuit.b_val,
        &circuit.c_val,
    ]
    .into_iter()
    .map(|eval| CircleEvaluation::new(domain, eval.clone()))
    .collect()
}

pub fn gen_interaction_trace(
    log_size: u32,
    circuit: &PlonkCircuitTrace,
    lookup_elements: &LookupElements<2>,
) -> (
    ColumnVec<CircleEvaluation<SimdBackend, BaseField, BitReversedOrder>>,
    SecureField,
) {
    let _span = span!(Level::INFO, "Generate interaction trace").entered();
    let mut logup_gen = LogupTraceGenerator::new(log_size);

    let mut col_gen = logup_gen.new_col();
    for vec_row in 0..(1 << (log_size - LOG_N_LANES)) {
        let q0: PackedSecureField =
            lookup_elements.combine(&[circuit.a_wire.data[vec_row], circuit.a_val.data[vec_row]]);
        let q1: PackedSecureField =
            lookup_elements.combine(&[circuit.b_wire.data[vec_row], circuit.b_val.data[vec_row]]);
        col_gen.write_frac(vec_row, q0 + q1, q0 * q1);
    }
    col_gen.finalize_col();

    let mut col_gen = logup_gen.new_col();
    for vec_row in 0..(1 << (log_size - LOG_N_LANES)) {
        let p = -circuit.mult.data[vec_row];
        let q: PackedSecureField =
            lookup_elements.combine(&[circuit.c_wire.data[vec_row], circuit.c_val.data[vec_row]]);
        col_gen.write_frac(vec_row, p.into(), q);
    }
    col_gen.finalize_col();

    logup_gen.finalize_last()
}

#[allow(unused)]
pub fn prove_fibonacci_plonk(
    log_n_rows: u32,
    config: PcsConfig,
) -> (PlonkComponent, StarkProof<Blake2sMerkleHasher>) {
    assert!(log_n_rows >= LOG_N_LANES);

    // Prepare a fibonacci circuit.
    let mut fib_values = vec![BaseField::one(), BaseField::one()];
    for _ in 0..(1 << log_n_rows) {
        fib_values.push(fib_values[fib_values.len() - 1] + fib_values[fib_values.len() - 2]);
    }
    let range = 0..(1 << log_n_rows);
    let mut circuit = PlonkCircuitTrace {
        mult: range.clone().map(|_| 2.into()).collect(),
        a_wire: range.clone().map(|i| i.into()).collect(),
        b_wire: range.clone().map(|i| (i + 1).into()).collect(),
        c_wire: range.clone().map(|i| (i + 2).into()).collect(),
        op: range.clone().map(|_| 1.into()).collect(),
        a_val: range.clone().map(|i| fib_values[i]).collect(),
        b_val: range.clone().map(|i| fib_values[i + 1]).collect(),
        c_val: range.clone().map(|i| fib_values[i + 2]).collect(),
    };
    circuit.mult.set((1 << log_n_rows) - 1, 0.into());
    circuit.mult.set((1 << log_n_rows) - 2, 1.into());

    // Precompute twiddles.
    let span = span!(Level::INFO, "Precompute twiddles").entered();
    let twiddles = SimdBackend::precompute_twiddles(
        CanonicCoset::new(log_n_rows + config.fri_config.log_blowup_factor + 1)
            .circle_domain()
            .half_coset,
    );
    span.exit();

    // Setup protocol.
    let channel = &mut Blake2sChannel::default();
    let mut commitment_scheme =
        CommitmentSchemeProver::<_, Blake2sMerkleChannel>::new(config, &twiddles);
    commitment_scheme.set_store_polynomials_coefficients();

    // Preprocessed trace.
    let span = span!(Level::INFO, "Constant").entered();
    let mut tree_builder = commitment_scheme.tree_builder();
    let mut constant_trace = [
        circuit.a_wire.clone(),
        circuit.b_wire.clone(),
        circuit.c_wire.clone(),
        circuit.op.clone(),
    ]
    .into_iter()
    .map(|col| {
        CircleEvaluation::<SimdBackend, _, BitReversedOrder>::new(
            CanonicCoset::new(log_n_rows).circle_domain(),
            col,
        )
    })
    .collect_vec();
    let constants_trace_location = tree_builder.extend_evals(constant_trace);
    tree_builder.commit(channel);
    span.exit();

    // Trace.
    let span = span!(Level::INFO, "Trace").entered();
    let trace = gen_trace(log_n_rows, &circuit);
    let mut tree_builder = commitment_scheme.tree_builder();
    let base_trace_location = tree_builder.extend_evals(trace);
    tree_builder.commit(channel);
    span.exit();

    // Draw lookup element.
    let lookup_elements = PlonkLookupElements::draw(channel);

    // Interaction trace.
    let span = span!(Level::INFO, "Interaction").entered();
    let (trace, claimed_sum) = gen_interaction_trace(log_n_rows, &circuit, &lookup_elements.0);
    let mut tree_builder = commitment_scheme.tree_builder();
    let interaction_trace_location = tree_builder.extend_evals(trace);
    tree_builder.commit(channel);
    span.exit();
    // Prove constraints.
    let component = PlonkComponent::new(
        &mut TraceLocationAllocator::default(),
        PlonkEval {
            log_n_rows,
            lookup_elements,
            claimed_sum,
            base_trace_location,
            interaction_trace_location,
            constants_trace_location,
        },
        claimed_sum,
    );

    // Sanity check. Remove for production.
    let trace_polys = commitment_scheme.trees.as_ref().map(|t| {
        t.polynomials
            .iter()
            .map(|p| p.coeffs.clone().unwrap())
            .collect_vec()
    });
    let component_eval = component.clone();
    assert_constraints_on_polys(
        &trace_polys,
        CanonicCoset::new(log_n_rows),
        |assert_eval| {
            component_eval.evaluate(assert_eval);
        },
        claimed_sum,
    );

    let proof = prove(&[&component], channel, commitment_scheme).unwrap();

    (component, proof)
}

/// Statistical zero-knowledge variant of [`prove_fibonacci_plonk`].
///
/// Builds the same PLONK circuit, preprocessed/trace/interaction trees and
/// LogUp lookup as the transparent harness, but proves through `prove_zk`, which
/// masks the committed composition quotient `q` by an independent random secure
/// polynomial `t` (committing `q' = q + t` split, plus `t` unsplit as a separate
/// last tree). The global FRI lifting is forced to the height of the taller `t`
/// tree so every committed tree shares a fold height.
///
/// `randomizer_dimension` controls how many independent base-field coefficients
/// each of `t`'s four coordinate polynomials carries; it must fit the composition
/// coefficient space `2^composition_log_size`.
#[cfg(feature = "statistical-zk")]
#[allow(clippy::type_complexity)]
pub fn prove_fibonacci_plonk_zk(
    log_n_rows: u32,
    config: PcsConfig,
    rng: &mut (impl rand::RngCore + rand::CryptoRng),
    randomizer_dimension: usize,
) -> (
    PlonkComponent,
    stwo::core::proof::ExtendedStarkProof<Blake2sMerkleHasher>,
) {
    use stwo::prover::prove_zk;

    assert!(log_n_rows >= LOG_N_LANES);
    // The composition lives at `composition_log_degree_bound = log_n_rows + 1`
    // for this AIR (max_constraint_log_degree_bound = log_n_rows + 1). The forced
    // lifting must accommodate the unsplit `t` tree, one log size above the split
    // composition chunks, at `log_n_rows + 1 + log_blowup_factor`.
    let log_blowup = config.fri_config.log_blowup_factor;
    assert_eq!(
        config.lifting_log_size,
        Some(log_n_rows + 1 + log_blowup),
        "ZK path requires lifting forced to log_n_rows + 1 + log_blowup_factor"
    );

    // Prepare a fibonacci circuit (identical to the transparent harness).
    let mut fib_values = vec![BaseField::one(), BaseField::one()];
    for _ in 0..(1 << log_n_rows) {
        fib_values.push(fib_values[fib_values.len() - 1] + fib_values[fib_values.len() - 2]);
    }
    let range = 0..(1 << log_n_rows);
    let mut circuit = PlonkCircuitTrace {
        mult: range.clone().map(|_| 2.into()).collect(),
        a_wire: range.clone().map(|i| i.into()).collect(),
        b_wire: range.clone().map(|i| (i + 1).into()).collect(),
        c_wire: range.clone().map(|i| (i + 2).into()).collect(),
        op: range.clone().map(|_| 1.into()).collect(),
        a_val: range.clone().map(|i| fib_values[i]).collect(),
        b_val: range.clone().map(|i| fib_values[i + 1]).collect(),
        c_val: range.clone().map(|i| fib_values[i + 2]).collect(),
    };
    circuit.mult.set((1 << log_n_rows) - 1, 0.into());
    circuit.mult.set((1 << log_n_rows) - 2, 1.into());

    // Precompute twiddles. The unsplit `t` tree reaches `log_n_rows + 1 +
    // log_blowup`, so the twiddle domain must cover that height.
    let span = span!(Level::INFO, "Precompute twiddles").entered();
    let twiddles = SimdBackend::precompute_twiddles(
        CanonicCoset::new(log_n_rows + 1 + log_blowup)
            .circle_domain()
            .half_coset,
    );
    span.exit();

    // Setup protocol.
    let channel = &mut Blake2sChannel::default();
    let mut commitment_scheme =
        CommitmentSchemeProver::<_, Blake2sMerkleChannel>::new(config, &twiddles);
    commitment_scheme.set_store_polynomials_coefficients();

    // Preprocessed trace.
    let span = span!(Level::INFO, "Constant").entered();
    let mut tree_builder = commitment_scheme.tree_builder();
    let constant_trace = [
        circuit.a_wire.clone(),
        circuit.b_wire.clone(),
        circuit.c_wire.clone(),
        circuit.op.clone(),
    ]
    .into_iter()
    .map(|col| {
        CircleEvaluation::<SimdBackend, _, BitReversedOrder>::new(
            CanonicCoset::new(log_n_rows).circle_domain(),
            col,
        )
    })
    .collect_vec();
    let constants_trace_location = tree_builder.extend_evals(constant_trace);
    tree_builder.commit(channel);
    span.exit();

    // Trace.
    let span = span!(Level::INFO, "Trace").entered();
    let trace = gen_trace(log_n_rows, &circuit);
    let mut tree_builder = commitment_scheme.tree_builder();
    let base_trace_location = tree_builder.extend_evals(trace);
    tree_builder.commit(channel);
    span.exit();

    // Draw lookup element.
    let lookup_elements = PlonkLookupElements::draw(channel);

    // Interaction trace.
    let span = span!(Level::INFO, "Interaction").entered();
    let (trace, claimed_sum) = gen_interaction_trace(log_n_rows, &circuit, &lookup_elements.0);
    let mut tree_builder = commitment_scheme.tree_builder();
    let interaction_trace_location = tree_builder.extend_evals(trace);
    tree_builder.commit(channel);
    span.exit();

    // Prove constraints.
    let component = PlonkComponent::new(
        &mut TraceLocationAllocator::default(),
        PlonkEval {
            log_n_rows,
            lookup_elements,
            claimed_sum,
            base_trace_location,
            interaction_trace_location,
            constants_trace_location,
        },
        claimed_sum,
    );

    // Sanity check the AIR on the underlying polynomials (unmasked).
    let trace_polys = commitment_scheme.trees.as_ref().map(|t| {
        t.polynomials
            .iter()
            .map(|p| p.coeffs.clone().unwrap())
            .collect_vec()
    });
    let component_eval = component.clone();
    assert_constraints_on_polys(
        &trace_polys,
        CanonicCoset::new(log_n_rows),
        |assert_eval| {
            component_eval.evaluate(assert_eval);
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

/// Statistical-ZK PLONK prover with Layer-1 trace masking.
///
/// Base-trace columns are committed as `ŵ = w + v_H·r` (witness-hiding off `H`);
/// when `mask_interaction` is set the LogUp interaction (cumulative-sum) columns
/// are masked too, otherwise they are only LIFTED to the masked geometry. The
/// public preprocessed columns are always lifted, never masked. This exercises
/// masked trace columns read at NONZERO offsets (the LogUp constraint reads the
/// cumulative-sum column at the current and previous row). `randomizer_seed` seeds
/// the trace-mask and composition-randomizer CSPRNG.
///
/// CANDIDATE: wires the masking MECHANISM (prove_zk accepts the masked trace); it
/// does NOT certify the absence of leakage.
#[cfg(feature = "statistical-zk")]
#[allow(clippy::type_complexity)]
pub fn prove_fibonacci_plonk_zk_trace_masked(
    log_n_rows: u32,
    randomizer_seed: u64,
    mask_interaction: bool,
) -> (
    PlonkComponent,
    PcsConfig,
    stwo::core::proof::ExtendedStarkProof<Blake2sMerkleHasher>,
) {
    use rand::rngs::StdRng;
    use rand::SeedableRng;
    use stwo::core::fri::FriConfig;
    use stwo::prover::prove_zk;
    use stwo::prover::statistical_zk::{mask_column, sample_salt_column, WitnessMaskConfig};

    // [F : F_q] for QM31 over M31.
    const E: usize = 4;
    assert!(log_n_rows >= LOG_N_LANES);
    let n = log_n_rows;
    let log_blowup = 1;
    let n_d = 64;
    // The LogUp interaction columns are read at two OODS points; size the mask for
    // that larger budget and apply it uniformly to every masked column.
    let h_col = E * 2 + n_d;
    let masked_log_size = {
        let need = (1usize << n) + h_col.next_power_of_two();
        let mut l = n + 1;
        while (1usize << l) < need {
            l += 1;
        }
        l
    };
    // PLONK has composition_log_degree_bound = n + 1, so masked composition is
    // masked_log_size + 1; force the lifting to cover the taller unsplit `t` tree.
    let comp_log = masked_log_size + 1;
    let config = PcsConfig {
        pow_bits: 10,
        fri_config: FriConfig::new(5, log_blowup, n_d, 1),
        lifting_log_size: Some(comp_log + log_blowup),
    };

    // Prepare the fibonacci circuit (identical to the transparent harness).
    let mut fib_values = vec![BaseField::one(), BaseField::one()];
    for _ in 0..(1 << n) {
        fib_values.push(fib_values[fib_values.len() - 1] + fib_values[fib_values.len() - 2]);
    }
    let range = 0..(1 << n);
    let mut circuit = PlonkCircuitTrace {
        mult: range.clone().map(|_| 2.into()).collect(),
        a_wire: range.clone().map(|i| i.into()).collect(),
        b_wire: range.clone().map(|i| (i + 1).into()).collect(),
        c_wire: range.clone().map(|i| (i + 2).into()).collect(),
        op: range.clone().map(|_| 1.into()).collect(),
        a_val: range.clone().map(|i| fib_values[i]).collect(),
        b_val: range.clone().map(|i| fib_values[i + 1]).collect(),
        c_val: range.clone().map(|i| fib_values[i + 2]).collect(),
    };
    circuit.mult.set((1 << n) - 1, 0.into());
    circuit.mult.set((1 << n) - 2, 1.into());

    let twiddles = SimdBackend::precompute_twiddles(
        CanonicCoset::new(comp_log + log_blowup)
            .circle_domain()
            .half_coset,
    );

    let channel = &mut Blake2sChannel::default();
    let mut commitment_scheme =
        CommitmentSchemeProver::<_, Blake2sMerkleChannel>::new(config, &twiddles);
    commitment_scheme.set_store_polynomials_coefficients();

    let mask_config = WitnessMaskConfig::new(n, masked_log_size, h_col).unwrap();
    mask_config.check_leakage_budget(h_col).unwrap();
    let mut rng = StdRng::seed_from_u64(randomizer_seed);
    let trace_domain = CanonicCoset::new(n).circle_domain();

    // Preprocessed trace: public, only LIFTED to the masked geometry.
    let mut tree_builder = commitment_scheme.tree_builder();
    let constant_polys = [
        circuit.a_wire.clone(),
        circuit.b_wire.clone(),
        circuit.c_wire.clone(),
        circuit.op.clone(),
    ]
    .into_iter()
    .map(|col| {
        CircleEvaluation::<SimdBackend, BaseField, BitReversedOrder>::new(trace_domain, col)
            .interpolate_with_twiddles(&twiddles)
            .extend(masked_log_size)
    })
    .collect_vec();
    let constants_trace_location = tree_builder.extend_polys(constant_polys);
    tree_builder.commit(channel);

    // Base trace: masked.
    let base_polys = gen_trace(n, &circuit)
        .into_iter()
        .map(|eval| mask_column(&eval.interpolate_with_twiddles(&twiddles), mask_config, &mut rng).unwrap())
        .collect_vec();
    let mut tree_builder = commitment_scheme.tree_builder();
    // Capture the trace location from the real columns only, then append the
    // leaf-size Layer-0 salt column AFTER (so the AIR never reads it).
    let base_trace_location = tree_builder.extend_polys(base_polys);
    tree_builder.extend_polys(vec![sample_salt_column::<SimdBackend, _>(comp_log, &mut rng)]);
    tree_builder.commit(channel);

    // Draw lookup element.
    let lookup_elements = PlonkLookupElements::draw(channel);

    // Interaction trace: masked when requested, otherwise lifted (still committed
    // at the masked geometry, read at nonzero offsets by the LogUp constraint).
    let (interaction_trace, claimed_sum) = gen_interaction_trace(n, &circuit, &lookup_elements.0);
    let interaction_polys = interaction_trace
        .into_iter()
        .map(|eval| {
            let coeffs = eval.interpolate_with_twiddles(&twiddles);
            if mask_interaction {
                mask_column(&coeffs, mask_config, &mut rng).unwrap()
            } else {
                coeffs.extend(masked_log_size)
            }
        })
        .collect_vec();
    let mut tree_builder = commitment_scheme.tree_builder();
    let interaction_trace_location = tree_builder.extend_polys(interaction_polys);
    tree_builder.extend_polys(vec![sample_salt_column::<SimdBackend, _>(comp_log, &mut rng)]);
    tree_builder.commit(channel);

    // `eval.log_size()` stays `n` (constraint vanishing domain); the component
    // declares the enlarged committed trace geometry separately.
    let component = PlonkComponent::new(
        &mut TraceLocationAllocator::default(),
        PlonkEval {
            log_n_rows: n,
            lookup_elements,
            claimed_sum,
            base_trace_location,
            interaction_trace_location,
            constants_trace_location,
        },
        claimed_sum,
    )
    .with_masked_trace_log_size(masked_log_size)
    // One Layer-0 salt column on the base-trace (tree 1) and interaction (tree 2)
    // trees; preprocessed (tree 0) is public, no salt.
    .with_salt_columns_per_tree(vec![0, 1, 1]);

    let randomizer_dimension = 1 << masked_log_size;
    let proof = prove_zk::<SimdBackend, Blake2sMerkleChannel>(
        &[&component],
        channel,
        commitment_scheme,
        &mut rng,
        randomizer_dimension,
    )
    .unwrap();

    (component, config, proof)
}

/// Preprocessed columns for describing a plonk circuit.
/// Each plonk gate is described by input wires `a_wire`, `b_wire`, output wire `c_wire`, and
/// operation `op`.
#[derive(Debug)]
pub struct Plonk {
    pub name: String,
}
impl Plonk {
    pub const fn new(name: String) -> Self {
        Self { name }
    }

    pub fn id(&self) -> PreProcessedColumnId {
        PreProcessedColumnId {
            id: format!("preprocessed_plonk_{}", self.name),
        }
    }
}

#[cfg(test)]
mod tests {
    use std::env;

    use stwo::core::air::Component;
    use stwo::core::channel::Blake2sChannel;
    use stwo::core::fri::FriConfig;
    use stwo::core::pcs::{CommitmentSchemeVerifier, PcsConfig};
    use stwo::core::vcs_lifted::blake2_merkle::Blake2sMerkleChannel;
    use stwo::core::verifier::verify;

    use crate::plonk::{prove_fibonacci_plonk, PlonkLookupElements};

    #[test_log::test]
    fn test_simd_plonk_prove() {
        // Get from environment variable:
        let log_n_instances = env::var("LOG_N_INSTANCES")
            .unwrap_or_else(|_| "10".to_string())
            .parse::<u32>()
            .unwrap();
        let config = PcsConfig {
            pow_bits: 10,
            fri_config: FriConfig::new(5, 4, 64, 1),
            lifting_log_size: None,
        };

        // Prove.
        let (component, proof) = prove_fibonacci_plonk(log_n_instances, config);

        // Verify.
        // TODO: Create Air instance independently.
        let channel = &mut Blake2sChannel::default();
        let commitment_scheme = &mut CommitmentSchemeVerifier::<Blake2sMerkleChannel>::new(config);

        // Decommit.
        // Retrieve the expected column sizes in each commitment interaction, from the AIR.
        let sizes = component.trace_log_degree_bounds();

        // Preprocessed columns.
        commitment_scheme.commit(proof.commitments[0], &sizes[0], channel);

        // Trace columns.
        commitment_scheme.commit(proof.commitments[1], &sizes[1], channel);
        // Draw lookup element.
        let lookup_elements = PlonkLookupElements::draw(channel);
        assert_eq!(lookup_elements, component.lookup_elements);
        // Interaction columns.
        commitment_scheme.commit(proof.commitments[2], &sizes[2], channel);

        verify(&[&component], channel, commitment_scheme, proof).unwrap();
    }
}

#[cfg(all(test, feature = "statistical-zk"))]
mod zk_tests {
    use rand::rngs::StdRng;
    use rand::SeedableRng;
    use stwo::core::air::Component;
    use stwo::core::channel::Blake2sChannel;
    use stwo::core::fri::FriConfig;
    use stwo::core::pcs::{CommitmentSchemeVerifier, PcsConfig};
    use stwo::core::vcs_lifted::blake2_merkle::Blake2sMerkleChannel;
    use stwo::core::verifier::verify_zk;

    use crate::plonk::{
        prove_fibonacci_plonk_zk, prove_fibonacci_plonk_zk_trace_masked, PlonkLookupElements,
    };

    /// Builds the PLONK PcsConfig with the FRI lifting forced to accommodate the
    /// taller unsplit composition-randomizer tree. The PLONK AIR has
    /// `composition_log_degree_bound = log_n_rows + 1`, so the randomizer tree
    /// reaches `log_n_rows + 1 + log_blowup_factor`.
    fn zk_config(log_n_rows: u32) -> PcsConfig {
        let log_blowup = 1;
        PcsConfig {
            pow_bits: 10,
            fri_config: FriConfig::new(5, log_blowup, 64, 1),
            lifting_log_size: Some(log_n_rows + 1 + log_blowup),
        }
    }

    /// Commits preprocessed/trace/interaction trees and redraws the lookup
    /// elements exactly as the transparent harness, then runs `verify_zk`. The
    /// composition-chunk and randomizer commitments are consumed inside
    /// `verify_zk`.
    fn verify_plonk_zk(
        component: &crate::plonk::PlonkComponent,
        proof: stwo::core::proof::StarkProof<
            stwo::core::vcs_lifted::blake2_merkle::Blake2sMerkleHasher,
        >,
        config: PcsConfig,
    ) {
        let channel = &mut Blake2sChannel::default();
        let commitment_scheme = &mut CommitmentSchemeVerifier::<Blake2sMerkleChannel>::new(config);

        let sizes = component.trace_log_degree_bounds();

        // Preprocessed columns.
        commitment_scheme.commit(proof.commitments[0], &sizes[0], channel);
        // Trace columns.
        commitment_scheme.commit(proof.commitments[1], &sizes[1], channel);
        // Redraw lookup element.
        let lookup_elements = PlonkLookupElements::draw(channel);
        assert_eq!(lookup_elements, component.lookup_elements);
        // Interaction columns.
        commitment_scheme.commit(proof.commitments[2], &sizes[2], channel);

        // Composition (commitments[3]) and t (commitments[4]) are committed inside
        // verify_zk.
        verify_zk(&[component], channel, commitment_scheme, proof, false).unwrap();
    }

    #[test]
    fn test_simd_plonk_prove_zk() {
        // log_n_rows starts at 6: with n_queries = 64 the composition randomizer `t`
        // needs dimension > n_F^comp + n_D = 65 for reconstruction-resistance, which
        // requires a composition coefficient space 2^(log_n_rows + 1) >= 66, i.e.
        // log_n_rows >= 6. (n = 5 gives only 2^6 = 64 < 66 — too small to hide `t`.)
        for log_n_rows in 6..=7 {
            let config = zk_config(log_n_rows);
            let mut rng = StdRng::seed_from_u64(2024);
            // Above the reconstruction-resistance budget (n_F^comp + n_D + 1 = 66)
            // and within the composition coefficient space 2^(log_n_rows + 1).
            let randomizer_dimension = 128;

            let (component, extended_proof) =
                prove_fibonacci_plonk_zk(log_n_rows, config, &mut rng, randomizer_dimension);

            verify_plonk_zk(&component, extended_proof.proof, config);
        }
    }

    /// Randomization smoke check (mechanism evidence, NOT a no-leak certificate):
    /// proves the same witness twice under two different rng seeds and asserts
    /// (a) both proofs verify, and (b) the committed composition-randomizer `t`
    /// OODS values differ between the runs, confirming `t` actually randomizes
    /// the committed composition.
    #[test]
    fn test_plonk_prove_zk_randomization_smoke() {
        let log_n_rows = 6;
        let config = zk_config(log_n_rows);
        // Above the reconstruction-resistance budget (n_F^comp + n_D + 1 = 66).
        let randomizer_dimension = 128;

        let mut rng_a = StdRng::seed_from_u64(1);
        let (component_a, proof_a) =
            prove_fibonacci_plonk_zk(log_n_rows, config, &mut rng_a, randomizer_dimension);

        let mut rng_b = StdRng::seed_from_u64(99999);
        let (component_b, proof_b) =
            prove_fibonacci_plonk_zk(log_n_rows, config, &mut rng_b, randomizer_dimension);

        // The unsplit randomizer `t` is the last sampled-values tree; the split
        // composition chunks are the second-to-last. Diff both across the two runs
        // to confirm the randomizer perturbs the committed composition openings.
        let t_a = proof_a.proof.sampled_values.last().unwrap();
        let t_b = proof_b.proof.sampled_values.last().unwrap();
        assert_ne!(
            t_a, t_b,
            "composition randomizer t OODS values must differ between rng seeds"
        );

        let n = proof_a.proof.sampled_values.len();
        let comp_a = &proof_a.proof.sampled_values[n - 2];
        let comp_b = &proof_b.proof.sampled_values[n - 2];
        assert_ne!(
            comp_a, comp_b,
            "masked composition q' OODS values must differ between rng seeds"
        );

        // Both proofs must verify under the same redraw protocol.
        verify_plonk_zk(&component_a, proof_a.proof, config);
        verify_plonk_zk(&component_b, proof_b.proof, config);
    }

    /// prove_zk fails closed when the composition randomizer is below the
    /// reconstruction-resistance budget (n_F^comp + n_D + 1 = 66 for n_queries=64):
    /// a too-small `t` would be reconstructible and the mask strippable.
    #[test]
    #[should_panic(expected = "CompositionRandomizerBudgetTooSmall")]
    fn test_plonk_prove_zk_rejects_undersized_randomizer() {
        let log_n_rows = 6;
        let config = zk_config(log_n_rows);
        let mut rng = StdRng::seed_from_u64(7);
        // 10 < 66 ⇒ prove_zk must reject (the harness unwraps the error).
        let _ = prove_fibonacci_plonk_zk(log_n_rows, config, &mut rng, 10);
    }

    /// Layer-1 trace masking with the LogUp interaction columns LIFTED (not yet
    /// masked): exercises masked base-trace columns AND nonzero-offset reads (the
    /// LogUp constraint reads the cumulative-sum column at current/previous row).
    /// Validates the per-offset OODS translation for the masked geometry.
    #[test]
    fn test_simd_plonk_prove_zk_trace_masked() {
        for log_n_rows in 6..=7 {
            let (component, config, extended_proof) =
                prove_fibonacci_plonk_zk_trace_masked(log_n_rows, 0, false);
            verify_plonk_zk(&component, extended_proof.proof, config);
        }
    }

    /// Full Layer-1 masking for a LogUp AIR: base-trace AND interaction columns
    /// committed as `ŵ = w + v_H·r`. CANDIDATE, mechanism only.
    #[test]
    fn test_simd_plonk_prove_zk_trace_and_interaction_masked() {
        for log_n_rows in 6..=7 {
            let (component, config, extended_proof) =
                prove_fibonacci_plonk_zk_trace_masked(log_n_rows, 0, true);
            verify_plonk_zk(&component, extended_proof.proof, config);
        }
    }

    /// Mask-isolating randomization check: same circuit, two randomizer seeds. The
    /// masked base-trace (tree 1) and interaction (tree 2) OODS openings must
    /// differ — with the witness fixed, only the trace mask `v_H·r` can cause that
    /// (a no-op mask would commit the identical trace and produce identical
    /// openings). Mechanism evidence, NOT a no-leak certificate.
    #[test]
    fn test_plonk_trace_masking_randomizes_openings() {
        let log_n_rows = 6;
        let (component_a, config_a, proof_a) =
            prove_fibonacci_plonk_zk_trace_masked(log_n_rows, 1, true);
        let (component_b, config_b, proof_b) =
            prove_fibonacci_plonk_zk_trace_masked(log_n_rows, 99999, true);
        assert_ne!(
            proof_a.proof.sampled_values[1], proof_b.proof.sampled_values[1],
            "masked base-trace OODS openings must differ across randomizer seeds"
        );
        assert_ne!(
            proof_a.proof.sampled_values[2], proof_b.proof.sampled_values[2],
            "masked interaction OODS openings must differ across randomizer seeds"
        );
        verify_plonk_zk(&component_a, proof_a.proof, config_a);
        verify_plonk_zk(&component_b, proof_b.proof, config_b);
    }
}
