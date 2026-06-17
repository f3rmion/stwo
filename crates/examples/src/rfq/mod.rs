//! RFQ batch-settlement AIR (witness-hiding example circuit).
//!
//! Models the single-DCO, principal-book RFQ SHAPE from the Infinite architecture:
//! a batch of `N` fills against the DCO principal book (no CLOB, no resting orders).
//! Per fill the circuit enforces the signed-notional settlement ARITHMETIC (boolean
//! side, `signed_size`, `delta`); a BALANCED LogUp proves the user ledger
//! `{(acct, delta)}` and the principal ledger `{(pacct, pdelta)}` are the SAME
//! MULTISET — a reconciliation / permutation argument. Equal multisets ⇒
//! `claimed_sum = 0`, the leak-free shape a verifier enforces with
//! `assert_lookup_balanced`. Under the ZK path the per-fill witness (account, side,
//! size, delta) is masked (Layer-1), hiding who traded what.
//!
//! HONEST SCOPE (v1 example circuit — read before reusing). Both ledgers are
//! PROVER-AUTHORED witnesses (the generator builds the principal ledger as a
//! permutation of the user ledger), so the balanced LogUp proves only that the
//! prover's two lists are the same multiset — NOT collateral conservation (`Σδ = 0`
//! is NOT enforced) and NOT settlement against any externally-committed book state.
//! Production soundness additionally needs: (a) binding `(pacct, pdelta)` and the
//! fills to a public/preprocessed book commitment / state roots (the
//! `infinite-proof` state-transition proof's job); and (b) the mark-band range
//! check (price within the canonical mark's signed bounds, a range-LogUp). Both are
//! out of v1 scope.

use num_traits::One;
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

pub type RfqComponent = FrameworkComponent<RfqEval>;

// Ledger entries are (account, signed collateral delta) pairs.
relation!(RfqLedger, 2);

/// Trace column order (must match `RfqEval::evaluate`'s `next_trace_mask` order):
/// `acct, side, size, price, signed_size, delta, pacct, pdelta`.
pub const N_TRACE_COLUMNS: usize = 8;

#[derive(Clone)]
pub struct RfqEval {
    pub log_n_fills: u32,
    pub ledger: RfqLedger,
    pub claimed_sum: SecureField,
}

impl FrameworkEval for RfqEval {
    fn log_size(&self) -> u32 {
        self.log_n_fills
    }

    fn max_constraint_log_degree_bound(&self) -> u32 {
        // Max constraint degree is 3: the pair-batched LogUp multiplies two
        // degree-1 denominators against the degree-1 interaction column. (The
        // algebraic settlement constraints, e.g. `signed_size · price`, are degree
        // 2.) The `+1` headroom suffices because a degree-3 constraint over a
        // `2^log_size` trace yields a quotient that fits `2^(log_size + 1)` — same
        // bound as the PLONK and logup_balanced examples.
        self.log_n_fills + 1
    }

    fn evaluate<E: EvalAtRow>(&self, mut eval: E) -> E {
        let acct = eval.next_trace_mask();
        let side = eval.next_trace_mask();
        let size = eval.next_trace_mask();
        let price = eval.next_trace_mask();
        let signed_size = eval.next_trace_mask();
        let delta = eval.next_trace_mask();
        let pacct = eval.next_trace_mask();
        let pdelta = eval.next_trace_mask();

        // side ∈ {0, 1} (buy / sell).
        eval.add_constraint(side.clone() * (E::F::one() - side.clone()));
        // signed_size = (1 - 2·side)·size  ⇒  signed_size = size - 2·side·size.
        eval.add_constraint(
            signed_size.clone() - (size.clone() - side.clone() * size.clone() - side.clone() * size),
        );
        // delta = signed_size · price (the user's signed collateral change).
        eval.add_constraint(delta.clone() - signed_size * price);

        // Balanced reconciliation LogUp: proves the user ledger and the principal
        // ledger record the SAME MULTISET of (account, delta) entries (a permutation
        // argument) ⇒ claimed_sum = 0. NOTE: both ledgers are prover witnesses; this
        // does NOT bind the principal side to an external book (see module header).
        eval.add_to_relation(RelationEntry::new(&self.ledger, E::EF::one(), &[acct, delta]));
        eval.add_to_relation(RelationEntry::new(&self.ledger, -E::EF::one(), &[pacct, pdelta]));

        eval.finalize_logup_in_pairs();
        eval
    }
}

/// Raw per-fill columns of one RFQ batch.
#[derive(Clone)]
pub struct RfqBatch {
    pub acct: BaseColumn,
    pub side: BaseColumn,
    pub size: BaseColumn,
    pub price: BaseColumn,
    pub signed_size: BaseColumn,
    pub delta: BaseColumn,
    pub pacct: BaseColumn,
    pub pdelta: BaseColumn,
}

/// Generate a deterministic, self-consistent RFQ batch: `2^log_n_fills` fills with
/// the settlement arithmetic satisfied, and a principal ledger that is a permutation
/// (hence the same multiset) of the user ledger — so the conservation LogUp is
/// balanced (`claimed_sum = 0`).
pub fn gen_rfq_batch(log_n_fills: u32) -> RfqBatch {
    rfq_batch_impl(log_n_fills, true)
}

/// Like [`gen_rfq_batch`] but the principal ledger does NOT reconcile: one entry is
/// altered, so the user and principal multisets differ and the conservation LogUp
/// is UNBALANCED (`claimed_sum != 0`). A correct verifier rejects it via the
/// balanced gate. For negative tests.
pub fn gen_rfq_batch_unbalanced(log_n_fills: u32) -> RfqBatch {
    rfq_batch_impl(log_n_fills, false)
}

fn rfq_batch_impl(log_n_fills: u32, balanced: bool) -> RfqBatch {
    let n = 1usize << log_n_fills;
    let n_accounts = 64u32.min(n as u32).max(1);
    let one = BaseField::one();

    let mut acct = Vec::with_capacity(n);
    let mut side = Vec::with_capacity(n);
    let mut size = Vec::with_capacity(n);
    let mut price = Vec::with_capacity(n);
    let mut signed_size = Vec::with_capacity(n);
    let mut delta = Vec::with_capacity(n);
    for i in 0..n {
        let i = i as u32;
        let a = BaseField::from_u32_unchecked(i % n_accounts);
        let s = BaseField::from_u32_unchecked(i & 1); // alternate buy / sell
        let sz = BaseField::from_u32_unchecked(1 + i % 997);
        let pr = BaseField::from_u32_unchecked(100 + i % 53);
        let ss = (one - (s + s)) * sz; // (1 - 2·side)·size
        let d = ss * pr; // signed notional
        acct.push(a);
        side.push(s);
        size.push(sz);
        price.push(pr);
        signed_size.push(ss);
        delta.push(d);
    }

    // Principal ledger: the same fills recorded by the book, in its own canonical
    // order (here a reversal). Same multiset ⇒ balanced reconciliation.
    let pacct: Vec<_> = (0..n).map(|i| acct[n - 1 - i]).collect();
    let mut pdelta: Vec<_> = (0..n).map(|i| delta[n - 1 - i]).collect();
    if !balanced {
        // Forge: the principal under-reports one fill's delta. The user and
        // principal multisets no longer match ⇒ claimed_sum != 0.
        pdelta[0] = pdelta[0] + BaseField::one();
    }

    RfqBatch {
        acct: acct.into_iter().collect(),
        side: side.into_iter().collect(),
        size: size.into_iter().collect(),
        price: price.into_iter().collect(),
        signed_size: signed_size.into_iter().collect(),
        delta: delta.into_iter().collect(),
        pacct: pacct.into_iter().collect(),
        pdelta: pdelta.into_iter().collect(),
    }
}

/// The 8 base-trace columns in `RfqEval` order.
pub fn gen_trace(
    log_n_fills: u32,
    batch: &RfqBatch,
) -> ColumnVec<CircleEvaluation<SimdBackend, BaseField, BitReversedOrder>> {
    let domain = CanonicCoset::new(log_n_fills).circle_domain();
    [
        &batch.acct,
        &batch.side,
        &batch.size,
        &batch.price,
        &batch.signed_size,
        &batch.delta,
        &batch.pacct,
        &batch.pdelta,
    ]
    .into_iter()
    .map(|col| CircleEvaluation::new(domain, col.clone()))
    .collect()
}

/// Balanced conservation LogUp: one column accumulating `1/q_user − 1/q_principal`
/// per fill, with `q = combine(acct, delta)`. Returns the interaction trace and the
/// `claimed_sum`, which is `0` for a balanced (correctly-reconciled) batch.
pub fn gen_interaction_trace(
    log_n_fills: u32,
    batch: &RfqBatch,
    ledger: &LookupElements<2>,
) -> (
    ColumnVec<CircleEvaluation<SimdBackend, BaseField, BitReversedOrder>>,
    SecureField,
) {
    let mut logup_gen = LogupTraceGenerator::new(log_n_fills);
    let mut col_gen = logup_gen.new_col();
    for vec_row in 0..(1 << (log_n_fills - LOG_N_LANES)) {
        let qa: PackedSecureField =
            ledger.combine(&[batch.acct.data[vec_row], batch.delta.data[vec_row]]);
        let qb: PackedSecureField =
            ledger.combine(&[batch.pacct.data[vec_row], batch.pdelta.data[vec_row]]);
        // +1/qa (user) − 1/qb (principal) = (qb − qa) / (qa·qb).
        col_gen.write_frac(vec_row, qb - qa, qa * qb);
    }
    col_gen.finalize_col();
    logup_gen.finalize_last()
}

/// Transparent prover for the RFQ batch-settlement AIR. Empty preprocessed tree,
/// 8-column base trace, one interaction column.
pub fn prove_rfq(
    log_n_fills: u32,
    config: PcsConfig,
) -> (RfqComponent, stwo::core::proof::StarkProof<Blake2sMerkleHasher>) {
    use stwo::prover::{prove, CommitmentSchemeProver};

    assert!(log_n_fills >= LOG_N_LANES);
    let batch = gen_rfq_batch(log_n_fills);

    let twiddles = SimdBackend::precompute_twiddles(
        CanonicCoset::new(log_n_fills + 1 + config.fri_config.log_blowup_factor)
            .circle_domain()
            .half_coset,
    );

    let channel = &mut Blake2sChannel::default();
    let mut commitment_scheme =
        CommitmentSchemeProver::<_, Blake2sMerkleChannel>::new(config, &twiddles);
    commitment_scheme.set_store_polynomials_coefficients();

    // Empty preprocessed tree (no public columns in v1).
    let tree_builder = commitment_scheme.tree_builder();
    tree_builder.commit(channel);

    // Base trace.
    let mut tree_builder = commitment_scheme.tree_builder();
    tree_builder.extend_evals(gen_trace(log_n_fills, &batch));
    tree_builder.commit(channel);

    // Draw the ledger lookup elements.
    let ledger = RfqLedger::draw(channel);

    // Interaction trace.
    let (interaction_trace, claimed_sum) = gen_interaction_trace(log_n_fills, &batch, &ledger.0);
    let mut tree_builder = commitment_scheme.tree_builder();
    tree_builder.extend_evals(interaction_trace);
    tree_builder.commit(channel);

    let component = RfqComponent::new(
        &mut TraceLocationAllocator::default(),
        RfqEval {
            log_n_fills,
            ledger,
            claimed_sum,
        },
        claimed_sum,
    );

    let proof = prove(&[&component], channel, commitment_scheme).unwrap();
    (component, proof)
}

/// Statistical-ZK prover for the RFQ batch (composition-masked path). Proves the
/// settlement + balanced reconciliation through `prove_zk` with a composition
/// randomizer, so the committed composition is blinded. `claimed_sum` is provably
/// `0`, so the verifier enforces `assert_lookup_balanced`. NOTE: this path does NOT
/// mask the base trace — the per-fill columns are committed in the clear; full
/// witness-hiding is the trace-masked path (`prove_rfq_zk_trace_masked`).
#[cfg(feature = "statistical-zk")]
pub fn prove_rfq_zk(
    log_n_fills: u32,
    config: PcsConfig,
    rng: &mut (impl rand::RngCore + rand::CryptoRng),
    randomizer_dimension: usize,
) -> (
    RfqComponent,
    stwo::core::proof::ExtendedStarkProof<Blake2sMerkleHasher>,
) {
    use num_traits::Zero;
    use stwo::prover::{prove_zk, CommitmentSchemeProver};

    assert!(log_n_fills >= LOG_N_LANES);
    let log_blowup = config.fri_config.log_blowup_factor;
    assert_eq!(
        config.lifting_log_size,
        Some(log_n_fills + 1 + log_blowup),
        "ZK path requires lifting forced to log_n_fills + 1 + log_blowup_factor"
    );

    let batch = gen_rfq_batch(log_n_fills);
    let twiddles = SimdBackend::precompute_twiddles(
        CanonicCoset::new(log_n_fills + 1 + log_blowup)
            .circle_domain()
            .half_coset,
    );

    let channel = &mut Blake2sChannel::default();
    let mut commitment_scheme =
        CommitmentSchemeProver::<_, Blake2sMerkleChannel>::new(config, &twiddles);
    commitment_scheme.set_store_polynomials_coefficients();

    // Empty preprocessed tree (no public columns in v1).
    let tree_builder = commitment_scheme.tree_builder();
    tree_builder.commit(channel);

    // Base trace.
    let mut tree_builder = commitment_scheme.tree_builder();
    tree_builder.extend_evals(gen_trace(log_n_fills, &batch));
    tree_builder.commit(channel);

    // Draw the ledger lookup elements.
    let ledger = RfqLedger::draw(channel);

    // Interaction trace.
    let (interaction_trace, claimed_sum) = gen_interaction_trace(log_n_fills, &batch, &ledger.0);
    assert!(
        claimed_sum.is_zero(),
        "reconciled RFQ batch must have claimed_sum == 0"
    );
    let mut tree_builder = commitment_scheme.tree_builder();
    tree_builder.extend_evals(interaction_trace);
    tree_builder.commit(channel);

    let component = RfqComponent::new(
        &mut TraceLocationAllocator::default(),
        RfqEval {
            log_n_fills,
            ledger,
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

/// Full witness-hiding RFQ prover: Layer-1 masks the base-trace AND interaction
/// columns (`ŵ = w + v_H·r`), so every off-domain / FRI-query opening of the
/// per-fill witness (account, side, size, delta) is blinded. The public statement
/// is the committed roots + `claimed_sum = 0` (the batch reconciles); WHO traded
/// WHAT is hidden. CANDIDATE: wires the masking mechanism; the leakage bound is the
/// cryptographer's, not certified here.
#[cfg(feature = "statistical-zk")]
pub fn prove_rfq_zk_trace_masked(
    log_n_fills: u32,
    randomizer_seed: u64,
) -> (
    RfqComponent,
    PcsConfig,
    stwo::core::proof::ExtendedStarkProof<Blake2sMerkleHasher>,
) {
    use rand::rngs::StdRng;
    use rand::SeedableRng;
    use stwo::core::fri::FriConfig;
    use stwo::prover::poly::circle::PolyOps;
    use stwo::prover::statistical_zk::{mask_columns, sample_salt_column, WitnessMaskConfig};
    use stwo::prover::{prove_zk, CommitmentSchemeProver};

    // [F : F_q] for QM31 over M31; a secure OODS opening charges e.
    const E: usize = 4;
    assert!(log_n_fills >= LOG_N_LANES);
    let n = log_n_fills;
    let log_blowup = 1;
    let n_d = 64; // FRI queries
    // The LogUp interaction (cumulative-sum) column is read at TWO OODS points
    // (offsets [-1, 0]), so its hiding budget needs n_F = 2 — and the SAME mask
    // config is applied to it below. Size every masked column for that larger
    // budget (e·2 + n_d); over-provisioning the base columns (read at offset 0 only)
    // is harmless. Matches the PLONK masked harness.
    let h_col = E * 2 + n_d;

    // Masked geometry: smallest log size above `n` holding the trace plus the
    // randomizer coefficient space.
    let masked_log_size = {
        let need = (1usize << n) + h_col.next_power_of_two();
        let mut l = n + 1;
        while (1usize << l) < need {
            l += 1;
        }
        l
    };
    let comp_log = masked_log_size + 1;
    let config = PcsConfig {
        pow_bits: 10,
        fri_config: FriConfig::new(5, log_blowup, n_d, 1),
        lifting_log_size: Some(comp_log + log_blowup),
    };

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

    let batch = gen_rfq_batch(n);

    // Empty preprocessed tree (no public columns in v1).
    let tree_builder = commitment_scheme.tree_builder();
    tree_builder.commit(channel);

    // Base trace: mask all 8 fill columns (batched — shared twiddles + v_H), then a
    // leaf-size Layer-0 salt column so the tree's leaf hashes hide.
    let trace_coeffs = gen_trace(n, &batch)
        .into_iter()
        .map(|eval| eval.interpolate_with_twiddles(&twiddles))
        .collect::<Vec<_>>();
    let mut masked_trace = mask_columns(&trace_coeffs, mask_config, &mut rng).unwrap();
    masked_trace.push(sample_salt_column::<SimdBackend, _>(comp_log, &mut rng));
    let mut tree_builder = commitment_scheme.tree_builder();
    tree_builder.extend_polys(masked_trace);
    tree_builder.commit(channel);

    // Draw the ledger lookup elements.
    let ledger = RfqLedger::draw(channel);

    // Interaction trace: masked too (its openings are witness-derived), plus a salt.
    let (interaction_trace, claimed_sum) = gen_interaction_trace(n, &batch, &ledger.0);
    let interaction_coeffs = interaction_trace
        .into_iter()
        .map(|eval| eval.interpolate_with_twiddles(&twiddles))
        .collect::<Vec<_>>();
    let mut masked_interaction = mask_columns(&interaction_coeffs, mask_config, &mut rng).unwrap();
    masked_interaction.push(sample_salt_column::<SimdBackend, _>(comp_log, &mut rng));
    let mut tree_builder = commitment_scheme.tree_builder();
    tree_builder.extend_polys(masked_interaction);
    tree_builder.commit(channel);

    let component = RfqComponent::new(
        &mut TraceLocationAllocator::default(),
        RfqEval {
            log_n_fills: n,
            ledger,
            claimed_sum,
        },
        claimed_sum,
    )
    .with_masked_trace_log_size(masked_log_size)
    // No salt on the empty preprocessed tree (0); one each on the base-trace (tree 1)
    // and interaction (tree 2) trees.
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

#[cfg(test)]
mod tests {
    use num_traits::Zero;
    use stwo::core::air::Component;
    use stwo::core::channel::Blake2sChannel;
    use stwo::core::pcs::{CommitmentSchemeVerifier, PcsConfig};
    use stwo::core::vcs_lifted::blake2_merkle::Blake2sMerkleChannel;
    use stwo::core::verifier::verify;

    use crate::rfq::{prove_rfq, RfqLedger};

    #[test]
    fn test_rfq_settlement_prove() {
        let log_n_fills = 8;
        let config = PcsConfig::default();
        let (component, proof) = prove_rfq(log_n_fills, config);

        // A correctly-reconciled batch is balanced.
        assert!(
            Component::claimed_sum(&component).is_zero(),
            "reconciled RFQ batch must have claimed_sum == 0"
        );

        let channel = &mut Blake2sChannel::default();
        let commitment_scheme = &mut CommitmentSchemeVerifier::<Blake2sMerkleChannel>::new(config);
        let sizes = component.trace_log_degree_bounds();
        commitment_scheme.commit(proof.commitments[0], &sizes[0], channel);
        commitment_scheme.commit(proof.commitments[1], &sizes[1], channel);
        let ledger = RfqLedger::draw(channel);
        assert_eq!(ledger, component.ledger);
        commitment_scheme.commit(proof.commitments[2], &sizes[2], channel);

        verify(&[&component], channel, commitment_scheme, proof).unwrap();
    }
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

    use crate::rfq::{prove_rfq_zk, prove_rfq_zk_trace_masked, RfqComponent, RfqLedger};

    fn zk_config(log_n_fills: u32) -> PcsConfig {
        let log_blowup = 1;
        PcsConfig {
            pow_bits: 10,
            fri_config: FriConfig::new(5, log_blowup, 64, 1),
            lifting_log_size: Some(log_n_fills + 1 + log_blowup),
        }
    }

    fn verify_rfq_zk(
        component: &RfqComponent,
        proof: stwo::core::proof::StarkProof<Blake2sMerkleHasher>,
        config: PcsConfig,
    ) {
        let channel = &mut Blake2sChannel::default();
        let commitment_scheme = &mut CommitmentSchemeVerifier::<Blake2sMerkleChannel>::new(config);
        let sizes = component.trace_log_degree_bounds();
        commitment_scheme.commit(proof.commitments[0], &sizes[0], channel);
        commitment_scheme.commit(proof.commitments[1], &sizes[1], channel);
        let ledger = RfqLedger::draw(channel);
        assert_eq!(ledger, component.ledger);
        commitment_scheme.commit(proof.commitments[2], &sizes[2], channel);

        // Conservation gate: a reconciled RFQ batch must net to zero, so the
        // verifier enforces the balanced-lookup shape before accepting.
        assert_lookup_balanced(Component::claimed_sum(component))
            .expect("reconciled RFQ batch must have claimed_sum == 0");

        verify_zk(&[component], channel, commitment_scheme, proof, false).unwrap();
    }

    #[test]
    fn test_rfq_settlement_prove_zk() {
        for log_n_fills in 6..=8 {
            let config = zk_config(log_n_fills);
            let mut rng = StdRng::seed_from_u64(2024);
            // Above the k-aware joint-hiding budget (~82 at n_queries=64, k=1) and
            // within the composition coefficient space 2^(log_n_fills + 1).
            let randomizer_dimension = 128;

            let (component, extended_proof) =
                prove_rfq_zk(log_n_fills, config, &mut rng, randomizer_dimension);

            assert!(
                Component::claimed_sum(&component).is_zero(),
                "reconciled RFQ batch must be balanced"
            );
            verify_rfq_zk(&component, extended_proof.proof, config);
        }
    }

    /// Full witness-hiding RFQ: Layer-1 masks the base-trace and interaction
    /// columns, so the per-fill data is hidden while the batch still proves it
    /// settled and reconciles (`claimed_sum = 0`). End-to-end prove/verify.
    #[test]
    fn test_rfq_settlement_prove_zk_trace_masked() {
        for log_n_fills in 6..=8 {
            let (component, config, extended_proof) = prove_rfq_zk_trace_masked(log_n_fills, 0);
            verify_rfq_zk(&component, extended_proof.proof, config);
        }
    }

    /// Negative control: an unreconciled batch (the principal ledger under-reports
    /// one fill) has a nonzero `claimed_sum`, so the balanced gate rejects it — the
    /// prover cannot make two ledgers that are not the same multiset pass the gate.
    #[test]
    fn test_rfq_unreconciled_batch_rejected() {
        use stwo::core::channel::Blake2sChannel;

        use crate::rfq::{gen_interaction_trace, gen_rfq_batch_unbalanced};

        let log_n_fills = 6;
        // The lookup challenge's exact value is irrelevant to the imbalance.
        let ledger = RfqLedger::draw(&mut Blake2sChannel::default());
        let batch = gen_rfq_batch_unbalanced(log_n_fills);
        let (_, claimed_sum) = gen_interaction_trace(log_n_fills, &batch, &ledger.0);

        assert!(
            !claimed_sum.is_zero(),
            "an unreconciled RFQ batch must have a nonzero claimed_sum"
        );
        assert!(
            assert_lookup_balanced(claimed_sum).is_err(),
            "the conservation gate must reject an unreconciled batch"
        );
    }
}
