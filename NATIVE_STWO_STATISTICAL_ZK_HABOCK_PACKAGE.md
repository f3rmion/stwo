# Statistical zero-knowledge for the S-two circle STARK — review package

**For:** Ulrich Haböck / StarkWare (best-fit reviewer — the construction sits at the intersection of
ePrint 2024/1037 and 2026/532, both yours).
**From:** the f3rmion team.
**Ask, stated precisely:** *please review our proof argument that this masking construction hides the
witness.* This is **not** a request to "confirm our system works." We have a prototype and supporting
numerical evidence, but **ZK failures are silent** — a construction can verify, pass two-witness tests,
and still leak — so the privacy guarantee is your review of the **argument**, never the prototype or any
test. Two steps we cannot close ourselves are marked **[GAP A]** and **[GAP B]** below; they are the
review.

This package is **candidate** until that review. Nothing here is represented as certified-secure.

---

## 1. What we built (mechanism-complete)

A statistical-ZK witness-hiding layer for the S-two circle STARK, **masking-only** (no quotient-chunk
decomposition / no perfect-ZK dependent correction), feature-gated behind `statistical-zk`, with the
transparent (non-ZK) path byte-identical. Three layers, all wired and tested end to end on WideFib
(no LogUp) and PLONK (real LogUp):

- **Layer 1 — column masking.** Each witness and LogUp-interaction column is committed as
  `ŵ = w + v_H·r`, agreeing with `w` on the trace domain `H` (AIR unchanged) and randomizing every
  off-domain / FRI-query opening. Handles offset-0 and transition (shifted-row) reads.
- **Layer 2 — composition masking.** The composition quotient is masked `q' = q + t` with `t` committed
  **unsplit** as a separate tree; the verifier checks `q'(ζ)_eff − t(2ζ)` against the trace-derived
  value. Committing `t` unsplit is the crux that hides the separate-chunk DOF (the §3 decomposition
  pitfall).
- **Layer 0 — salted hiding Merkle.** Every witness-bearing tree carries a leaf-size random salt column
  (no OODS sample, FRI-invisible, Merkle-bound) so authentication paths do not leak unopened leaves.

The full argument — definition, simulator, four lemmas, dimension budget, distance bound — is in
**`NATIVE_STWO_STATISTICAL_ZK_PROOF_SKETCH.md`** (read this first; Appendix B has the as-implemented
corrections, B.7 the implemented composition quantities, B.8 the LogUp multiplicity analysis).

## 2. The two questions we cannot close (the actual review)

- **[GAP A] — column-opening blinding (proof sketch §6, Ask #3).** The circle-FFT evaluation map `E` of
  the randomizer basis at the revealed OODS/query points must not be *identically* rank-deficient,
  accounting for the conjugate-pair structure `f(p̄) = conj(f(p))`. We give the dimension budget
  (`h_col ≥ e·n_F + n_D`) and numerical full-rank evidence at deployed points; the **general
  non-degeneracy theorem over all admissible configurations, with its Schwartz–Zippel `ε`**, is yours.
- **[GAP B] — composition `t` sufficiency (proof sketch §7, Ask #2).** That an *independent* `t` suffices
  for the **statistical** target — rather than the perfect-ZK *dependent* correction of Haböck–Kindi §4 —
  is the highest-value claim. We show single-point chunk-hiding cleanly and give the reconstruction-
  resistance budget (`4·h_t > e·(n_F^comp + n_D)`); the **joint full-rank bound over all revealed points
  and its `ε`** is yours.

The final distance bound `Δ ≤ ε_M + ε_col + ε_comp ≤ 2⁻¹⁰⁰` is conditional on GAP A / GAP B.

## 3. Supporting evidence (NOT proof — read as falsifiable mechanism checks)

| Evidence | What it shows | What it does NOT show |
|---|---|---|
| Numerical rank check (`crates/stwo/src/prover/statistical_zk_rank_check.rs`) | `E` reaches full rank `e·n_F+n_D` at the budget and fails one below; `t` is under-determined at the budget and reconstructible when over-opened (negative control); `M ≠ 0` on the real query domain; conjugate counting | Non-degeneracy over *all* configs / random challenges; the `ε`. Computed facts at tested params only. |
| Two-witness same-statement (`test_wide_fib_multi_witness_same_statement_indistinguishable`) | many distinct witnesses, one public statement: the statement commitment is byte-identical across all, all verify, masked openings do not collide | statistical indistinguishability (that is GAP A) |
| Randomizer isolation (`*_trace_masking_randomizes_openings`, PLONK + WideFib) | same witness, different randomizer ⇒ masked openings differ (the mask is not a no-op) | absence of leakage |
| LogUp multiplicity (`test_claimed_sum_leaks_multiplicities_unless_balanced`, B.8) | the only non-opening multiplicity channels are `claimed_sum` and geometry; `claimed_sum` must be balanced (`= 0`), enforced by `assert_lookup_balanced` | — |
| Budget enforcement (`prove_zk` / `verify_zk`, fail-closed) | undersized `t` rejected prover- and verifier-side | that the enforced budget is *sufficient* (GAP B) |
| Overhead benchmark (`bench_wide_fib_zk_overhead`) | prover overhead +29% (n=6) → +48% (n=8) → +120% (n=10), an UPPER BOUND — the harness over-provisions the randomizer to the full coefficient space and masks every column to the enlarged geometry | production overhead at budget-sized randomizers (`h_t ≈ n_F+n_D+1`, `h_col`), expected far lower |

## 4. Code map

| Layer / piece | Location |
|---|---|
| Masking primitives, budgets, balanced check | `crates/stwo/src/prover/statistical_zk.rs` |
| Composition `q'=q+t`, salt, prove path | `crates/stwo/src/prover/mod.rs` (`prove_zk`) |
| OODS extractors `q'(ζ)_eff`, `t(2ζ)` | `crates/stwo/src/core/proof.rs` |
| Verifier DEEP-ALI `q'(ζ)_eff − t(2ζ)` | `crates/stwo/src/core/verifier.rs` (`verify_zk`) |
| Numerical evidence | `crates/stwo/src/prover/statistical_zk_rank_check.rs` |
| LogUp / PLONK harness | `crates/examples/src/plonk/mod.rs` |
| WideFib trace-masking harness | `crates/examples/src/wide_fibonacci/fib_with_preprocessed.rs` |

Prototype history (branch `native-statistical-zk`): Layer-1 primitives `33cee95`; Layer-2 `t` +
proof sketch `050432e`; rank check `f207c80`; Layer-2 wiring `58d1e31`; PLONK LogUp `592ee2b`;
proof-sketch Lemma 2 `6fdf920`; Layer-1 base-trace masking `aa9f73b`; offsets + interaction `01af06f`;
Layer-0 salt `6728e5c` / `9589ee0`; budget + rank check `6e94d84`; LogUp multiplicity + balanced check
`f9fd197`.

## 5. Specific asks

1. **[GAP A]** Is `E` provably non-identically-rank-deficient on the circle at all admissible OODS/query
   sets (conjugate pairs accounted), and what is the resulting `ε_col`?
2. **[GAP B]** Does an independent `t` (committed unsplit, reconstruction-resistance budget) suffice for
   the statistical target, or is the §4 dependent correction required? What is `ε_comp`?
3. Is the dimension budget (`h_col ≥ e·n_F + n_D`, `4·h_t > e·(n_F^comp + n_D)`) tight / correct?
4. Any gap in the simulator (proof sketch §9) or the hybrid (§4)?

## 6. Known limitations (disclosed, not hidden)

- **`claimed_sum` channel-binding.** The balanced (`claimed_sum = 0`) dark-pool path is safe. The
  alternative "nonzero `claimed_sum` pinned by the public statement" is safe for *hiding* but is
  currently **unsound** in the PLONK ZK harness because `claimed_sum` is not mixed into the Fiat–Shamir
  transcript there — bind it before use if that variant is ever needed (proof sketch B.8).
- **`COMPOSITION_LOG_SPLIT = 1`** (hardcoded, `verifier.rs`) blocks constraint-degree ≥ 2 AIRs
  (poseidon, realistic RFQ dark-pool circuits). A product blocker, orthogonal to the hiding argument.
- The masking is a **low-degree blind**; its adequacy is exactly GAP A / GAP B.

---

*References: Haböck & Kindi, ePrint 2024/1037; Haböck, Levit, Papini, ePrint 2024/278; Carmon, Goldberg,
Haböck, Lerer, Lesokhin, ePrint 2026/532.*
