# Soundness & Zero-Knowledge Audit Plan — stwo statistical-ZK fork

**Author role:** staff cryptographer (circle-STARK co-design background), engaged to *prove* — not
assert — the security of the modifications on branch `native-statistical-zk` of the f3rmion/stwo fork.

**Discipline.** Every claim below is an *obligation to discharge*, not a result. The construction is
CANDIDATE until each obligation is closed by a written reduction, a machine-checked algebraic lemma, or a
cryptographer-signed distance bound. ZK failures are silent; soundness failures are loud — the two
properties get different evidentiary standards (a passing test is meaningful evidence for soundness, and
*no* evidence for zero-knowledge).

---

## 0. The two properties (do not conflate)

| | (A) Knowledge-soundness | (B) Statistical HVZK (no-leak) |
|---|---|---|
| Adversary | malicious **prover** `A_snd` | malicious/curious **verifier** / distinguisher `A_zk` |
| Goal | accept a statement with **no** witness | learn a bit of the witness `w` |
| Target | soundness error `≤ 2⁻⁸⁰` (FRI + grinding + S–Z), tight to base stwo | distance `ε ≤ 2⁻¹⁰⁰`, for **all** `w` |
| Failure mode | LOUD (a forged proof verifies) | SILENT (verifies, passes two-witness tests, still leaks) |
| Evidence admissible | reductions, machine-checked identities, mutation/fuzz tests | reductions + general rank theorems ONLY; tests are not evidence |

Both must be proven. The masking (B-motivated) altered the commitment geometry, the composition split,
and the Merkle tree shapes that (A) rests on — so (A) is **re-opened** by this work and is not inherited
for free from upstream stwo.

**Trust base (assumptions, to be stated explicitly in the final proof):** ROM for the hash; the circle
FRI low-degree-test soundness (ePrint 2024/278 + 2026/532); the binding of the (salted) Merkle vector
commitment; the M31/QM31 field arithmetic.

---

## 1. Object under audit — the modifications, enumerated

| # | Modification | Files | Touches |
|---|---|---|---|
| M1 | Layer-1 column masking `ŵ = w + v_H·r` (base + interaction, all offsets), lifted geometry, reduced vanishing `masked_constraint_log_degree_bound` | `prover/statistical_zk.rs`, `constraint-framework/.../component.rs` | A + B |
| M2 | Layer-2 composition randomizer `q' = q + t`, `t` committed UNSPLIT, check `q'(ζ)_eff − t(2^k·ζ)` | `prover/mod.rs::prove_zk`, `core/verifier.rs::verify_zk`, `core/proof.rs` | A + B |
| M3 | Layer-0 salted hiding Merkle (leaf-size salt column, no OODS sample) | `prover/mod.rs`, `statistical_zk.rs`, `constraint-framework/.../component.rs` | A (binding) + B |
| M4 | `COMPOSITION_LOG_SPLIT` generalization: `2^k` chunks via `split_k`, Horner-fold recombination `recombine_split_evals`, `t` at `repeated_double(k)`, `k = composition_log_degree_bound − base` | `prover/poly/circle/secure_poly.rs`, `core/proof.rs`, `core/verifier.rs`, `prover/mod.rs`, `core/air/components.rs` | **A (primarily)** + B |
| M5 | Empty lifted-Merkle tree height fix (column-less tree → height 0 regardless of forced lifting) | `core/vcs_lifted/verifier.rs` | A (binding/decommit) |
| M6 | Leakage budget enforcement (`4·h_t > e·(n_F^comp+n_D)`, `h_col ≥ e·n_F+n_D`), fail-closed; balanced-lookup check (`claimed_sum = 0`) | `statistical_zk.rs`, `prover/mod.rs`, `core/verifier.rs` | B + **A (claimed_sum binding — see V7)** |

---

## 2. Adversary models

- **`A_snd` (soundness):** PPT, adaptive, *chooses every committed value and every off-protocol quantity*,
  sees all Fiat–Shamir challenges as they are derived (can grind the transcript up to the PoW bound).
  Wins if `verify`/`verify_zk` returns `Ok` on a statement for which no valid witness exists. This is the
  red team's primary target.
- **`A_zk` (zero-knowledge):** honest-verifier distinguisher; given the public statement `x` and a real
  transcript, decides between two prover witnesses `w₀, w₁` (or extracts a function of `w`). Wins with
  advantage `> ε`.
- **`A_fs` (Fiat–Shamir):** a soundness sub-adversary specialising in transcript/challenge manipulation:
  reorders absorptions, injects unbound public inputs, grinds challenges.

The audit must keep these separate: an attack that helps `A_zk` (e.g. `t`-reconstruction) is a privacy
break, not a forgery; an attack that helps `A_snd` (e.g. an unbound `claimed_sum`) is a forgery, not a
leak.

---

## 3. Property (A) — knowledge-soundness, proof plan

**Strategy: a transparent-transformation reduction.** Show the modified argument's soundness reduces to
(i) base stwo/circle-FRI soundness and (ii) a finite set of *algebraic identities* and *non-degeneracy
edges*. The masking randomizers (`r`, `t`, salt) are committed **before** the OODS point `ζ` is drawn, so
under Fiat–Shamir they are *fixed* adversarial constants by the time `ζ` is sampled — every soundness
argument therefore conditions on fixed `r, t, salt` and applies the base DEEP-ALI + FRI reduction to the
fixed polynomials. This is the backbone; the obligations below are the places that backbone can break.

### Soundness obligations & their adversaries

**O-A1 (M2 — composition mask does not absorb cheating).** Prove: if `verify_zk` accepts, then with
probability `≥ 1 − ε_snd` the committed trace satisfies the AIR on `H`.
- *Reduction:* `t` is committed (tree built, root mixed) **before** `ζ` → `q' = q + t` is a fixed
  committed polynomial; the check `q'(ζ)_eff − t(2^k ζ) = N(ζ)/v_H(ζ)` equals `q(ζ) = N(ζ)/v_H(ζ)` at a
  random `ζ`. Since `q', t` are independently FRI-tested low-degree polynomials, `q = q' − t` is
  low-degree; DEEP-ALI + Schwartz–Zippel give the base soundness error. **Discharge by reduction to base
  stwo soundness on the fixed `q'−t`.**
- *Attack `A_snd`-1 (high-degree `t`):* prover commits a `t` that is NOT low-degree to gain a
  degree-of-freedom. **Obligation:** prove `t` is genuinely FRI-tested. Evidence in-code: a committed
  column enters the FRI quotient **iff it has an OODS sample** (`pcs/quotients.rs`); `t`'s four coordinate
  columns each have the sample at `2^k·ζ`, so `t` is degree-bounded. **Verify rigorously**, including that
  the unsplit `t` at the *full* composition degree bound is tested at that bound (not a looser one).
- *Attack `A_snd`-2 (salt smuggling):* prover hides a non-low-degree column as the "salt". **Obligation:**
  prove the salt column, having **no** OODS sample, never enters the quotient and is never read by a
  constraint, so it cannot affect the accepted relation (it is pure Merkle padding). Confirm it also
  cannot be *read* via a mask offset (it is appended after the trace-location capture).

**O-A2 (M4 — recombination is exact and edge-free).** This is the highest-risk new soundness surface.
- *Identity to machine-check:* for all `k ≥ 1` and all admissible `ζ`,
  `recombine_split_evals(open(chunks), ζ, max_log_degree_bound, k) = q'(ζ)` exactly, where the multipliers
  are `ζ.repeated_double(max_log_degree_bound − 1 + i).x`, `i = 0..k`, deepest level first. A wrong fold
  makes the verifier test the wrong quantity → unsound. **Discharge by a machine-checked proof (Lean/Coq)
  over the circle group**, reducing to the single-`split_at_mid` identity `p(z) = p_L(z) + π·p_R(z)`,
  `π = z.repeated_double(L−2).x`, composed `k` times. (Computational corroboration: the `k = 0..3`
  recombination test exists; it is *evidence*, not the theorem.)
- *Attack `A_snd`-3 (vanishing multiplier → dropped chunk):* if any Horner multiplier
  `repeated_double(max_log_degree_bound − 1 + i).x = 0` on the query/OODS domain, a chunk drops out of the
  recombination and a malicious prover can commit garbage in it. **Obligation:** generalise the §B.1
  `M ≠ 0` argument from `k = 1` to *every level* `i = 0..k` — prove `repeated_double(e).x ≠ 0` for each
  exponent `e ∈ {max_log_degree_bound−1, …, max_log_degree_bound+k−2}` on the canonic query domain
  (the `M = 0 ⟺ exponent = L_dom − 1 ⟺ blowup = 0` closed form must be re-run per level). A single
  vanishing level is a forgery.
- *Attack `A_snd`-4 (prover-chosen `k`):* `k` must be a public function of the AIR, not a prover DOF.
  **Obligation:** prove `k = composition_log_degree_bound − base` is computed identically by P and V from
  public data (`base = Components::base_trace_log_degree_bound` transparent / `…base_constraint…` ZK), is
  independent of committed *values*, and that a prover committing `2^{k'}` chunks with `k' ≠ k` is rejected
  at the size/commit check. (Note the discovered subtlety: the verifier's PCS `column_log_sizes` are
  blow-up-extended and `column_log_sizes()` asserts preprocessed completeness — confirm the chosen
  AIR-derived `base` is the unique consistent value on both sides.)
- *Attack `A_snd`-5 (`t` doubled-point collision):* `t` is opened at `2^k·ζ`. **Obligation:** prove
  `2^k·ζ` lands on the intended effective fold point and does NOT collide with a query position, a special
  point (`y = 0`, conjugate-self), or the trace domain in a way that lets the cancellation `q'−t` be
  satisfied without a valid `q`.

**O-A3 (M1 — masking preserves the AIR and its degree bookkeeping).**
- *Sub-obligation O-A3a (on-`H` agreement):* `v_H ≡ 0` on `H` ⇒ `ŵ = w` on `H`. Trivial, but state it in
  the *lifted* frame (masked geometry) so it is not vacuous.
- *Sub-obligation O-A3b (the `VB − (M − m) = n` cancellation):* the masked column is opened in a frame
  lifted `m − n` levels; the constraint vanishing is taken at the **reduced** degree
  `max_log_degree_bound − (m − n)` and the mask-offset translation steps by that reduced coset.
  **Obligation (machine-checked):** prove this reduced vanishing equals `v_H` evaluated in the lifted
  opening frame, for **all** masked enlargements `(m, n)` and **all** mask offsets — a wrong neighbour on a
  transition constraint lets `A_snd` satisfy a shifted-row relation with inconsistent rows
  (*attack `A_snd`-6*). The implementers proved a general `VB − (M − m) = n`; the audit must
  *independently* re-derive and machine-check it.
- *Attack `A_snd`-7 (degree headroom):* `ŵ` has higher degree than `w`; prove the enlarged committed
  column is FRI-tested at the masked bound so the headroom cannot encode an out-of-AIR value that still
  passes the constraint quotient.

**O-A4 (M5 — empty-tree height fix is binding-preserving).**
- *Obligation:* prove that treating a **column-less** committed tree as height 0 (skipping its
  decommitment under a forced lifting) loses no binding. The column count per tree is **public**
  (AIR-fixed via `trace_log_degree_bounds`); a prover cannot claim a non-empty tree is empty (the verifier
  derives the expected sizes from the AIR and the commit would mismatch). The root of a column-less tree is
  a public constant; nothing is "hidden" in it. **Confirm:** (i) no queried values are expected from a
  height-0 tree, (ii) the FRI bound (`trees.last().height`) and query-position preparation are unaffected,
  (iii) the change is inert for all non-empty trees and for empty trees with no forced lifting (`k=1`
  byte-identity). *Attack `A_snd`-8:* prover commits data in a tree it declares column-less — rejected by
  the public size check; verify there is no path that declares a tree empty while decommitting values from
  it.

**O-A5 (M3/M4 — FRI soundness under the lifted multi-height frame).**
- *Obligation:* the forced lifting pins columns that sit `k` levels below the FRI degree bound (trace,
  interaction, composition chunks) into one FRI domain. Prove the circle-FRI soundness bound is preserved
  for columns `k > 1` levels below the bound (the DEEP-quotient / degree-correction for lifted columns).
  The empty-tree bug (M5) was a *decommit* manifestation of this lifted frame; the audit must confirm
  there is no *soundness* manifestation (e.g. a column that is low-degree at the lifted bound but not at
  its true bound passing FRI). *Attack `A_snd`-9:* prover exploits the lift to pass a column that is not
  low-degree at the claimed split bound.

**O-A6 (Fiat–Shamir binding — protocol fix landed + balanced path demonstrated).**
- *Attack `A_fs`-1 (unbound `claimed_sum` — PROTOCOL-CLOSED + DEMONSTRATED):* the LogUp public sum
  `claimed_sum` was originally **not mixed into the channel**; it entered only as a constraint constant, so
  for a **nonzero, statement-pinned** `claimed_sum` an `A_snd` could choose it *after* seeing the challenges
  → adaptive forgery. **Resolved two ways, both landed:** (i) `claimed_sum` is now absorbed into the
  transcript **before** `lookup_elements`/`ζ` are drawn (`Component::claimed_sum` + `mix_felts` in
  prove_zk/verify_zk, `c5e8a98`), closing the adaptive vector; and (ii) the **balanced** lookup path
  (`claimed_sum = 0`, enforced by `assert_lookup_balanced`) is now **demonstrated end-to-end** — fixture
  `examples/src/logup_balanced` proves+verifies a permutation LogUp whose verifier enforces the gate, and
  the unbalanced PLONK fixture is an explicit negative test (`test_unbalanced_plonk_claimed_sum_rejected`,
  `c088649`). **Residual:** for a deployed circuit the audit must still verify the verifier checks the
  bound value against its expected total (`0` balanced, or the statement-pinned value) — that
  instantiation is the dark-pool integration's, the mechanism is no longer in question.
- *Attack `A_fs`-2 (absorption order):* prove the transcript order binds every new commitment before the
  challenge that depends on it: `commit(q'+salt) → commit(t+salt) → draw ζ`. Confirm `t` is bound before
  `ζ` (else adaptivity) and the randomizer dimension / budget are not themselves challengeable.

### (A) methodology & evidence
1. **Reductions** (pen-and-paper, peer-reviewed) for O-A1, O-A4, O-A5, O-A6.
2. **Machine-checked algebra** (Lean 4 over M31/QM31 + circle group) for the load-bearing identities:
   O-A2 (Horner recombination + per-level `M≠0`), O-A3b (`VB−(M−m)=n`). These are finite, exact, and the
   highest-risk; they deserve formal proof, not prose.
3. **Adversarial mutation/fuzz testing** (loud-failure property): systematically perturb a committed chunk,
   a `t` coordinate, a salt value, a mask offset, the recombination multiplier, `k`, the doubled point —
   assert `verify_zk` REJECTS. A surviving mutation is a soundness bug. Extend the differential harness to
   degree-2 (poseidon-zk) and to `k ≥ 3`.
4. **Concrete soundness-error accounting:** FRI + PoW grinding + Schwartz–Zippel (recombination, DEEP-ALI)
   + per-level `M≠0` union bound, instantiated at deployed parameters.

---

## 4. Property (B) — statistical zero-knowledge, proof plan

**Strategy: simulator + hybrid, already drafted** (proof sketch §4–§10, App. B). The simulator `S(x)` is
ours to finish; the two rank theorems and the final `ε` are the cryptographer's deliverable. Restated as
obligations:

**O-B1 (Lemma 0 — Merkle hiding).** With salted leaves, (roots, auth paths) are simulatable independent of
unopened leaves, error `ε_M`. *Caveat surfaced by M4:* the salt sits at leaf size only when it is one
level above the chunks; the audit must confirm the **deployed** salt geometry gives per-leaf-independent
salt (the `k>1` composition salt is at `max_log_degree_bound`, one level above the *chunks at `comp−k`* —
re-examine whether a `k>1`-fold replication weakens `ε_M`, since the chunks and salt now differ by `k`
levels in the same tree). State `ε_M` as a function of `k`.

**O-B2 (Lemma 1 — column hiding) = GAP A.** Prove the circle-FFT evaluation map `E` (randomizer basis at
the revealed OODS/query points, in `F_q`-coordinates, accounting for `f(p̄) = conj(f(p))`) has full row
rank `e·n_F + n_D` at **all** admissible configurations, and bound the Schwartz–Zippel failure `ε_col`
over the random challenges. *Adversary `A_zk`-1:* find an admissible OODS/query set where `E` is
identically rank-deficient (a `w`-dependent opening survives the mask). This is one of the two genuinely
novel theorems; numerical full-rank at tested params is corroboration only.

**O-B3 (Lemma 2 — chunk hiding via unsplit `t`) = GAP B.** Prove the *joint* `R ⊕ S` map (revealed
`t`-functionals `R` ⊕ per-point split-direction freedoms `S`) is full rank, so an *independent* `t`
suffices for the **statistical** target (i.e. the Haböck–Kindi §4 *dependent* quotient correction is not
required), and bound `ε_comp`. Must be redone in the **implemented** quantities `{q'_left, q'_right,
t(2^k ζ)}` (App. B.7) **and generalised to `2^k` chunks** — the `k`-fold split exposes `2^k − 1`
split-direction freedoms per point, not one; prove the unsplit `t` covers all of them. *Adversary
`A_zk`-2:* over-determine `t` (the reconstruction attack) — the audit must confirm `4·h_t > e·(n_F^comp +
n_D)` is *sufficient* for general `k`, not just `k = 1` (the budget may need a `k`-dependent term, since
there are now `2^k − 1` freedoms).

**O-B4 (Lemma 3 — FRI/final layer add nothing).** Deterministic public images of simulated openings;
contributes `0` beyond the rank events. Confirm for the lifted multi-height frame and `2^k` chunks.

**O-B5 (LogUp multiplicity channel).** Confirm App. B.8: the only multiplicity-dependent non-opening
quantities are `claimed_sum` (→ balanced, O-A6) and committed geometry (→ fixed padded geometry). The
audit re-runs the channel enumeration adversarially (a third channel is a privacy break).

**O-B6 (the bound).** `Δ(S(x), real) ≤ ε_M + ε_col + ε_comp ≤ 2⁻¹⁰⁰` at deployed parameters, with the
dimension budget `h_col ≥ e·n_F + n_D`, `h_t ≳ (k-aware) d·(e·n_F + n_D)`. **Self-certification is
explicitly disallowed** — this line is the cryptographer's signature.

### (B) methodology & evidence
- General rank theorems (GAP A/B) — pen-and-paper, the novel research deliverable; target a short note
  suitable for the Haböck review.
- The **rank-check harness** (`statistical_zk_rank_check.rs`) extended to: degree-2 (`k=2`) deployed
  points, the `2^k − 1` split freedoms, the `k`-aware `t` budget, and negative controls (must fail).
  *Corroboration only.*
- Two-witness indistinguishability + empirical leakage scan — *mechanism evidence, not proof*; keep the
  "not a certificate" labelling.

---

## 5. Red-team catalog (single index of attack vectors)

| ID | Property | Vector | Status |
|---|---|---|---|
| A_snd-1 | A | high-degree `t` evades FRI | obligation O-A1 |
| A_snd-2 | A | non-low-degree "salt" smuggling | obligation O-A1 |
| A_snd-3 | A | vanishing Horner multiplier drops a chunk | obligation O-A2 (extend B.1 per level) |
| A_snd-4 | A | prover-chosen `k` / chunk count | obligation O-A2 |
| A_snd-5 | A | `t` doubled-point `2^k·ζ` collision | obligation O-A2 |
| A_snd-6 | A | wrong shifted-row neighbour (masked offset) | obligation O-A3b |
| A_snd-7 | A | mask degree headroom encodes out-of-AIR value | obligation O-A3 |
| A_snd-8 | A | declare non-empty tree as column-less | obligation O-A4 |
| A_snd-9 | A | lifted column low-degree at lift but not at true bound | obligation O-A5 |
| **A_fs-1** | **A** | **unbound `claimed_sum` → adaptive forgery** | **FIX LANDED + DEMONSTRATED** — channel-bound before challenges (`c5e8a98`); balanced gate `assert_lookup_balanced` proven end-to-end on `logup_balanced` fixture + negative test on PLONK (`c088649`). Deployed-circuit instantiation of the check remains the integration's |
| A_fs-2 | A | absorption-order / FS binding | obligation O-A6 |
| A_zk-1 | B | `E` identically rank-deficient (GAP A) | obligation O-B2 |
| A_zk-2 | B | `t` over-determined / reconstruction (GAP B, `k`-aware) | obligation O-B3 |
| A_zk-3 | B | salt replication for `k>1` weakens Merkle hiding | obligation O-B1 |
| A_zk-4 | B | third multiplicity channel beyond `{claimed_sum, geometry}` | obligation O-B5 |

### 5.1 Red-team rounds (claude-committee, candidate evidence — NOT a substitute for the §7 firm audit)

Each round = independent adversaries (one per property/dimension) attempt to break a specific claim, then
every claimed break is handed to an independent skeptic instructed to *refute* it (falsify-before-certify).
A break counts only if the skeptic cannot refute it from the code. Claude red-teaming is statistical and
fallible; these rounds raise confidence and catch regressions, they do not discharge any soundness/ZK
obligation.

- **Round 1** (during M6/M8 hardening). Confirmed: unbound `claimed_sum` adaptive vector (→ A_fs-1, fixed
  `c5e8a98`); non-`k`-aware GAP B budget (→ k-aware floor, `6bff7fb`); prefix sampler left split chunks
  unmasked (→ spread sampler, `6bff7fb`). Corrected an over-called T3 deployment constraint.

- **Round 2** (post-`c088649`, surface = balanced fixture + `claimed_sum` binding + spread sampler/k-aware
  budget). 5 dimensions — soundness×2, hiding/two-witness, code-isolation, budget-arithmetic — 20 claims,
  **1 confirmed, 19 refuted. Zero soundness, zero hiding, zero scope breaks.** The one confirmed finding was
  an **implementation-isolation** defect, not a protocol weakness: the `logup_balanced` module was declared
  un-gated in `lib.rs`, so with `statistical-zk` OFF its feature-only helpers/imports became dead-code and
  the repo's `-Dwarnings` broke the transparent examples build — a feature-gating-invariant violation
  (auditor duty, §7). Fixed by gating the module (`3454061`), verified both ways (feature-off build clean,
  feature-on test green). Refuted highlights, each by independent skeptic: `claimed_sum` is structurally
  pinned by the LogUp boundary constraint and verifier-supplied (never proof-sourced), so the gate living in
  a test wrapper is correct design; the default-zero `claimed_sum()` cannot restore adaptivity; the
  composition-only fixture opens public constants (no witness to leak). The budget-arithmetic dimension
  refuted all its own probes; the skeptic additionally flagged one adversary's "rank deficient by 192"
  figure as **fabricated** (absent from the repo) — recorded here as a reminder that committee numbers
  require code-grounding. Per-chunk sufficiency remains open GAP B (O-B3), by design.

- **Round 3** (surface = the soundness CORE, not the latest diff). 5 dimensions — split/recombine
  (A_snd-3,4,5), lifted-frame masking (A_snd-6,7,9), salt/Merkle/tree (A_snd-1,2,8), FS absorption order
  (A_fs-2), and k-derivation/extraction. 18 claims; **zero soundness, zero hiding, zero scope breaks** in
  the committed code. Triage of the raw "6 confirmed": (a) **five** of them were the SAME uncommitted
  `eprintln!("PROBE prove_zk: …")` an adversary wrote into the working tree as a perturbation probe — not in
  `HEAD`, a workflow self-artifact, discarded (the committed prover is clean); (b) the lone "high" empty-tree
  height-0 early-return (`vcs_lifted/verifier.rs:118-120`) was a **false positive** — the skeptic confirmed
  it with "no forge built", but the tree's emptiness is AIR-derived (`column_log_sizes` from the AIR, never
  the proof), so a populated tree cannot be declared empty and an empty tree allocates no queried values and
  contributes nothing to FRI; verdict rejected on manual code review; (c) the **one genuine** finding was a
  test-coverage gap: no negative test asserted `verify_zk` REJECTS a tampered masked-trace opening — fixed
  by `test_plonk_zk_trace_masked_tampered_opening_rejected` (`147b4fb`), which demonstrates the reduced-degree
  DEEP-ALI check has teeth on the masked geometry (it does not bound an adversarial masked column — the open
  GAP-A rank theorem). Refuted highlights, each code-grounded: recombine exponents `repeated_double(mlb-1+i)`
  correct for k=0..3 with the lifted-frame fold cancelling the off-by-k; prover-k == verifier-k (identical
  pure trait composition, both AIR-derived); transparent `extract_composition_oods_eval` byte-identical at
  k=1; FS transcript in lockstep with `t` and `claimed_sum` bound before ζ; salt is Merkle-bound only and
  dropped by every extractor. **Process note:** round 3 hit the account session limit mid-run and was
  completed by resuming the workflow (cached agents replay, only failed agents re-run); two adversaries also
  mutated the working tree (the PROBE + a split-recombine repro test) — a reminder that committee runs can
  leave self-inflicted scratch that must be triaged out, not committed.

- **Round 4** (surface = the PERFORMANCE changes + regressions). Two landed perf commits: batched Layer-1
  masking (`4c096cf`, `mask_columns` hoisting the per-column-shared twiddles + `v_H`) and per-tree FRI
  query-position routing (`f315d4c`). 4 dimensions — routing-soundness, masking-equivalence, masking-hiding,
  regression-interaction. 6 claims; **zero soundness, zero hiding, zero correctness, zero scope breaks.**
  Strongest verifications, all code-grounded: a skeptic's 548,862-case check proved the per-tree remap binds
  exactly the value FRI consumes (`prepare(prepare(raw,L,h),h,lc) == prepare(raw,L,lc)`) and is the identity
  for full-height trees, so `f315d4c` changes no committed root and the transparent path stays byte-identical;
  `mask_columns` is bit-identical to the old per-column `mask_column` (RNG order/count preserved, hoisted data
  is RNG-free) with the only behavioral delta (an error-variant ordering) proven unreachable via disjoint
  cosets; batching preserves per-column randomizer independence. **Anti-fabrication worked:** multiple
  skeptics flagged adversaries citing tests "not in the committed tree" and a phantom test name
  (`temp_redteam_intersect_unreachable_scan`) from a STALE compiled binary; verified against `HEAD` (grep
  count 0, not tracked) — the phantom does not exist in committed code, no fix needed. Round 4 added no
  commits (no real findings).

---

## 6. Milestones & gates

- **G0 — scope freeze.** Pin the modification set, the deployed AIRs (incl. degree, LogUp balance), the
  parameters, the trust base. Output: this document, ratified.
- **G1 — soundness reductions (A).** O-A1, O-A4, O-A5, O-A6 written and peer-reviewed. **Hard gate:**
  A_fs-1 (`claimed_sum`) resolved in code (balanced-only OR channel-bound) before any "sound" claim.
  *Status:* protocol half done — `claimed_sum` is channel-bound (mixed before challenges), adaptive
  vector closed (`c5e8a98`); balanced gate demonstrated end-to-end — `logup_balanced` fixture enforces
  `assert_lookup_balanced` with a green prove/verify and a PLONK negative test (`c088649`). The only
  remaining piece is instantiating the verifier's check (bound value vs. expected total) on the deployed
  dark-pool circuit — the integration's, with the mechanism no longer open.
- **G2 — machine-checked algebra (Lean).** The Tier-1 theorems of §8 — `T1` recombination identity,
  `T2` reduced-vanishing cancellation, `T3` per-level multiplier non-vanishing, `T4` on-`H` vanishing —
  proved in Lean against the trust-base axioms `Ax1–Ax3`. **Hard gate:** no soundness sign-off without
  `T1`–`T3` (a silent error in any of them forges proofs); these are the load-bearing identities and are
  *fully* machine-checkable, so prose is not accepted here.
- **G3 — adversarial mutation suite.** Loud-failure fuzzing across M1–M5, degree-2 and `k≥3`; zero
  surviving mutations. (Complements G2: G2 proves the identity is *right*; G3 proves the *code computes
  the identity*. The Tier-1 Lean theorems should be connected to the Rust via an extraction/oracle test.)
- **G4 — ZK rank theorems (B).** GAP A (O-B2) and `k`-aware GAP B (O-B3): the §8 Tier-3 *statements*
  (`T7`) are pinned in Lean so the cryptographer proves the right proposition; the *proof* is the novel
  research deliverable (Lean-checkable once a constructive argument exists, else pen-and-paper under
  external sign-off). `ε` (O-B6, `T8`) computed. Self-certification disallowed.
- **G5 — report.** Combined soundness reduction + ZK distance bound + assumptions + residual risk; the
  artifact that ships with the Haböck package.

**Gate ordering note:** G1–G3 (soundness) can and should proceed *in parallel* with, and independently of,
G4 (ZK). A sound-but-leaky system is a safe-but-useless dark pool; a leak-free-but-unsound system mints
fake trades. The product needs both gates green.

---

## 7. Roles
- **Lead (staff cryptographer):** reductions, the two rank theorems, final bound, sign-off.
- **Formal-methods engineer:** the Lean development of §8 (Tier-1 proofs; Tier-2 decision procedures;
  Tier-3 statements + axiom interface).
- **Adversarial reviewer(s):** the red-team catalog (§5) — independent attempts to realise each vector;
  a realised attack is the most valuable output.
- **Implementation auditor:** transcript order, fail-closed budget, byte-identity of the transparent path,
  feature-gating, the empty-tree fix's inertness on all other commitments; the §8 extraction/oracle test
  binding Lean theorems to the Rust.

---

## 8. Formal-verification (Lean) specification — pinning the hard problems

The point of this section is to state the load-bearing problems *as Lean propositions*, so "we proved it"
means a `#print axioms` with nothing but the declared trust base — not a convincing paragraph. Equally
important: to be **honest about what Lean cannot settle**, so effort is not wasted formalising the wrong
layer. Three tiers.

### 8.0 Trust base, as Lean axioms (the only things we are allowed to assume)
These are the boundary of the formal development; everything else must be *derived*.
```lean
-- Ax1: circle-FRI low-degree soundness (ePrint 2024/278 §FRI, 2026/532). We do NOT re-prove FRI.
axiom fri_soundness {F} [CircleField F] (bound : ℕ) (cfg : FriConfig) :
    ∀ (oracle : QueryOracle F), accepts cfg oracle →
      δ_close oracle (lowDegree bound) (friError cfg)       -- list-decoding/soundness statement

-- Ax2: Merkle vector-commitment binding in the ROM.
axiom merkle_binding {H} [RandomOracle H] : CollisionResistant H → Binding (MerkleScheme H)

-- Ax3: Fiat–Shamir / ROM challenge independence (challenges = RO of the prefix transcript).
axiom fs_challenges_uniform {H} [RandomOracle H] : ChallengesUniformGivenPrefix H
```
Any proof whose `#print axioms` shows more than `{Ax1, Ax2, Ax3, propext, Classical.choice, Quot.sound}`
is rejected.

### 8.1 Infrastructure to build (NOT in Mathlib — this is real, scoped work)
Mathlib has finite fields, `Polynomial`, `Matrix.rank`, `MvPolynomial`. It does **not** have the circle
primitives. The development must provide, with their algebraic laws:
`Mersenne31` (`M31`), `QM31` (degree-4 ext, `e = 4`); the circle group `Circle F` with `repeatedDouble`,
`x`, `conj`/`(x,−y)`; `CanonicCoset n`, the half-coset and its conjugate; `CirclePoly F` in the
**circle-FFT basis** with `eval`, `logSize`, `extend`, and the two operations under audit
`splitAtMid : CirclePoly → CirclePoly × CirclePoly` and `splitK : CirclePoly → ℕ → List CirclePoly`;
`vanishingH n` and `cosetVanishing`. This basis layer is the prerequisite for *every* Tier-1 theorem and
is where most of the Lean labour sits.

### 8.2 Tier 1 — FULLY machine-checkable, exact, decidable (the G2 hard gate)
Finite, deterministic identities over the circle/field. A silent error here forges proofs, so these get
*no* paper proof — Lean only.

```lean
-- T1 (O-A2, M4): the k-fold split recombines EXACTLY, in the lifted frame, for all k and all z.
--   `recombineSplitEvals` is the Horner fold with multipliers (z.repeatedDouble (mlb-1+i)).x, i=0..k.
theorem recombine_split_k_exact (p : CirclePoly QM31) (k : ℕ) (z : Circle QM31) (mlb : ℕ)
    (hmlb : mlb = p.logSize - k) :
    recombineSplitEvals ((p.splitK k).map (fun c => c.eval z)) z mlb k = p.eval z

-- T1a: degenerate base case ties T1 to the single split actually used at k=1 (byte-identity anchor).
theorem recombine_eq_splitAtMid (p : CirclePoly QM31) (z : Circle QM31) :
    recombineSplitEvals [p.splitAtMid.1.eval z, p.splitAtMid.2.eval z] z (p.logSize - 1) 1 = p.eval z

-- T2 (O-A3b, M1): the reduced masked vanishing equals v_H in the lifted opening frame, for ALL (n,m).
--   ŵ = w + vanishingH n · r committed at log m, opened lifted (m-n) levels; constraint vanishing taken
--   at the reduced degree. The constraint quotient is invariant under the lift.
theorem masked_constraint_quotient_invariant
    (n m mlb : ℕ) (hnm : n ≤ m) (w r : CirclePoly M31) (point : Circle QM31)
    (N : CirclePoly QM31) (hN : vanishesOn N (canonicCoset n)) :
    N.eval point / (cosetVanishing (canonicCoset (mlb - (m - n))) point)
      = N.eval point / (vanishingH n).eval point        -- equality under the (m-n)-level frame change

-- T3 (O-A2 / A_snd-3): NO Horner multiplier vanishes on the query domain, for every level and every k.
--   This is the per-level generalisation of App. B.1 (M = 0 ⟺ exponent = L_dom − 1).
theorem multiplier_nonzero_on_query_domain
    (mlb logBlowup i k L_dom : ℕ) (hk : i < k) (hblow : 1 ≤ logBlowup)
    (hL : L_dom = mlb + logBlowup) (z : Circle QM31)
    (hz : z ∈ (canonicCoset L_dom).points) :
    (z.repeatedDouble (mlb - 1 + i)).x ≠ 0
-- NOTE: this is the theorem MOST likely to reveal an edge. The closed form forces a root when
-- `mlb - 1 + i = L_dom - 1`, i.e. `i = logBlowup`. If `i = logBlowup` is reachable (`logBlowup < k`),
-- T3 is FALSE as stated and the deployment must constrain (k, logBlowup) — Lean will force this out
-- into the open rather than leaving it to a passing poseidon test. PIN IT DOWN HERE.

-- T4 (O-A3a, M1): v_H vanishes on H (so ŵ = w on H — the AIR is unchanged). Trivial but explicit.
theorem vanishingH_zero_on_H (n : ℕ) (p : Circle M31) (hp : p ∈ (canonicCoset n).points) :
    (vanishingH n).eval p = 0
```
**`T3` is the single most valuable thing to formalise first** — my own hand-analysis cannot currently
rule out a vanishing multiplier at `i = logBlowup` for `k > logBlowup`, and a passing poseidon test
(`k=2, logBlowup=1`) does **not** decide it. Lean settles it definitively, and either confirms safety or
hands us an exact `(k, logBlowup)` deployment constraint.

### 8.3 Tier 2 — Lean-able core + a thin probabilistic wrapper (decision procedures)
```lean
-- T5 (O-A1): DEEP-ALI Schwartz–Zippel. The algebraic identity is exact; the probability is a
--   root-count bound (Mathlib `Polynomial.card_roots`). t,q' fixed before ζ (Ax3) ⇒ q'-t fixed.
theorem deep_ali_soundness (q' t N vH : CirclePoly QM31) (D : ℕ)
    (hdeg : (q' - t - N / vH).natDegree ≤ D) :
    Pr_{ζ} [ (q' - t).eval ζ = (N/vH).eval ζ ∧ q' - t ≠ N/vH ] ≤ (D : ℝ) / Fintype.card QM31

-- T6 (O-B2/O-B3 at DEPLOYED points): a SPECIFIC evaluation/`t` matrix has full rank.
--   Decidable: `Matrix.rank` over M31 via `det ≠ 0` of a maximal minor. Upgrades the Rust rank harness
--   from "computed" to "proved" for fixed parameters (NOT the general theorem — that is T7).
theorem E_full_rank_at (params : DeployedParams) :
    (evaluationMatrix params).rank = params.e * params.n_F + params.n_D := by decide  -- or native_decide
```

### 8.4 Tier 3 — STATEMENT is Lean-able, PROOF is the research (or assumed)
Pinned in Lean so the cryptographer proves the right proposition; the body is the novel work.
```lean
-- T7 (O-B2/O-B3, GAP A / k-aware GAP B): GENERIC full rank = a non-vanishing determinant polynomial
--   over the challenge space. Statement is formal; proof needs a constructive non-vanishing argument
--   (then S–Z) — that argument is the unpublished research, not a formalisation task.
theorem E_not_identically_singular :
    (minorDet : MvPolynomial ChallengeVars QM31) ≠ 0
-- Corollary (S–Z, Mathlib): Pr_{challenges}[ rank deficient ] ≤ minorDet.totalDegree / card QM31.

-- T8 (O-B6): the distance bound, composing L0–L3; an inequality provable ONCE T7 is in hand.
theorem zk_distance_bound (x : Statement) :
    statDist (simulator x) (realTranscript x) ≤ ε_M + ε_col + ε_comp ∧ ε_M + ε_col + ε_comp ≤ 2^(-100)
```
**Not Lean-able / explicitly out of scope:** re-proving circle-FRI soundness from first principles (`Ax1`);
ROM idealisation (`Ax2/Ax3`). Formalising these is a multi-year program; we *assume* them and make the
assumption auditable via `#print axioms`.

### 8.5 Classification & build order
| Theorem | Obligation | Tier | Lean settles | Build order |
|---|---|---|---|---|
| `T1`,`T1a` | O-A2 recombination | 1 (full) | yes — exact | 2nd (needs basis layer) |
| `T2` | O-A3b vanishing cancel | 1 (full) | yes — exact | 3rd |
| **`T3`** | O-A2 / A_snd-3 edge | 1 (full) | **yes — and may FALSIFY** | **1st (cheapest, highest signal)** |
| `T4` | O-A3a on-H | 1 (full) | yes — trivial | with basis layer |
| `T5` | O-A1 DEEP-ALI | 2 | core yes, prob. wrapper yes | 4th |
| `T6` | O-B2/3 @ params | 2 | yes — `decide` | anytime (independent) |
| `T7` | GAP A / B generic | 3 | statement only | research-gated |
| `T8` | ε bound | 3 | after `T7` | last |

Build order: **(0)** circle-FFT basis infrastructure (§8.1) + the `Ax1–Ax3` interface; **(1)** `T3`
(cheap, decisive, may force a deployment constraint); **(2)** `T1/T1a`; **(3)** `T2`; **(4)** `T5`; `T6`
in parallel; `T7/T8` gated on the research. An **extraction/oracle test** must connect the Lean
`recombineSplitEvals`/`splitK`/vanishing definitions to the Rust ones (same fixed vectors → same outputs)
so the proofs are about the *deployed* code, not a Lean re-model that could drift.

---

*Companion artifacts:* `NATIVE_STWO_STATISTICAL_ZK_PROOF_SKETCH.md` (the candidate ZK argument, App. B as
implemented), `NATIVE_STWO_STATISTICAL_ZK_HABOCK_PACKAGE.md` (the review package). This plan is the
audit/attack scaffolding those two feed into. CANDIDATE until G1–G5 are closed.
