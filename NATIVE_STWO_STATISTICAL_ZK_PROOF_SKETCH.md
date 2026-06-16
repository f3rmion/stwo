# Statistical Zero-Knowledge for the S-two Circle STARK — A Worked Proof Sketch

**Status: CANDIDATE argument for educational use and cryptographic review.** This is our own
attempt to prove the masking construction hides the witness. It is NOT a certified-secure proof: ZK
failures are silent (a construction can verify, pass two-witness tests, and still leak), so the
guarantee is a cryptographer's review of *this argument*, not the existence of the argument or any
test. Two places below are marked **[GAP]** — they are the steps we cannot close ourselves.

The aim is pedagogical: to show *what a statistical-ZK proof for this construction actually is*, so
the construction, the dimension formulas, and the review questions all become concrete.

---

## 0. What "does not leak" means (the definition we must hit)

A public-coin argument is **statistical honest-verifier zero-knowledge (HVZK)** with error `ε` if there
is a probabilistic polynomial-time **simulator** `S` that, given only the *public* statement `x` (and
the public parameters), outputs a full transcript whose distribution is within statistical distance
`ε` of the real prover's transcript distribution on `(x, w)`, for every private witness `w`:

```
  Δ( S(x) ,  View_V⟨P(x,w), V⟩ )  ≤  ε       for all w.
```

Intuition: if a simulator who never saw `w` can produce indistinguishable transcripts, the transcript
carries `≤ ε` worth of information about `w`. Our target is `ε ≤ 2⁻¹⁰⁰`. "Prove it does not leak" =
"exhibit `S` and bound `Δ`." Everything below builds `S` and bounds `Δ`.

(HVZK suffices because Fiat–Shamir makes the verifier public-coin; the challenges are deterministic
functions of the transcript via the random oracle.)

## 1. Setting and notation

- `F_q = M31`, `q = 2³¹−1`. Extension `F = QM31`, `e = [F : F_q] = 4`, so `|F| = q⁴ ≈ 2¹²⁴`.
- Trace domain `H ⊂ C(F_q)` a canonic coset, `|H| = 2ⁿ`. Evaluation domain `D ⊂ C(F_q)`,
  `|D| = 2ⁿ⁺ᵝ`, `D ∩ H = ∅`. Both are conjugation-closed: `p = (x, y) ∈ S ⟹ p̄ = (x, −y) ∈ S`.
- Witness columns `w₁,…,w_M` in the circle-FFT space `L_n'(F_q)` (dimension `2ⁿ`, base-field coeffs).
- `v_H` = vanishing polynomial of `H`; `v_H(p) ≠ 0` exactly when `p ∉ H`.
- OODS point `ζ ∈ C(F)`, off-domain. Transition constraints also use the shift `ζ·g`. `n_F` = number of
  OODS sample points charged per column (e.g. `{ζ}` or `{ζ, ζg}`).
- FRI: `n_D` query positions `x₁,…,x_{n_D} ∈ D`.

A key circle fact used throughout: a **base-field** polynomial `f` satisfies `f(p̄) = conj(f(p))`. So an
opening of `f` at `ζ` (a full `F`-value, `e = 4` base coordinates) already *determines* `f(ζ̄)`; the
conjugate point contributes no independent information. This is why each OODS opening is charged as `e`
base-field functionals, not `2e`.

## 2. The construction under analysis

**Layer 1 (columns).** Replace each `wᵢ` by `ŵᵢ = wᵢ + v_H · rᵢ`, where `rᵢ ∈ L(F_q)` is uniform with
`h_col` free base-field coefficients. Since `v_H ≡ 0` on `H`, `ŵᵢ = wᵢ` on `H` (the AIR is unchanged);
off `H`, `ŵᵢ(p) = wᵢ(p) + v_H(p)·rᵢ(p)` with `v_H(p) ≠ 0`.

**Layer 2 (composition).** Let `N = Σ_k αᵏ C_k(ŵ)` be the constraint numerator (vanishes on `H`) and
`q = N / v_H` the composition quotient. S-two commits `q` by a degree-reducing split into two halves,
`q = q₀ + π · q₁` where `π(p) := (the x of p doubled n−2 times)` is the public split multiplier, and
commits `q₀, q₁` *separately*. Sample an independent uniform secure polynomial `t` (`h_t` free
coefficients per coordinate) and commit `q' = q + t`, i.e. the masked split `q'₀ = q₀ + t₀`,
`q'₁ = q₁ + t₁`. **`t` is committed UNSPLIT**: the verifier obtains only the combined `t(p)`, never
`t₀(p), t₁(p)`. The OODS check becomes `q'(ζ) − t(ζ) = N(ζ)/v_H(ζ)`.

**Layer 0 (Merkle).** Leaves are salted so a revealed authentication path is independent of unopened
leaves. (Standard hiding-Merkle; assumed throughout as Lemma 0.)

## 3. The verifier's view (everything we must simulate)

1. **Commitments**: Merkle roots for `{ŵᵢ}`, for `{q'₀, q'₁}` and `t`, for each FRI layer, and the
   final-layer polynomial.
2. **Challenges** (deterministic from the transcript): `α`, `ζ`, FRI folding challenges, query
   positions `{x_j}`.
3. **Openings**:
   - column OODS: `ŵᵢ(ζ), ŵᵢ(ζg) ∈ F`;
   - column queries: `ŵᵢ(x_j) ∈ F_q`;
   - composition: `q'₀(p), q'₁(p)` and `t(p)` at `p ∈ {ζ} ∪ {x_j}`;
   - FRI fold openings across layers and the final layer;
   - Merkle authentication paths for all the above.

## 4. Proof strategy

Build `S` and bound `Δ` by a hybrid argument over four lemmas: Merkle paths reveal nothing (L0),
column openings are uniform (L1), composition chunk openings are uniform given the columns (L2), and
FRI/final-layer are deterministic functions of those (L3). Then `S` samples uniform openings subject to
exactly the linear relations the verifier checks, and `Δ` is the sum of the per-lemma errors.

## 5. Lemma 0 (Merkle hiding)

With salted leaves, the joint distribution of (roots, authentication paths) for the opened positions is
simulatable independently of the unopened leaf values, with error `ε_M` negligible in the hash security
parameter. `S` commits to random salted leaves and produces consistent paths. *(Standard; not the novel
part.)*

## 6. Lemma 1 (column hiding) — the heart

**Claim.** Fix a masked column `ŵ = w + v_H·r`. The joint distribution of its revealed openings
`(ŵ(ζ), ŵ(ζg), ŵ(x₁),…,ŵ(x_{n_D}))` is **uniform** over `F^{n_F} × F_q^{n_D}` and independent of `w`,
provided `h_col ≥ e·n_F + n_D` **and** the evaluation map below has full rank.

**Derivation.** Each revealed value is
```
  ŵ(p) = w(p) + v_H(p) · r(p),     v_H(p) ≠ 0  for every revealed p.
```
Write `r(p) = Σ_{k<h_col} ρ_k · b_k(p)`, where `ρ = (ρ_k) ∈ F_q^{h_col}` are `r`'s free coefficients and
`b_k` are the FFT-basis functions. Stacking the revealed points and expanding each `F`-valued OODS
opening into its `e` base-field coordinates (via any `F_q`-basis of `F`), the revealed vector is
```
  open(ŵ) = open(w) + diag(v_H(p)) · E · ρ ,
```
where `E` is the `(e·n_F + n_D) × h_col` **evaluation matrix** of the randomizer basis at the revealed
points (OODS rows in `F`-coordinates, query rows in `F_q`). The diagonal `v_H(p)` factors are nonzero,
so they do not change the rank.

`ρ` is uniform on `F_q^{h_col}`. Therefore `open(ŵ)` is uniform on the target space (and independent of
`open(w)`) **iff the linear map `ρ ↦ E·ρ` is surjective**, i.e. `E` has full row rank `e·n_F + n_D`.
That forces `h_col ≥ e·n_F + n_D` (the dimension budget) and the rank condition on `E`.

`S` therefore samples each column's openings uniformly from `F^{n_F} × F_q^{n_D}`, except where the
*public* statement pins a value (e.g. a public boundary opening), which `S` sets to the public value —
those coordinates are not free in the real transcript either.

**Genericity / the `ε` term.** `det` of any maximal minor of `E` is a polynomial in the coordinates of
the random `ζ` and the random query positions. By Schwartz–Zippel, it is nonzero except with
probability `≤ deg / |F|` over the challenges, contributing a term `ε_col ≤ poly(2ⁿ, n_D) / |F|` to the
distance. With `|F| ≈ 2¹²⁴`, this is comfortably below `2⁻¹⁰⁰` for realistic sizes — *provided the minor
is not identically zero*, which is the rank condition.

**[GAP A] (= proposal Ask #3).** That `E` is *not identically rank-deficient* on the circle must be
proved, accounting for the conjugate-pair structure `f(p̄) = conj(f(p))`. On the circle, basis-function
evaluations at a point and its conjugate are related, so the relevant Vandermonde-type minor could
vanish identically for some admissible opening configuration. Proving it does not (or characterizing the
admissible sets where it holds) is the part we cannot close ourselves.

## 7. Lemma 2 (composition chunk hiding via the unsplit `t`)

This is the step that motivates committing `t` unsplit. Work at a single revealed point `p` with public
split multiplier `π = π(p)`.

The witness-dependent unknowns are the *separate* chunk values `q₀(p), q₁(p)`. They are constrained only
by the combination the verifier can pin:
```
  q(p) = q₀(p) + π · q₁(p)      (pinned: q(p) = N(p)/v_H(p) is a function of the column openings,
                                 already uniform/simulated by Lemma 1).
```
So there is exactly **one free witness DOF** at `p`: parametrize `q₀(p) = a`, then `q₁(p) = (q(p) − a)/π`.
This `a` is the residual leak that Layer-1 masking does *not* remove (it is internal to the separate
chunk commitments — the "decomposition pitfall").

The verifier reveals `q'₀(p) = a + t₀(p)`, `q'₁(p) = (q(p)−a)/π + t₁(p)`, and the **combined**
`t(p) = t₀(p) + π·t₁(p)`. Treat `(a, t₀(p), t₁(p))` as unknowns; the verifier's three observations give:
```
  (i)   q'₀(p)      = a + t₀(p)
  (ii)  π·q'₁(p)    = (q(p) − a) + π·t₁(p)
  (iii) t(p)        = t₀(p) + π·t₁(p)
```
Add (i) and (ii): `q'₀(p) + π·q'₁(p) = q(p) + t₀(p) + π·t₁(p) = q(p) + t(p)`. This is exactly relation
(iii) substituted — i.e. **(iii) is linearly dependent on (i)+(ii)**. So the system has three unknowns
and only **two independent equations**: a one-dimensional solution family parametrized by `a`. For every
value of `a`, consistent `t₀(p) = q'₀(p) − a` and `t₁(p) = (π·q'₁(p) − q(p) + a)/π` exist. Hence the
observed openings are *identically consistent with every `a`* — **`a` is information-theoretically
hidden at `p`**, provided `t₀(p), t₁(p)` are free (uniform) there.

Had `t` been committed **split**, the verifier would also see `t₀(p), t₁(p)` directly; then (i) gives
`a = q'₀(p) − t₀(p)` immediately — the mask collapses. This is the precise reason `t` must be unsplit.

**Joint version + dimension.** Across all revealed points `p ∈ {ζ} ∪ {x_j}`, the freedoms `t₀(p), t₁(p)`
must be *jointly* uniform conditioned on the pinned combinations `t(p)`. This is again a full-rank
condition on the evaluation map of `t`'s coefficient space onto the per-point "split-direction"
functionals; it requires `h_t` large enough to cover them — conservatively `h_t ≳ d·(e·n_F + n_D)` with
`d = 2` chunks. `S` samples `t(p)` uniform, samples the per-point chunk DOF uniform, and sets
`q'₀(p), q'₁(p)` consistent with `q'(p) = q(p) + t(p)`.

**[GAP B] (= proposal Ask #2).** That this *independent* `t` suffices for the **statistical** target —
rather than the perfect-ZK quotient-chunk *dependent* correction of Haböck–Kindi §4 — is the
highest-value claim to confirm. Our equations show single-point hiding cleanly; the joint full-rank
bound over all revealed points (and its `ε`) is the part we cannot fully close.

> **As implemented:** the wired check is `q'(ζ)_eff − t(2ζ)`, not the single-point `q'(ζ) − t(ζ)`
> framed above. See **B.7** for Lemma 2 re-derived in the observed quantities
> `{q'_left(ζ), q'_right(ζ), t(2ζ)}`; the cancellation is unchanged.

## 8. Lemma 3 (FRI folds and final layer add nothing)

Each FRI fold value is a fixed `F`-linear combination (with public folding challenges) of two values of
the layer below at conjugate positions; the DEEP quotient that seeds FRI is a public rational
combination of the column/composition/`t` openings at the query points. All of those are already
uniform/simulated (L1, L2). A deterministic linear image of simulated values is simulated with no extra
error, and the final-layer polynomial is determined by them. `S` computes folds and final layer from the
sampled openings. Contribution to `Δ`: `0` beyond the rank events already charged.

## 9. The simulator `S(x)`, assembled

1. Sample salted random leaves; publish their Merkle roots (L0). Derive `α, ζ, {x_j}`, fold challenges
   by Fiat–Shamir.
2. **Columns:** sample `ŵᵢ(ζ), ŵᵢ(ζg)` uniform in `F`, `ŵᵢ(x_j)` uniform in `F_q`; overwrite any
   publicly pinned coordinate with its public value (L1).
3. **Composition:** compute `q(p) = N(p)/v_H(p)` from the simulated column openings (deterministic);
   sample `t(p)` uniform and the chunk split DOF uniform; set `q'₀(p), q'₁(p)` consistent with
   `q'(p) = q(p) + t(p)` (L2).
4. **FRI:** compute fold openings and the final layer from the simulated openings (L3).
5. Produce Merkle authentication paths consistent with the sampled leaves (L0).

By construction every verifier check (Merkle, OODS `q'(ζ) − t(ζ) = N(ζ)/v_H(ζ)`, FRI consistency) holds,
and each opening matches the real distribution by L0–L3.

## 10. The distance bound

```
  Δ( S(x), real )  ≤  ε_M  +  ε_col  +  ε_comp
                    ≤  ε_M  +  poly(2ⁿ, n_D, n_F) / |F|        (≤ 2⁻¹⁰⁰ for chosen params)
```
where `ε_col, ε_comp` are the Schwartz–Zippel rank-failure probabilities of Lemmas 1 and 2 over the
random challenges, **conditional on [GAP A]/[GAP B] holding** (the relevant minors not vanishing
identically). The dimension budget that makes the ranks achievable is
```
  h_col ≥ e·n_F + n_D            (per column)
  h_t   ≳ d·(e·n_F + n_D),  d = 2 (composition randomizer)
```

## 11. What we proved vs. what remains

**Proved here (modulo standard hiding-Merkle):** the *structure* of the simulator; that single-point
column and chunk openings are uniform and witness-independent given the dimension budget; the precise
reason `t` must be unsplit; the shape of the distance bound.

**Not closed by us — the two [GAP]s, which are exactly the cryptographer-review questions:**
- **[GAP A]** the circle-FFT evaluation map is not identically rank-deficient at admissible OODS/query
  sets, accounting for conjugate pairs (Ask #3);
- **[GAP B]** the *joint* full-rank bound for the independent `t` suffices for the statistical target,
  so the §4 dependent correction is not needed (Ask #2).

These are why the construction is shared as a proposal: the simulator and the dimension formulas are
ours to write; the two rank theorems and the final `ε` are a cryptographer's to certify. A **numerical
rank check** of `E` (and the `t` map) at the actual deployed points turns [GAP A]/[GAP B] into computed
facts for specific parameters — strong, falsifying evidence, but not the general theorem.

---

### References
- Haböck, Kindi, *A note on adding zero-knowledge to STARKs*, ePrint 2024/1037 (§2 masking, §3
  decomposition pitfall, §4 Lagrange/quotient correction, App. A permutation arguments).
- Haböck, Levit, Papini, *Circle STARKs*, ePrint 2024/278.
- Carmon, Goldberg, Haböck, Lerer, Lesokhin, *S-two Whitepaper*, ePrint 2026/532 (soundness only).

---

## Appendix B — Adversarial review: corrections, computational evidence, residual

A multi-reviewer adversarial pass (independent proof attempts for GAP A and GAP B, an adversary
tasked to break them, a numerical rank check, and a tie-breaker) refined this sketch. No fundamental
break of the construction-as-designed was found. The corrections below supersede the looser statements
in §6–§10 where they conflict. **This remains a candidate; certification still requires a cryptographer.**

### B.0 Scope: two components are specified but NOT yet built

- **Layer 0 (hiding/salted Merkle)** is assumed in §5 but is not implemented. The full construction
  requires it (auth paths otherwise leak through sibling hashes of unopened leaves).
- **The composition wiring is now built** behind the `statistical-zk` feature (`prove_zk`/`verify_zk`):
  `q' = q + t` is committed (chunks split), `t` is committed unsplit as a separate tree, and the check
  is enforced. NOTE the implemented check is `q'(ζ)_eff − t(2ζ)` evaluated at the lifted effective
  point, NOT the single-point `q'(ζ) − t(ζ)` of §2/§7 — `t` is opened at
  `2ζ = ζ.repeated_double(COMPOSITION_LOG_SPLIT)` so it lands on the same effective point the split
  chunks fold to. Lemma 2 is re-derived in the observed quantities
  `{q'_left(ζ), q'_right(ζ), t(2ζ)}` in **B.7** (the cancellation still holds — combined `t` is the
  only `t`-functional revealed — the single-point *quantities* of §2/§7 are inaccurate as written, the
  cancellation conclusion unchanged).
- **Layer-1 base-trace masking is now wired** behind the `statistical-zk` feature: base-trace columns
  are committed as `ŵ = w + v_H·r` (§6, Lemma 1), so their off-domain/query openings are randomized
  while the AIR is unchanged on `H`. Because the constraint framework ties a single log size to the
  vanishing domain, the committed-column size, and the composition size, a masked component decouples
  them: `eval.log_size()` stays `2ⁿ` (the vanishing/constraint domain), while the committed trace and
  the composition grow to the masked geometry, and the OODS-point vanishing degree is reduced by the
  masking enlargement so it equals `v_H` in the trace's lifted opening frame. The public preprocessed
  columns are LIFTED (not masked). The runtime leakage budget (`check_leakage_budget`) is invoked
  fail-closed (still a dimension check, not derived from real opening counts). CANDIDATE — mechanism
  only, no leakage certificate.
- **Nonzero-offset (transition) AIRs and LogUp interaction columns are now also wired.** Masked columns
  are committed `m − n` log sizes above the constraint domain and opened in that lifted frame, so the
  mask-offset translation steps by the constraint (trace) domain coset seen in the lifted frame —
  degree `max_log_degree_bound − (m − n)`, the same reduction as the vanishing — instead of the
  composition coset. (The prover-side offset stepping already keys off the trace log size `n`, so it is
  unchanged.) This lets transition constraints (shifted-row reads) and the LogUp cumulative-sum columns
  be masked. Validated end to end: WideFib (no LogUp, offset-0), and PLONK with real LogUp — base trace
  AND interaction columns committed as `ŵ = w + v_H·r` (the cumulative-sum read at current/previous
  row), masked `prove_zk`/`verify_zk` accept, and the trace + interaction openings randomize under the
  mask. CANDIDATE — mechanism only.
- **Layer 0 (salted hiding Merkle) is now wired** behind the feature for every witness-bearing tree —
  trace, interaction, composition-chunk and `t`. Each carries a leaf-size random salt column (no OODS
  sample point, unread by any constraint, so invisible to FRI) whose values enter every leaf hash,
  making those trees' authentication-path sibling hashes hiding; the public preprocessed tree is not
  salted. The salt is committed at leaf size so it is not replicated across leaves. Combined with
  Layer-1 (openings randomized) the trace is **mechanism-complete witness-hidden** (openings masked AND
  auth paths hiding). The salt is a low-degree blind (CANDIDATE, same caveat as the other randomizers).
- **Still NOT built:** a leakage budget derived from real OODS/FRI opening counts (currently a
  conservative caller-supplied dimension); and the cryptographer's no-leak certificate (the joint
  full-rank / Vandermonde blinding bound, §6 [GAP A] / §7 [GAP B]).

### B.1 The split multiplier never vanishes on the query domain (the §7 π-edge is closed)

The verifier's split multiplier is `M(p) = p.repeated_double(max_log_degree_bound − 1).x`, and
composition query points live on `CanonicCoset(max_log_degree_bound + log_blowup_factor)`. On a canonic
coset of log size `L`, `M(p) = 0` happens iff the doubling exponent equals `L − 1`. Here the exponent is
`max_log_degree_bound − 1` and `L = max_log_degree_bound + log_blowup_factor`, so `M = 0` would require
`log_blowup_factor = 0`. Since the blow-up factor is always `≥ 1`, **`M(p) ≠ 0` at every admissible
query point** (proved closed-form, confirmed by exhaustive scan for `n = 4..7`). Hence Lemma 2's
division by `M` is safe and the singular branch is never reached. (An earlier worry that `M = 0` occurs
for a constant fraction of query points dropped the blow-up factor and was incorrect.)

### B.2 Two conjugations — the OODS charge is `e`, but query conjugates do NOT collapse

There are two distinct conjugations, and only one yields `f(p̄) = conj(f(p))`:
- **Field/Frobenius conjugate**: gives the relation, so the Frobenius-conjugate opening is an
  `F_q`-linear image of the original — its rows collapse, and each OODS opening is correctly charged as
  `e = 4` base functionals (not `2e`). *Confirmed numerically: rank stays 4.*
- **Circle/geometric conjugate `(x, −y)`**: a different point; its opening is independent. *Confirmed
  numerically: rank rises.*

Consequence (correcting the GAP-A "[R1] count distinct functionals" remark): geometric-conjugate
**query** points do not coincide — their rows are independent (rank grows `1 → 2`). The only genuine
query-rank collapse is at **self-conjugate points `y = 0`**, which canonic domains exclude (and OODS
enforces `ζ.y ≠ conj(ζ.y)`). So the relevant admissibility condition is "no `y = 0` query point,"
not "no conjugate-pair query."

### B.3 Corrected leakage budget for `t` (secure column ⇒ charge `e` per opening)

`t` is a *secure* polynomial: a query opening exposes all `e = 4` base coordinates, so query openings of
`t` are charged `e·n_D`, not `n_D`; and `t` carries `4·h_t` base-field DOF (h_t per coordinate). The
composition is OODS-sampled at `ζ` only, so `n_F^comp = 1`. Two requirements:
- **reconstruction-resistance** (the decisive one): the verifier's `t`-openings must be strictly fewer
  than `t`'s DOF, `4·h_t > e·(n_F^comp + n_D)`, else the verifier interpolates `t`, computes the public
  split `(t_0, t_1) = split(t)`, and strips the mask `q_0 = q'_0 − t_0`;
- **joint hiding**: `4·h_t ≥ dim R + dim S` where `R` = revealed `t`-functionals and `S` = the per-point
  split-direction freedoms.

The exact inequality must be **derived from real opening counts and enforced fail-closed** at wiring
time (the existing `check_leakage_budget` is not yet called on `t`). The §3/§7 formula
`h_t ≳ d·(e·n_F + n_D)` is safe but loose (it over-counts by mixing per-coordinate vs total and using
`n_F = 2`).

### B.4 LogUp division of labor

`t` covers the LogUp constraint's contribution to the **composition quotient** (it is just more
`C_k` in the same `N`). LogUp **auxiliary columns** (running-sum / fraction) are covered by Layer 1
(they must be `ŵ = w + v_H·r` masked), not by `t`. If LogUp is discharged via a **GKR/sumcheck** path
instead of in-composition constraints, that transcript is a **separate ZK surface** untouched by `t` or
column masking and is outside this argument.

### B.5 Computational evidence (numerical rank check)

`crates/stwo/src/prover/statistical_zk_rank_check.rs` computes exact base-field ranks at concrete points,
with negative controls (it can fail). At the tested parameters it establishes **non-identical
degeneracy**:
- Lemma 1: `E` reaches full row rank `e·n_F + n_D` at the budget; under-provisioning by one fails.
- Lemma 2: `t` is under-determined at the conservative budget (positive coefficient nullspace);
  over-opening `t` makes it reconstructible (negative control) — confirming the reconstruction defense.
- The conjugate counting (B.2) and `M ≠ 0` on the real query domain (B.1).

These are **computed facts for specific parameters and points** — evidence that the maps are not
identically degenerate. They are **not** the genericity theorem over random challenges, nor all
admissible configurations, nor the statistical-distance bound `ε`.

### B.6 Updated residual for cryptographer review

1. The **general non-degeneracy theorems** for `E` (GAP A) and the `R ⊕ S` map (GAP B): full rank at
   *all* admissible OODS/query configurations, with the Schwartz–Zippel `ε` over the random challenges
   (note query positions are uniform over the finite domain `D`, not over `F` — the query term is a
   distinctness/non-`y=0` argument, not a field-size term).
2. The **corrected, enforced budget** of B.3 (derive `h_t`, `h_col` from real counts; fail-closed).
3. Build **Layer 0** (hiding Merkle) and the **prove/verify wiring**; confirm the **LogUp path**
   (in-composition vs GKR).

Overall: the adversarial pass moved GAP A and GAP B to **PROVED-MODULO their non-degeneracy
assumptions, with those assumptions numerically confirmed at tested parameters and no fundamental break
found** — a strengthened candidate, still pending the cryptographer's general theorems and `ε`.

### B.7 Lemma 2, re-derived in the implemented quantities `{q'_left(ζ), q'_right(ζ), t(2ζ)}`

§7 derived chunk-hiding in idealized single-point quantities `{q'₀(p), q'₁(p), t(p)}`. The wired path
(`prove_zk`/`verify_zk`, `statistical-zk` feature) reveals a slightly different set, because the masked
composition is committed **split** while `t` is committed **unsplit, one log size taller**. This
subsection redoes Lemma 2 in exactly the quantities the verifier sees. The cancellation — the whole
reason `t` is unsplit — survives unchanged; only the framing moves.

**What the verifier actually observes (per revealed point `ζ`).**
- the two split-chunk openings `q'_left(ζ), q'_right(ζ)` of the masked composition (committed at
  `split_composition_log_degree_bound = composition_log_degree_bound − COMPOSITION_LOG_SPLIT`),
  reconstructed into the effective value
  `q'(ζ)_eff = q'_left(ζ) + π·q'_right(ζ)`, with public split multiplier
  `π = ζ.repeated_double(max_log_degree_bound − 1).x` (`≠ 0` on the query domain by B.1) —
  computed by `extract_composition_oods_eval_zk` (`core/proof.rs`);
- the single **combined** randomizer opening `t(2ζ)`, where `2ζ := ζ.repeated_double(COMPOSITION_LOG_SPLIT)`
  — `extract_t_oods_eval`. `t` is committed unsplit at the full composition log size (one above the
  chunks), so opening it at the doubled point returns its value at the *same effective point* the chunks
  fold to. The verifier never sees `t_left, t_right`.

The verifier check is `q'(ζ)_eff − t(2ζ) = N(ζ)/v_H(ζ)` (`core/verifier.rs` DEEP-ALI check; mirrored as
the prover-side sanity check in `prove_zk`).

**The mask is linear through the split.** `prove_zk` forms `q' = q + t` on the full (log size
`s = composition_log_degree_bound`) coefficient vectors and only *then* splits. Splitting is
`F`-linear, so
```
  q'_left = q_left + t_left,   q'_right = q_right + t_right,   (t_left, t_right) = split(t).
```
Opening the unsplit `t` at `2ζ` returns precisely the chunk reconstruction of its own halves,
```
  t(2ζ) = t_left(ζ) + π·t_right(ζ),
```
the identity that makes the check well-formed. The *same* multiplier `π` is valid for both the chunks
and `t` because the unsplit `t` is committed at exactly the chunks' parent (lifted) log size and
`2ζ = ζ.repeated_double(COMPOSITION_LOG_SPLIT)` is the same single fold the split chunks undergo;
opening `t` there is identically `t`'s own chunk-reconstruction at `ζ`. (The prover's sanity check
passing, and `verify_zk` accepting, on the toy `a·b=c` AIR and on PLONK with real LogUp, are exactly
this identity holding end to end.)

**The single free witness DOF.** As in §7, the only witness-dependent freedom not pinned by the trace
openings is the split direction. Lemma 1 (via the accepted check) pins the unmasked reconstruction
`Q(ζ) := q_left(ζ) + π·q_right(ζ) = N(ζ)/v_H(ζ)`. Parametrize `a := q_left(ζ)`, so
`q_right(ζ) = (Q(ζ) − a)/π`. The observed quantities expand to
```
  (i)    q'_left(ζ)    = a + t_left(ζ)
  (ii)   π·q'_right(ζ) = (Q(ζ) − a) + π·t_right(ζ)
  (iii)  t(2ζ)         = t_left(ζ) + π·t_right(ζ)
```
Adding (i)+(ii): `q'(ζ)_eff = Q(ζ) + t(2ζ)` — i.e. (iii) is exactly the combination already implied by
(i)+(ii): **linearly dependent**. Three observed quantities, two independent equations in the unknowns
`{a, t_left(ζ), t_right(ζ)}` ⇒ a one-parameter solution family in `a`. For every `a` there exist
consistent `t_left(ζ) = q'_left(ζ) − a` and `t_right(ζ) = q'_right(ζ) − (Q(ζ) − a)/π`. Hence `a` is
**information-theoretically hidden at `ζ`**, provided `t_left(ζ), t_right(ζ)` are free (uniform) — i.e.
provided `t` carries the budget of B.3.

This is identical to §7 under the substitution `t₀(p) ↦ t_left(ζ)`, `t₁(p) ↦ t_right(ζ)`,
`t(p) ↦ t(2ζ)`. The doubled opening point is bookkeeping for the one-log-taller unsplit `t` tree; it
adds **no** new verifier-visible `t`-functional, so the count is unchanged. Had `t` been committed
split, the verifier would read `t_left(ζ)` directly and recover `a = q'_left(ζ) − t_left(ζ)` — the mask
collapses, exactly the §7 reason for unsplit `t`.

**Budget (as implemented, per B.3).** `t` is a *secure* polynomial (`e = 4` base coordinates exposed
per query opening), OODS-sampled at `ζ` only (`n_F^comp = 1`). Reconstruction-resistance is decisive:
```
  4·h_t > e·(n_F^comp + n_D)   (else the verifier interpolates t, splits it publicly, strips the mask)
  4·h_t ≥ dim R + dim S        (joint hiding: R = revealed t-functionals, S = per-point split freedoms)
```
The §3/§7 figure `h_t ≳ d·(e·n_F + n_D)` is safe but loose. This budget is **not yet enforced** in
`prove_zk` (`check_leakage_budget` is not called on `t`) — workstream 4.

**Scope (no over-claim).** This re-derivation establishes only **single-point** chunk-hiding in the
implemented quantities, and that the `2ζ` opening preserves the §7 cancellation. The **joint** statement
over all revealed points `{ζ} ∪ {x_j}` — that `t_left(ζ), t_right(ζ)` are jointly uniform under the
pinned combinations, with its Schwartz–Zippel `ε` — remains **[GAP B]**, unchanged. The numerical rank
check (B.5) confirms non-identical degeneracy at tested parameters only, not the general theorem. The
wired path masks the **composition only**: Layer-1 trace masking and Layer-0 salted Merkle are not
built, so this path is **not yet witness-hiding on the trace**. Candidate until the cryptographer
certifies GAP B and the budget is enforced.
