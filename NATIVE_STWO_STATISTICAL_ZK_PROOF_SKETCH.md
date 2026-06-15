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
