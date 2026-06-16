//! Numerical rank checks for the witness-masking construction.
//!
//! These are FALSIFIABLE computational checks, not proofs. They evaluate the
//! linear maps that the masking argument requires to have a specified rank, at
//! concrete circle points, and compute the EXACT rank over the base field by
//! Gaussian elimination. They are wired with negative controls so that a broken
//! assumption FAILS the test rather than passing silently.
//!
//! What a passing run establishes: at the TESTED parameters and points, the
//! evaluation maps are NOT identically degenerate — the column-randomizer map is
//! surjective onto the opening space when the randomizer budget covers it, and
//! the composition mask is under-determined by the revealed openings (so the
//! masked chunks are not reconstructible). What it does NOT establish: the
//! general theorem over all admissible point configurations, nor the statistical
//! distance bound. Silent ZK failures mean only a cryptographer's review of the
//! argument certifies privacy; these numbers are evidence, not certification.

#![cfg(all(test, feature = "statistical-zk"))]

use num_traits::{One, Zero};

use crate::core::circle::CirclePoint;
use crate::core::fields::m31::BaseField;
use crate::core::fields::qm31::SecureField;
use crate::core::fields::ComplexConjugate;
use crate::core::poly::circle::CanonicCoset;
use crate::prover::backend::cpu::{CpuBackend, CpuCirclePoly};
use crate::prover::poly::circle::CircleCoefficients;

/// Exact rank of a base-field matrix by Gaussian elimination over M31.
///
/// Operates on a row-major `Vec<Vec<BaseField>>`. Uses field inverse for pivot
/// normalization, so the result is exact (no rounding). Returns the number of
/// pivots, i.e. the row rank, which equals the column rank.
fn m31_matrix_rank(rows: &[Vec<BaseField>]) -> usize {
    if rows.is_empty() {
        return 0;
    }
    let n_cols = rows[0].len();
    if n_cols == 0 {
        return 0;
    }
    // Work on a mutable copy.
    let mut mat: Vec<Vec<BaseField>> = rows.to_vec();
    let n_rows = mat.len();
    debug_assert!(mat.iter().all(|r| r.len() == n_cols));

    let mut rank = 0usize;
    let mut pivot_row = 0usize;
    for col in 0..n_cols {
        if pivot_row >= n_rows {
            break;
        }
        // Find a nonzero entry in this column at or below `pivot_row`.
        let mut sel = None;
        for r in pivot_row..n_rows {
            if !mat[r][col].is_zero() {
                sel = Some(r);
                break;
            }
        }
        let Some(sel) = sel else {
            continue; // Column is all zero below pivot; skip (no rank gained).
        };
        mat.swap(pivot_row, sel);

        // Normalize the pivot row so the pivot becomes 1.
        let inv = mat[pivot_row][col].inverse();
        for c in col..n_cols {
            mat[pivot_row][c] = mat[pivot_row][c] * inv;
        }

        // Eliminate this column from every other row.
        for r in 0..n_rows {
            if r == pivot_row {
                continue;
            }
            let factor = mat[r][col];
            if factor.is_zero() {
                continue;
            }
            for c in col..n_cols {
                let sub = factor * mat[pivot_row][c];
                mat[r][c] = mat[r][c] - sub;
            }
        }

        rank += 1;
        pivot_row += 1;
    }
    rank
}

/// Evaluates basis function `b_k` of a length-`coeff_count` FFT-basis polynomial
/// at `point`.
///
/// `b_k` is realized by a `CircleCoefficients` carrying a unit coefficient in
/// slot `k` and zeros elsewhere, then evaluated at `point`. Reading the basis
/// functions off `eval_at_point` this way is internal-ordering-agnostic: whatever
/// the FFT basis and its bit-reversal are, slot `k` selects exactly its basis
/// function.
fn basis_value_at(coeff_count: usize, k: usize, point: CirclePoint<SecureField>) -> SecureField {
    assert!(coeff_count.is_power_of_two());
    assert!(k < coeff_count);
    let coeffs: Vec<BaseField> = (0..coeff_count)
        .map(|i| if i == k { BaseField::one() } else { BaseField::zero() })
        .collect();
    let poly: CpuCirclePoly = CircleCoefficients::<CpuBackend>::new(coeffs);
    poly.eval_at_point(point)
}

/// Lifts a base-field circle point into the secure field.
fn lift(point: CirclePoint<BaseField>) -> CirclePoint<SecureField> {
    point.into_ef::<SecureField>()
}

/// Builds the column-randomizer evaluation matrix `E` for Lemma 1.
///
/// Rows: for each OODS point `ζ ∈ C(F)` (a secure point) we evaluate every
/// randomizer basis function and split the resulting `F`-value into its 4 base
/// coordinates — 4 rows per OODS point. For each query point `x_j ∈ D ⊂ C(F_q)`
/// (a base-field point) we take the single base coordinate — 1 row per query.
/// Columns: the `h_col` randomizer coefficient slots.
///
/// The returned row count is `4 * oods_points.len() + query_points.len()`.
fn build_column_eval_matrix(
    h_col: usize,
    oods_points: &[CirclePoint<SecureField>],
    query_points: &[CirclePoint<BaseField>],
) -> Vec<Vec<BaseField>> {
    let coeff_count = h_col.next_power_of_two().max(1);
    let mut rows: Vec<Vec<BaseField>> = Vec::new();

    // OODS rows: 4 base-field functionals per point.
    for &zeta in oods_points {
        let mut coord_rows: [Vec<BaseField>; 4] =
            [Vec::with_capacity(h_col), Vec::with_capacity(h_col), Vec::with_capacity(h_col), Vec::with_capacity(h_col)];
        for k in 0..h_col {
            let v = basis_value_at(coeff_count, k, zeta);
            let [a, b, c, d] = v.to_m31_array();
            coord_rows[0].push(a);
            coord_rows[1].push(b);
            coord_rows[2].push(c);
            coord_rows[3].push(d);
        }
        rows.extend(coord_rows);
    }

    // Query rows: 1 base-field functional per point.
    for &x in query_points {
        let p = lift(x);
        let mut row = Vec::with_capacity(h_col);
        for k in 0..h_col {
            let v = basis_value_at(coeff_count, k, p);
            // A base-field basis polynomial at a base-field point is base-valued;
            // coordinate 0 carries it, coords 1..4 are zero.
            let [a, b, c, d] = v.to_m31_array();
            debug_assert!(b.is_zero() && c.is_zero() && d.is_zero());
            row.push(a);
        }
        rows.push(row);
    }

    rows
}

/// Builds the t-map for Lemma 2: the linear map from `t`'s `4 * h_t` free
/// base-field coefficients to its revealed openings, expanded into base
/// coordinates.
///
/// `t` is an unsplit secure polynomial. Each of its 4 QM31-coordinate polynomials
/// carries `h_t` free base-field coefficients. A revealed opening `t(p)` is one
/// QM31 value (4 base coordinates) at every revealed point `p` (OODS and query
/// alike, since `t` is secure-valued everywhere).
///
/// Columns are ordered as `(coordinate j, slot k)` for `j in 0..4`, `k in 0..h_t`.
/// Rows are `4 * revealed_points.len()` base-field functionals.
fn build_t_map(h_t: usize, revealed_points: &[CirclePoint<SecureField>]) -> Vec<Vec<BaseField>> {
    let coeff_count = h_t.next_power_of_two().max(1);
    let n_cols = 4 * h_t;

    // For each (coordinate-poly index j, slot k), the unit vector `u_j` times the
    // scalar basis value `b_k(p)` gives a QM31 contribution; its 4 base coords are
    // the column entries for that point's 4 rows.
    //
    // u_0 = 1, u_1 = i, u_2 = u, u_3 = iu, in the QM31 representation.
    let unit_qm31: [SecureField; 4] = [
        SecureField::from_u32_unchecked(1, 0, 0, 0),
        SecureField::from_u32_unchecked(0, 1, 0, 0),
        SecureField::from_u32_unchecked(0, 0, 1, 0),
        SecureField::from_u32_unchecked(0, 0, 0, 1),
    ];

    let mut rows: Vec<Vec<BaseField>> = Vec::new();
    for &p in revealed_points {
        // Precompute b_k(p) for all slots once per point.
        let basis: Vec<SecureField> = (0..h_t).map(|k| basis_value_at(coeff_count, k, p)).collect();

        let mut coord_rows: [Vec<BaseField>; 4] = [
            Vec::with_capacity(n_cols),
            Vec::with_capacity(n_cols),
            Vec::with_capacity(n_cols),
            Vec::with_capacity(n_cols),
        ];
        for j in 0..4 {
            for k in 0..h_t {
                // Contribution of coefficient (j, k) to t(p): u_j * b_k(p).
                let contrib = unit_qm31[j] * basis[k];
                let [a, b, c, d] = contrib.to_m31_array();
                coord_rows[0].push(a);
                coord_rows[1].push(b);
                coord_rows[2].push(c);
                coord_rows[3].push(d);
            }
        }
        rows.extend(coord_rows);
    }
    rows
}

/// Off-domain OODS points used across the Lemma-1 / Lemma-2 checks.
///
/// `n_F = 2`: the pair `{ζ, ζg}`, where `g` is the trace subgroup generator. We
/// model `ζg = ζ + g` with `g` the (base-field) canonic step lifted to `F`.
fn oods_pair(trace_log_size: u32, zeta_index: u128) -> [CirclePoint<SecureField>; 2] {
    let zeta = CirclePoint::<SecureField>::get_point(zeta_index);
    let g = CanonicCoset::new(trace_log_size).step();
    let zeta_g = zeta + lift(g);
    [zeta, zeta_g]
}

#[cfg(test)]
mod tests {
    use super::*;

    // ----- Part A: rank routine sanity (with negative-direction checks). -----

    #[test]
    fn rank_identity_and_dependent_rows() {
        // Identity-like full-rank matrix.
        let id: Vec<Vec<BaseField>> = (0..3)
            .map(|r| {
                (0..3)
                    .map(|c| if r == c { BaseField::one() } else { BaseField::zero() })
                    .collect()
            })
            .collect();
        assert_eq!(m31_matrix_rank(&id), 3);

        // A matrix with a linearly dependent third row (row3 = row1 + row2).
        let dep = vec![
            vec![BaseField::from(1u32), BaseField::from(2u32), BaseField::from(3u32)],
            vec![BaseField::from(4u32), BaseField::from(5u32), BaseField::from(6u32)],
            vec![BaseField::from(5u32), BaseField::from(7u32), BaseField::from(9u32)],
        ];
        assert_eq!(m31_matrix_rank(&dep), 2);

        // Zero matrix has rank 0.
        let zero = vec![vec![BaseField::zero(); 4]; 3];
        assert_eq!(m31_matrix_rank(&zero), 0);

        // Wide matrix: rank bounded by rows.
        let wide = vec![
            vec![BaseField::from(1u32), BaseField::zero(), BaseField::from(7u32), BaseField::from(9u32)],
            vec![BaseField::zero(), BaseField::from(1u32), BaseField::from(2u32), BaseField::from(3u32)],
        ];
        assert_eq!(m31_matrix_rank(&wide), 2);
    }

    // ----- Part B: Lemma 1 column evaluation matrix E. -----

    #[test]
    fn lemma1_positive_full_rank_when_budget_covers() {
        // trace log n = 5; OODS {ζ, ζg}; some FRI queries on D.
        let trace_log_size = 5;
        let oods = oods_pair(trace_log_size, 1234567);
        let n_f = oods.len();

        // Query points: distinct, non-conjugate, drawn from the evaluation
        // domain D (blow-up factor 2 -> masked/eval log size 6).
        let d_domain = CanonicCoset::new(trace_log_size + 1).circle_domain();
        let query_points = vec![d_domain.at(1), d_domain.at(3), d_domain.at(5), d_domain.at(7)];
        let n_d = query_points.len();

        let rows = 4 * n_f + n_d; // e*n_F + n_D
        let h_col = rows; // budget exactly covers.

        let e = build_column_eval_matrix(h_col, &oods, &query_points);
        assert_eq!(e.len(), rows);
        let rank = m31_matrix_rank(&e);
        println!(
            "[Lemma1 POSITIVE] e*n_F+n_D = {rows}, h_col = {h_col}, rank(E) = {rank}"
        );
        assert_eq!(
            rank, rows,
            "E must reach full row rank e*n_F+n_D when h_col >= e*n_F+n_D"
        );

        // Over-provisioned budget keeps full row rank (rank capped by #rows).
        let h_col_big = rows + 5;
        let e_big = build_column_eval_matrix(h_col_big, &oods, &query_points);
        let rank_big = m31_matrix_rank(&e_big);
        println!("[Lemma1 POSITIVE] over-provisioned h_col = {h_col_big}, rank(E) = {rank_big}");
        assert_eq!(rank_big, rows);
    }

    #[test]
    fn lemma1_negative_underprovisioned_budget_cannot_cover() {
        // NEGATIVE CONTROL: with h_col < e*n_F + n_D the map cannot be surjective.
        let trace_log_size = 5;
        let oods = oods_pair(trace_log_size, 7654321);
        let n_f = oods.len();

        let d_domain = CanonicCoset::new(trace_log_size + 1).circle_domain();
        let query_points = vec![d_domain.at(1), d_domain.at(3), d_domain.at(5), d_domain.at(7)];
        let n_d = query_points.len();

        let target = 4 * n_f + n_d;
        let h_col = target - 1; // deliberately short by one.

        let e = build_column_eval_matrix(h_col, &oods, &query_points);
        let rank = m31_matrix_rank(&e);
        println!(
            "[Lemma1 NEGATIVE] target e*n_F+n_D = {target}, h_col = {h_col}, rank(E) = {rank}"
        );
        // The map is into a `target`-dimensional space but has at most `h_col`
        // columns: it CANNOT be surjective. This is the check FAILING by design.
        assert!(
            rank < target,
            "under-provisioned randomizer must NOT reach full opening rank"
        );
        // Moreover the columns are independent here, so rank == h_col: the limit
        // is the budget, not a degeneracy.
        assert_eq!(rank, h_col, "columns of E should be independent at these points");
    }

    #[test]
    fn lemma1_edge_oods_conjugate_counting() {
        // EDGE / the "distinct functionals counting" issue (GAP A). The sketch
        // charges each OODS opening as e=4 base functionals (not 2e) because a
        // base-field `f` satisfies `f(p^c) = conj(f(p))`. But there are TWO
        // distinct conjugations in play and only ONE produces that relation:
        //
        //   * circle conjugate  (x, -y):  flips only the y-coordinate.
        //   * field conjugate   complex_conjugate(p): the Frobenius of F that the
        //                       base-field-poly relation actually uses.
        //
        // This computation shows they behave OPPOSITELY at a generic OODS point,
        // which is precisely the counting subtlety a reviewer must get right.
        let zeta = CirclePoint::<SecureField>::get_point(424242);
        let zeta_circle_conj = zeta.conjugate(); // (x, -y)
        let zeta_field_conj = zeta.complex_conjugate(); // Frobenius of F

        // Budget large enough that it is never the binding constraint.
        let h_col = 16;

        let only_zeta = build_column_eval_matrix(h_col, &[zeta], &[]);
        let rank_zeta = m31_matrix_rank(&only_zeta);

        let with_circle = build_column_eval_matrix(h_col, &[zeta, zeta_circle_conj], &[]);
        let rank_circle = m31_matrix_rank(&with_circle);

        let with_field = build_column_eval_matrix(h_col, &[zeta, zeta_field_conj], &[]);
        let rank_field = m31_matrix_rank(&with_field);

        println!(
            "[Lemma1 EDGE/OODS] rank({{ζ}}) = {rank_zeta} (4 rows); \
             + circle-conj (x,-y): rank = {rank_circle} (8 rows); \
             + field-conj Frob(ζ): rank = {rank_field} (8 rows)"
        );

        // A single OODS point gives e = 4 independent functionals.
        assert_eq!(rank_zeta, 4, "a single OODS point yields e=4 functionals");

        // The CIRCLE conjugate (x,-y) is NOT a field automorphism: at a generic
        // secure ζ its 4 rows are INDEPENDENT, so rank rises to 8. A naive
        // "circle-conjugate opening is free" reading is therefore FALSE.
        assert_eq!(
            rank_circle, 8,
            "circle-conjugate OODS rows are independent at generic ζ (rank rises)"
        );

        // The FIELD conjugate (Frobenius) DOES give f(p^c)=conj(f(p)), so its 4
        // rows are F_q-linear images of ζ's rows: rank does NOT increase. THIS is
        // the conjugation the e-not-2e counting relies on.
        assert_eq!(
            rank_field, 4,
            "field-conjugate (Frobenius) OODS rows collapse: rank must not increase"
        );
    }

    #[test]
    fn lemma1_edge_conjugate_query_rows_are_distinct_not_collapsing() {
        // The conjugate COLLAPSE is an OODS (F-valued) phenomenon. For base-field
        // QUERY points x and x̄ we take only ONE base coordinate each, and those
        // rows are generally DISTINCT (they differ in the y-odd basis functions),
        // so the rank DOES increase. We document this explicitly: a naive "query
        // conjugates coincide" reading is FALSE at generic points.
        let trace_log_size = 5;
        let d_domain = CanonicCoset::new(trace_log_size + 1).circle_domain();
        let half = d_domain.size() / 2;
        // domain.at(i) and domain.at(i+half) are conjugates (see domain tests).
        let x = d_domain.at(1);
        let x_bar = d_domain.at(1 + half);
        assert_eq!(x_bar, x.conjugate(), "constructed a genuine conjugate pair");

        let h_col = 16;
        let single = build_column_eval_matrix(h_col, &[], &[x]);
        let pair = build_column_eval_matrix(h_col, &[], &[x, x_bar]);
        let rank_single = m31_matrix_rank(&single);
        let rank_pair = m31_matrix_rank(&pair);
        println!(
            "[Lemma1 EDGE/query-conjugate] rank({{x}}) = {rank_single}, \
             rank({{x,x̄}}) = {rank_pair} (distinct base rows -> rank grows)"
        );
        assert_eq!(rank_single, 1);
        assert_eq!(
            rank_pair, 2,
            "generic conjugate QUERY rows are independent; they do NOT collapse"
        );

        // The genuine self-conjugate degeneracy: a point with y = 0 equals its own
        // conjugate, so the two "conjugate" rows are literally identical and the
        // rank does not grow. We exhibit it via an order-2 point (x=-1, y=0).
        let self_conj = CirclePoint::<BaseField> {
            x: -BaseField::one(),
            y: BaseField::zero(),
        };
        assert_eq!(self_conj, self_conj.conjugate());
        let doubled = build_column_eval_matrix(h_col, &[], &[self_conj, self_conj]);
        let rank_doubled = m31_matrix_rank(&doubled);
        println!(
            "[Lemma1 EDGE/self-conjugate y=0] rank({{p,p}}) = {rank_doubled} \
             (identical rows -> no rank gain)"
        );
        assert_eq!(rank_doubled, 1, "identical rows add no rank");
    }

    // ----- Part C: Lemma 2 t-map / reconstruction. -----

    #[test]
    fn lemma2_t_is_underdetermined_at_budget() {
        // Realistic params: n_F = 2 (ζ, ζg); pick n_D so the conservative budget
        // h_t makes the revealed openings strictly fewer than t's coefficients.
        //
        // Revealed t openings = 4 * (n_F + n_D) base coords.
        // t coefficients      = 4 * h_t.
        // Conservative budget : h_t >= d*(e*n_F + n_D)/4, d = 2.
        let trace_log_size = 5;
        let oods = oods_pair(trace_log_size, 999983);
        let n_f = oods.len();

        let d_domain = CanonicCoset::new(trace_log_size + 1).circle_domain();
        // n_D small enough that 2*n_F > n_D, which makes the budget exceed the
        // reconstruction threshold (h_t > n_F + n_D).
        let query_points = vec![d_domain.at(1), d_domain.at(3)];
        let n_d = query_points.len();

        let e_n_f = 4 * n_f; // e * n_F
        let budget = (2 * (e_n_f + n_d)).div_ceil(4); // h_t >= d*(e*n_F+n_D)/4
        let h_t = budget;

        // Revealed points for t: OODS pair plus the query points (all secure).
        let mut revealed: Vec<CirclePoint<SecureField>> = oods.to_vec();
        revealed.extend(query_points.iter().map(|&x| lift(x)));

        let n_openings = 4 * revealed.len();
        let n_coeffs = 4 * h_t;

        let map = build_t_map(h_t, &revealed);
        assert_eq!(map.len(), n_openings);
        assert_eq!(map[0].len(), n_coeffs);
        let rank = m31_matrix_rank(&map);

        println!(
            "[Lemma2] n_F = {n_f}, n_D = {n_d}, h_t = {h_t}, \
             #openings = {n_openings}, 4*h_t = {n_coeffs}, rank(T) = {rank}"
        );

        // KEY EVIDENCE: the map's rank equals the number of openings AND that is
        // strictly fewer than t's coefficient count. So the revealed openings do
        // not pin t: it is information-theoretically under-determined and cannot
        // be reconstructed from what the verifier sees.
        assert_eq!(
            rank, n_openings,
            "the revealed openings are jointly independent (no accidental collapse)"
        );
        assert!(
            n_openings < n_coeffs,
            "openings must be strictly fewer than coefficients for under-determination"
        );
        // Therefore the coefficient nullspace has positive dimension:
        let null_dim = n_coeffs - rank;
        println!("[Lemma2] coefficient nullspace dimension = {null_dim} (> 0 => not reconstructible)");
        assert!(null_dim > 0, "t must retain hidden DOFs given the revealed openings");
    }

    #[test]
    fn lemma2_negative_overopened_t_becomes_reconstructible() {
        // NEGATIVE CONTROL: if the verifier were given MORE openings than t has
        // coefficients (e.g. an undersized randomizer budget, or split t halves
        // revealed), the map can attain full COLUMN rank and t becomes
        // reconstructible. This is the failure mode the unsplit/budget design
        // avoids; here we confirm the check can detect it.
        let h_t = 2; // deliberately tiny coefficient budget: 4*h_t = 8.

        // Many revealed points -> many openings, exceeding 4*h_t.
        let revealed: Vec<CirclePoint<SecureField>> = (0..6)
            .map(|i| CirclePoint::<SecureField>::get_point(1_000 + 7 * i as u128))
            .collect();

        let n_openings = 4 * revealed.len(); // 24
        let n_coeffs = 4 * h_t; // 8

        let map = build_t_map(h_t, &revealed);
        let rank = m31_matrix_rank(&map);
        println!(
            "[Lemma2 NEGATIVE] h_t = {h_t}, #openings = {n_openings}, 4*h_t = {n_coeffs}, \
             rank(T) = {rank}"
        );
        // Full column rank: the nullspace collapses, t IS reconstructible.
        assert_eq!(
            rank, n_coeffs,
            "with more openings than coefficients t attains full column rank"
        );
        let null_dim = n_coeffs - rank;
        println!("[Lemma2 NEGATIVE] coefficient nullspace dimension = {null_dim} (= 0 => reconstructible)");
        assert_eq!(null_dim, 0, "no hidden DOFs remain: t is reconstructible (failure mode)");
    }

    #[test]
    fn lemma2_split_multiplier_nonzero_on_real_query_domain() {
        // The verifier reconstructs the split with multiplier
        //   M(p) = p.repeated_double(max_log_degree_bound - 1).x      (core/proof.rs)
        // and composition query points live on the commitment/query domain
        //   CanonicCoset(max_log_degree_bound + log_blowup_factor).
        // The split parametrization q1(p) = (q(p) - a)/M is singular only where
        // M(p) = 0. On a canonic coset of log size L, M(p)=0 happens iff the
        // doubling exponent equals L - 1. Here exponent = max_log_degree_bound - 1
        // and L = max_log_degree_bound + log_blowup, so M=0 needs log_blowup = 0.
        // Because the blow-up factor is always >= 1, no query point has M(p)=0.
        // Scan the REAL domain and exponent to confirm (faithful to the verifier).
        for max_log_degree_bound in [4u32, 5, 6] {
            let exponent = max_log_degree_bound - 1;
            for log_blowup in [1u32, 2] {
                let query_domain =
                    CanonicCoset::new(max_log_degree_bound + log_blowup).circle_domain();
                let any_zero = (0..query_domain.size()).any(|i| {
                    let mut x = query_domain.at(i).x;
                    for _ in 0..exponent {
                        x = CirclePoint::<BaseField>::double_x(x);
                    }
                    x.is_zero()
                });
                assert!(
                    !any_zero,
                    "M(p) must be nonzero on the real query domain (blow-up >= 1)"
                );
                println!(
                    "[Lemma2 M!=0] max_log_degree_bound={max_log_degree_bound}, \
                     blowup={log_blowup}: no query point has M(p)=0"
                );
            }
        }

        // The degenerate case the construction must avoid: with blow-up 0 the
        // exponent equals L-1 and EVERY point of the bare coset hits x=0 (M=0).
        // This is why blow-up >= 1 is load-bearing for the split mask, not luck.
        let mldb = 5u32;
        let exponent = mldb - 1;
        let bare = CanonicCoset::new(mldb).circle_domain();
        let all_zero = (0..bare.size()).all(|i| {
            let mut x = bare.at(i).x;
            for _ in 0..exponent {
                x = CirclePoint::<BaseField>::double_x(x);
            }
            x.is_zero()
        });
        assert!(
            all_zero,
            "blow-up 0 degenerate: every bare-coset point hits x=0 (M=0)"
        );
        println!(
            "[Lemma2 M!=0] degenerate blow-up 0 (exponent=L-1) hits x=0 everywhere; \
             excluded because the blow-up factor is always >= 1"
        );
    }

    // ----- Part D: rank checks at DEPLOYED-scale parameters. -----

    #[test]
    fn deployed_scale_lemma1_full_rank_and_lemma2_underdetermined() {
        // Plonk-scale opening counts: n_queries = 64 (the zk_config value), an
        // interaction column charged at n_F = 2 OODS points, the composition charged
        // at n_F^comp = 1. Budgets are the ENFORCED ones: h_col = e·n_F + n_D and
        // h_t = n_F^comp + n_D + 1. This turns the enforced budget formulas into
        // computed rank facts at the real deployed scale.
        let trace_log_size = 6;
        let n_d = 64usize;

        // 64 distinct, non-conjugate query points on the evaluation domain.
        let d_domain = CanonicCoset::new(trace_log_size + 1).circle_domain();
        let query_points: Vec<CirclePoint<BaseField>> =
            (0..n_d).map(|i| d_domain.at(2 * i + 1)).collect();

        // Lemma 1: column-randomizer map E reaches full row rank at h_col = e·n_F+n_D.
        let oods = oods_pair(trace_log_size, 13579);
        let n_f = oods.len(); // 2
        let h_col = 4 * n_f + n_d; // e·n_F + n_D
        let e = build_column_eval_matrix(h_col, &oods, &query_points);
        let rows = 4 * n_f + n_d;
        let rank_e = m31_matrix_rank(&e);
        println!("[deployed Lemma1] e·n_F+n_D = {rows}, h_col = {h_col}, rank(E) = {rank_e}");
        assert_eq!(rank_e, rows, "E full row rank at the deployed column budget");

        // Lemma 2: at h_t = n_F^comp + n_D + 1 (the enforced reconstruction-resistance
        // budget) t stays under-determined: #openings < 4·h_t, nullspace > 0.
        let comp_oods = CirclePoint::<SecureField>::get_point(24680); // ζ, n_F^comp = 1
        let h_t = 1 + n_d + 1; // 66
        let mut revealed: Vec<CirclePoint<SecureField>> = vec![comp_oods];
        revealed.extend(query_points.iter().map(|&x| lift(x)));
        let map = build_t_map(h_t, &revealed);
        let n_openings = 4 * revealed.len(); // 4·65 = 260
        let n_coeffs = 4 * h_t; // 4·66 = 264
        let rank_t = m31_matrix_rank(&map);
        println!(
            "[deployed Lemma2] h_t = {h_t}, #openings = {n_openings}, 4·h_t = {n_coeffs}, \
             rank(T) = {rank_t}, nullspace = {}",
            n_coeffs - rank_t
        );
        assert_eq!(rank_t, n_openings, "t openings jointly independent at the deployed budget");
        assert!(
            n_openings < n_coeffs,
            "t under-determined at the enforced reconstruction-resistance budget"
        );

        // Negative control at the deployed scale: one below the budget (h_t = n_D+1)
        // makes #openings == 4·h_t, collapsing the nullspace — t reconstructible.
        let h_t_short = n_d + 1; // 65 -> 4·65 = 260 == #openings
        let map_short = build_t_map(h_t_short, &revealed);
        let rank_short = m31_matrix_rank(&map_short);
        println!(
            "[deployed Lemma2 NEGATIVE] h_t = {h_t_short}, 4·h_t = {}, rank = {rank_short}",
            4 * h_t_short
        );
        assert_eq!(
            rank_short,
            4 * h_t_short,
            "one below budget: t attains full column rank (reconstructible)"
        );
    }
}
