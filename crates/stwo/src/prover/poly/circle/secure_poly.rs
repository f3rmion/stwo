use std::marker::PhantomData;
use std::ops::{Deref, DerefMut};

use super::{CircleCoefficients, CircleEvaluation, PolyOps};
use crate::core::circle::CirclePoint;
use crate::core::fields::m31::BaseField;
use crate::core::fields::qm31::{SecureField, SECURE_EXTENSION_DEGREE};
use crate::core::poly::circle::CircleDomain;
use crate::prover::backend::{ColumnOps, CpuBackend};
use crate::prover::poly::twiddles::TwiddleTree;
use crate::prover::poly::BitReversedOrder;
use crate::prover::secure_column::SecureColumnByCoords;

pub struct SecureCirclePoly<B: ColumnOps<BaseField>>(
    pub [CircleCoefficients<B>; SECURE_EXTENSION_DEGREE],
);

impl<B: PolyOps> SecureCirclePoly<B> {
    pub fn eval_at_point(&self, point: CirclePoint<SecureField>) -> SecureField {
        SecureField::from_partial_evals(self.eval_columns_at_point(point))
    }

    pub fn eval_columns_at_point(
        &self,
        point: CirclePoint<SecureField>,
    ) -> [SecureField; SECURE_EXTENSION_DEGREE] {
        [
            self[0].eval_at_point(point),
            self[1].eval_at_point(point),
            self[2].eval_at_point(point),
            self[3].eval_at_point(point),
        ]
    }

    pub fn log_size(&self) -> u32 {
        self[0].log_size()
    }

    pub fn evaluate_with_twiddles(
        &self,
        domain: CircleDomain,
        twiddles: &TwiddleTree<B>,
    ) -> SecureEvaluation<B, BitReversedOrder> {
        let polys = self.0.each_ref();
        let columns = polys.map(|poly| poly.evaluate_with_twiddles(domain, twiddles).values);
        SecureEvaluation::new(domain, SecureColumnByCoords { columns })
    }

    pub fn into_coordinate_polys(self) -> [CircleCoefficients<B>; SECURE_EXTENSION_DEGREE] {
        self.0
    }

    /// See the documentation in `[super::ops::split_at_mid]`.
    pub fn split_at_mid(self) -> (Self, Self) {
        // To avoid cloning or copying, destructure self by-value so we can move the contents.
        // NOTE: This requires `self` to be passed by value, not by reference!
        let [poly0, poly1, poly2, poly3] = self.0;
        let (left0, right0) = poly0.split_at_mid();
        let (left1, right1) = poly1.split_at_mid();
        let (left2, right2) = poly2.split_at_mid();
        let (left3, right3) = poly3.split_at_mid();
        let left = [left0, left1, left2, left3];
        let right = [right0, right1, right2, right3];
        (Self(left), Self(right))
    }

    /// Splits into `2^k` chunks by applying [`Self::split_at_mid`] `k` times.
    ///
    /// `k = 0` returns `self`; `k = 1` is `split_at_mid` (left then right). The
    /// returned chunks, each of log size `self.log_size() - k`, recombine to the
    /// original polynomial at a point `z` by a Horner fold from the deepest level
    /// up: starting from the chunk evaluations, repeatedly combine adjacent pairs
    /// `a + m_i·b` with `m_i = z.repeated_double(chunk_log_size - 1 + i).x` for
    /// `i = 0..k` (where `chunk_log_size = self.log_size() - k`). See
    /// [`super::ops::split_at_mid`] for the single-level identity.
    pub fn split_k(self, k: u32) -> Vec<Self> {
        if k == 0 {
            return vec![self];
        }
        let (left, right) = self.split_at_mid();
        let mut chunks = left.split_k(k - 1);
        chunks.extend(right.split_k(k - 1));
        chunks
    }
}

impl<B: ColumnOps<BaseField>> Deref for SecureCirclePoly<B> {
    type Target = [CircleCoefficients<B>; SECURE_EXTENSION_DEGREE];

    fn deref(&self) -> &Self::Target {
        &self.0
    }
}

/// A [`SecureField`] evaluation defined on a [CircleDomain].
///
/// The evaluation is stored as a column major array of [`SECURE_EXTENSION_DEGREE`] many base field
/// evaluations. The evaluations are ordered according to the [CircleDomain] ordering.
#[derive(Clone)]
pub struct SecureEvaluation<B: ColumnOps<BaseField>, EvalOrder> {
    pub domain: CircleDomain,
    pub values: SecureColumnByCoords<B>,
    _eval_order: PhantomData<EvalOrder>,
}

impl<B: ColumnOps<BaseField>, EvalOrder> SecureEvaluation<B, EvalOrder> {
    pub fn new(domain: CircleDomain, values: SecureColumnByCoords<B>) -> Self {
        assert_eq!(domain.size(), values.len());
        Self {
            domain,
            values,
            _eval_order: PhantomData,
        }
    }

    pub fn into_coordinate_evals(
        self,
    ) -> [CircleEvaluation<B, BaseField, EvalOrder>; SECURE_EXTENSION_DEGREE] {
        let Self { domain, values, .. } = self;
        values.columns.map(|c| CircleEvaluation::new(domain, c))
    }

    pub fn to_cpu(&self) -> SecureEvaluation<CpuBackend, EvalOrder> {
        SecureEvaluation {
            domain: self.domain,
            values: self.values.to_cpu(),
            _eval_order: PhantomData,
        }
    }
}

impl<B: ColumnOps<BaseField>, EvalOrder> Deref for SecureEvaluation<B, EvalOrder> {
    type Target = SecureColumnByCoords<B>;

    fn deref(&self) -> &Self::Target {
        &self.values
    }
}

impl<B: ColumnOps<BaseField>, EvalOrder> DerefMut for SecureEvaluation<B, EvalOrder> {
    fn deref_mut(&mut self) -> &mut Self::Target {
        &mut self.values
    }
}

impl<B: PolyOps> SecureEvaluation<B, BitReversedOrder> {
    /// Computes a minimal [`SecureCirclePoly`] that evaluates to the same values as this
    /// evaluation, using precomputed twiddles.
    pub fn interpolate_with_twiddles(self, twiddles: &TwiddleTree<B>) -> SecureCirclePoly<B> {
        let domain = self.domain;
        let cols = self.values.columns;
        SecureCirclePoly(cols.map(|c| {
            CircleEvaluation::<B, BaseField, BitReversedOrder>::new(domain, c)
                .interpolate_with_twiddles(twiddles)
        }))
    }
}

impl<EvalOrder> From<CircleEvaluation<CpuBackend, SecureField, EvalOrder>>
    for SecureEvaluation<CpuBackend, EvalOrder>
{
    fn from(evaluation: CircleEvaluation<CpuBackend, SecureField, EvalOrder>) -> Self {
        Self::new(evaluation.domain, evaluation.values.into_iter().collect())
    }
}

#[cfg(test)]
mod tests {
    use crate::core::circle::CirclePoint;
    use crate::core::fields::m31::BaseField;
    use crate::prover::backend::cpu::CpuCirclePoly;
    use crate::prover::poly::circle::SecureCirclePoly;

    #[test]
    fn test_secure_circle_poly_split_at_mid() {
        let log_size = 10;
        let poly = SecureCirclePoly(std::array::from_fn(|i| {
            CpuCirclePoly::new(
                (0..1 << log_size)
                    .map(|x| {
                        BaseField::from_u32_unchecked(x) + BaseField::from_u32_unchecked(i as u32)
                    })
                    .collect(),
            )
        }));

        let (left, right) = SecureCirclePoly(poly.clone()).split_at_mid();
        let random_point = CirclePoint::get_point(21903);

        assert_eq!(
            left.eval_at_point(random_point)
                + random_point.repeated_double(log_size - 2).x * right.eval_at_point(random_point),
            poly.eval_at_point(random_point)
        );

        assert_eq!(left.log_size(), log_size - 1);
        assert_eq!(right.log_size(), log_size - 1);
    }

    #[test]
    fn test_secure_circle_poly_split_k_recombines() {
        use crate::core::proof::recombine_split_evals;

        let log_size = 10;
        let make = || {
            SecureCirclePoly(std::array::from_fn(|i| {
                CpuCirclePoly::new(
                    (0..1 << log_size)
                        .map(|x| {
                            BaseField::from_u32_unchecked(x) + BaseField::from_u32_unchecked(i as u32)
                        })
                        .collect(),
                )
            }))
        };
        let z = CirclePoint::get_point(21903);
        let expected = make().eval_at_point(z);

        // k = 0..=3: 2^k chunks at log_size - k recombine to the original eval, and
        // k = 1 matches split_at_mid's single-multiplier identity.
        for k in 0..=3u32 {
            let chunks = make().split_k(k);
            assert_eq!(chunks.len(), 1 << k);
            for c in &chunks {
                assert_eq!(c.log_size(), log_size - k);
            }
            let evals: Vec<_> = chunks.iter().map(|c| c.eval_at_point(z)).collect();
            let chunk_log_degree_bound = log_size - k;
            assert_eq!(
                recombine_split_evals(&evals, z, chunk_log_degree_bound, k),
                expected,
                "split_k recombination must reproduce the original eval (k={k})"
            );
        }
    }
}
