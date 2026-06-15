//! Statistical zero-knowledge witness masking — Layer 1.
//!
//! CANDIDATE construction, pending cryptographer sign-off. The formal
//! statistical-distance / leakage-bound argument does NOT yet exist in this
//! repository and is required before this is relied on for privacy. This module
//! masks the off-domain openings of a single witness column. It does NOT, on its
//! own, certify that a proof leaks nothing: ZK failures are silent. The unit
//! tests here prove the *mechanism* — on-domain values are preserved and
//! off-domain openings are
//! randomized — not the absence of leakage. The privacy guarantee is the
//! reviewed statistical-distance bound, never the test suite.
//!
//! # Construction
//!
//! Replace a witness polynomial `w` by
//!
//! ```text
//! ŵ = w + v_H · r,
//! ```
//!
//! where `v_H` is the vanishing polynomial of the trace domain `H` (the full
//! circle domain: the half-coset times its conjugate) and `r` is a random
//! low-degree polynomial carrying `randomizer_dimension` independent base-field
//! coefficients. Because `v_H ≡ 0` on `H`, the masked column agrees with `w` on
//! the trace domain — the AIR is unchanged — while every off-domain / FRI-query
//! opening is masked by `v_H · r`. NOTE: openings at distinct points are
//! correlated evaluations of one low-degree `r`, NOT mutually independent
//! quantities; whether the *joint* distribution of all verifier-visible openings
//! is blinded depends on a full-rank (Vandermonde) condition that a cryptographer
//! review must establish — it is not delivered by this masking step alone.
//!
//! `v_H · r` has higher degree than `w`, so `ŵ` lives in a larger FFT space; the
//! caller specifies that enlarged space via `masked_log_size`.

use num_traits::Zero;
use rand::{CryptoRng, RngCore};
use thiserror::Error;

use crate::core::circle::CirclePoint;
use crate::core::constraints::coset_vanishing;
use crate::core::fields::m31::{BaseField, P as M31_MODULUS};
use crate::core::fields::ExtensionOf;
use crate::core::poly::circle::{CanonicCoset, CircleDomain};
use crate::prover::backend::{Col, Column};
use crate::prover::poly::circle::{CircleCoefficients, CircleEvaluation, PolyOps};
use crate::prover::poly::BitReversedOrder;

/// Per-column parameters for Layer-1 witness masking.
///
/// `leakage_budget` is the conservative upper bound on the number of
/// verifier-visible linear openings of the masked column (OODS samples plus FRI
/// query openings, e.g. `e·n_F + n_D`). The randomizer carries at least that
/// many coefficients, the intended condition for the joint distribution of those
/// openings to be blinded — subject to a full-rank (Vandermonde) condition that
/// a cryptographer review must establish. Currently `leakage_budget` is a
/// caller-supplied number, not derived from the actual OODS/FRI opening counts.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct WitnessMaskConfig {
    trace_log_size: u32,
    masked_log_size: u32,
    randomizer_dimension: usize,
    leakage_budget: usize,
}

impl WitnessMaskConfig {
    /// Builds a config whose randomizer dimension equals the leakage budget.
    pub fn new(
        trace_log_size: u32,
        masked_log_size: u32,
        leakage_budget: usize,
    ) -> Result<Self, WitnessMaskError> {
        Self::with_randomizer_dimension(
            trace_log_size,
            masked_log_size,
            leakage_budget,
            leakage_budget,
        )
    }

    /// Builds a config with an explicit randomizer dimension `>= leakage_budget`.
    pub fn with_randomizer_dimension(
        trace_log_size: u32,
        masked_log_size: u32,
        randomizer_dimension: usize,
        leakage_budget: usize,
    ) -> Result<Self, WitnessMaskError> {
        let config = Self {
            trace_log_size,
            masked_log_size,
            randomizer_dimension,
            leakage_budget,
        };
        config.validate()?;
        Ok(config)
    }

    pub const fn trace_log_size(&self) -> u32 {
        self.trace_log_size
    }

    pub const fn masked_log_size(&self) -> u32 {
        self.masked_log_size
    }

    pub const fn randomizer_dimension(&self) -> usize {
        self.randomizer_dimension
    }

    pub const fn leakage_budget(&self) -> usize {
        self.leakage_budget
    }

    /// Fail-closed check that the masked column can absorb `required` openings.
    ///
    /// Both the randomizer dimension and the declared budget must cover the
    /// number of verifier-visible openings actually charged for this column.
    ///
    /// NOTE: `required` is currently supplied by the caller and is not derived
    /// from the real OODS/FRI opening counts. An `Ok` result asserts only a
    /// dimension inequality between declared numbers — it is NOT a leakage or
    /// zero-knowledge guarantee.
    pub fn check_leakage_budget(&self, required: usize) -> Result<(), WitnessMaskError> {
        if self.randomizer_dimension < required || self.leakage_budget < required {
            return Err(WitnessMaskError::PublicLeakageBudgetExceeded {
                randomizer_dimension: self.randomizer_dimension,
                leakage_budget: self.leakage_budget,
                required,
            });
        }
        Ok(())
    }

    /// Number of coefficient slots the randomizer occupies (dimension rounded up
    /// to a power of two).
    fn randomizer_coeff_count(&self) -> Result<usize, WitnessMaskError> {
        if self.randomizer_dimension == 0 {
            return Err(WitnessMaskError::EmptyRandomizerSpace);
        }
        self.randomizer_dimension
            .checked_next_power_of_two()
            .ok_or(WitnessMaskError::RandomizerDimensionTooLarge)
    }

    fn validate(&self) -> Result<(), WitnessMaskError> {
        if self.leakage_budget == 0 {
            return Err(WitnessMaskError::EmptyLeakageBudget);
        }
        if self.randomizer_dimension < self.leakage_budget {
            return Err(WitnessMaskError::InsufficientRandomizerDimension {
                randomizer_dimension: self.randomizer_dimension,
                leakage_budget: self.leakage_budget,
            });
        }

        let trace_domain = self.trace_domain()?;
        let masked_domain = self.masked_domain()?;
        let randomizer_coeff_count = self.randomizer_coeff_count()?;

        if masked_domain.log_size() <= trace_domain.log_size() {
            return Err(WitnessMaskError::MaskedDomainNotLarger {
                trace_log_size: trace_domain.log_size(),
                masked_log_size: masked_domain.log_size(),
            });
        }

        // `v_H · r` spans the trace domain plus the randomizer coefficients; the
        // masked FFT space must be wide enough to hold it without truncation.
        let required = trace_domain.size().checked_add(randomizer_coeff_count);
        if required.is_none_or(|required| required > masked_domain.size()) {
            return Err(WitnessMaskError::MaskedDomainTooSmall {
                trace_size: trace_domain.size(),
                randomizer_coeff_count,
                masked_size: masked_domain.size(),
            });
        }

        Ok(())
    }

    fn trace_domain(&self) -> Result<CircleDomain, WitnessMaskError> {
        Ok(CanonicCoset::try_new(self.trace_log_size)
            .map_err(|_| WitnessMaskError::InvalidCanonicCosetLogSize {
                log_size: self.trace_log_size,
            })?
            .circle_domain())
    }

    fn masked_domain(&self) -> Result<CircleDomain, WitnessMaskError> {
        Ok(CanonicCoset::try_new(self.masked_log_size)
            .map_err(|_| WitnessMaskError::InvalidCanonicCosetLogSize {
                log_size: self.masked_log_size,
            })?
            .circle_domain())
    }
}

/// Errors raised while configuring or applying Layer-1 witness masking.
#[derive(Clone, Copy, Debug, Error, PartialEq, Eq)]
pub enum WitnessMaskError {
    #[error("leakage budget must be non-zero")]
    EmptyLeakageBudget,
    #[error("randomizer dimension must be non-zero")]
    EmptyRandomizerSpace,
    #[error("randomizer dimension {randomizer_dimension} is smaller than leakage budget {leakage_budget}")]
    InsufficientRandomizerDimension {
        randomizer_dimension: usize,
        leakage_budget: usize,
    },
    #[error("leakage budget too small: randomizer dimension={randomizer_dimension}, declared budget={leakage_budget}, required={required}")]
    PublicLeakageBudgetExceeded {
        randomizer_dimension: usize,
        leakage_budget: usize,
        required: usize,
    },
    #[error("randomizer dimension is too large")]
    RandomizerDimensionTooLarge,
    #[error("invalid canonic coset log size: {log_size}")]
    InvalidCanonicCosetLogSize { log_size: u32 },
    #[error("masked domain must be larger than trace domain: trace={trace_log_size}, masked={masked_log_size}")]
    MaskedDomainNotLarger {
        trace_log_size: u32,
        masked_log_size: u32,
    },
    #[error("masked domain too small: trace size={trace_size}, randomizer coefficients={randomizer_coeff_count}, masked size={masked_size}")]
    MaskedDomainTooSmall {
        trace_size: usize,
        randomizer_coeff_count: usize,
        masked_size: usize,
    },
    #[error("masked domain intersects trace domain")]
    MaskedDomainIntersectsTraceDomain,
    #[error("witness degree space exceeds trace domain: witness={witness_log_size}, trace={trace_log_size}")]
    WitnessDegreeExceedsTraceDomain {
        witness_log_size: u32,
        trace_log_size: u32,
    },
}

/// Masks a witness column: returns `ŵ = w + v_H · r`.
///
/// On-domain (`H`) values are preserved; off-domain and FRI-query openings are
/// randomized by the fresh randomizer drawn from `rng`. Call with an independent
/// CSPRNG draw per column.
///
/// This function does NOT verify the opening count against the budget: callers
/// must invoke [`WitnessMaskConfig::check_leakage_budget`] separately.
pub fn mask_column<B, R>(
    witness: &CircleCoefficients<B>,
    config: WitnessMaskConfig,
    rng: &mut R,
) -> Result<CircleCoefficients<B>, WitnessMaskError>
where
    B: PolyOps,
    R: RngCore + CryptoRng + ?Sized,
{
    config.validate()?;

    if witness.log_size() > config.trace_log_size {
        return Err(WitnessMaskError::WitnessDegreeExceedsTraceDomain {
            witness_log_size: witness.log_size(),
            trace_log_size: config.trace_log_size,
        });
    }

    let trace_domain = config.trace_domain()?;
    let masked_domain = config.masked_domain()?;
    let twiddles = B::precompute_twiddles(masked_domain.half_coset);

    // v_H evaluated over the masked domain, in natural order; reject if the
    // masked domain meets H (any zero), which would defeat the masking.
    let vanishing_natural: Col<B, BaseField> = masked_domain
        .iter()
        .map(|point| full_trace_domain_vanishing(trace_domain, point))
        .collect();
    if (0..vanishing_natural.len()).any(|i| vanishing_natural.at(i).is_zero()) {
        return Err(WitnessMaskError::MaskedDomainIntersectsTraceDomain);
    }
    // Align v_H values with the bit-reversed evaluation order used below.
    let vanishing_values = CircleEvaluation::<B, BaseField>::new(masked_domain, vanishing_natural)
        .bit_reverse()
        .values;

    // r: a random polynomial with `randomizer_dimension` nonzero coefficients,
    // padded to the next power-of-two coefficient space.
    let randomizer = sample_randomizer::<B, R>(
        config.randomizer_coeff_count()?,
        config.randomizer_dimension,
        rng,
    );
    let randomizer_values = randomizer
        .evaluate_with_twiddles(masked_domain, &twiddles)
        .values;

    // delta = v_H · r, formed pointwise on the masked domain then interpolated.
    let delta_values: Col<B, BaseField> = (0..masked_domain.size())
        .map(|i| vanishing_values.at(i) * randomizer_values.at(i))
        .collect();
    let delta =
        CircleEvaluation::<B, BaseField, BitReversedOrder>::new(masked_domain, delta_values)
            .interpolate_with_twiddles(&twiddles);

    // ŵ = w + delta, in the enlarged FFT space.
    let extended_witness = witness.extend(masked_domain.log_size());
    let coeffs: Col<B, BaseField> = (0..extended_witness.coeffs.len())
        .map(|i| extended_witness.coeffs.at(i) + delta.coeffs.at(i))
        .collect();

    Ok(CircleCoefficients::new(coeffs))
}

/// Vanishing polynomial of the full trace domain `H = +-C + <G_n>`, evaluated at
/// `point`: the product of the half-coset and conjugate-half-coset vanishings.
fn full_trace_domain_vanishing<F>(trace_domain: CircleDomain, point: CirclePoint<F>) -> F
where
    F: ExtensionOf<BaseField>,
{
    coset_vanishing(trace_domain.half_coset, point)
        * coset_vanishing(trace_domain.half_coset.conjugate(), point)
}

/// Draws a randomizer polynomial: `dimension` uniform base-field coefficients,
/// the rest zero, in a `coeff_count`-slot FFT-basis coefficient vector.
fn sample_randomizer<B, R>(
    coeff_count: usize,
    dimension: usize,
    rng: &mut R,
) -> CircleCoefficients<B>
where
    B: PolyOps,
    R: RngCore + CryptoRng + ?Sized,
{
    let coeffs: Col<B, BaseField> = (0..coeff_count)
        .map(|i| {
            if i < dimension {
                sample_base_field(rng)
            } else {
                BaseField::zero()
            }
        })
        .collect();
    CircleCoefficients::new(coeffs)
}

/// Uniform M31 sample by rejection.
fn sample_base_field<R>(rng: &mut R) -> BaseField
where
    R: RngCore + ?Sized,
{
    loop {
        let candidate = rng.next_u32() & 0x7fff_ffff;
        if candidate < M31_MODULUS {
            return BaseField::from_u32_unchecked(candidate);
        }
    }
}

#[cfg(test)]
mod tests {
    use rand::rngs::StdRng;
    use rand::SeedableRng;

    use super::*;
    use crate::core::fields::m31::M31;
    use crate::core::fields::qm31::SecureField;
    use crate::prover::backend::cpu::CpuBackend;

    #[test]
    fn mask_preserves_trace_domain_and_randomizes_off_domain() {
        let witness = CircleCoefficients::<CpuBackend>::new((0..8).map(M31::from).collect());
        let config = WitnessMaskConfig::new(3, 5, 8).unwrap();

        let mut rng0 = StdRng::seed_from_u64(1);
        let mut rng1 = StdRng::seed_from_u64(2);
        let masked0 = mask_column(&witness, config, &mut rng0).unwrap();
        let masked1 = mask_column(&witness, config, &mut rng1).unwrap();

        // On the trace domain the AIR is untouched: ŵ == w.
        let trace_domain = CanonicCoset::new(config.trace_log_size()).circle_domain();
        for point in trace_domain {
            let point = point.into_ef::<SecureField>();
            assert_eq!(witness.eval_at_point(point), masked0.eval_at_point(point));
            assert_eq!(witness.eval_at_point(point), masked1.eval_at_point(point));
        }

        // Off domain, two independent randomizers give different openings.
        let off_domain_point = CanonicCoset::new(config.masked_log_size())
            .circle_domain()
            .at(0)
            .into_ef::<SecureField>();
        assert_ne!(
            masked0.eval_at_point(off_domain_point),
            masked1.eval_at_point(off_domain_point)
        );
    }

    #[test]
    fn config_rejects_bad_parameters() {
        assert_eq!(
            WitnessMaskConfig::with_randomizer_dimension(3, 5, 7, 8).unwrap_err(),
            WitnessMaskError::InsufficientRandomizerDimension {
                randomizer_dimension: 7,
                leakage_budget: 8,
            }
        );
        assert_eq!(
            WitnessMaskConfig::new(3, 5, 0).unwrap_err(),
            WitnessMaskError::EmptyLeakageBudget
        );
        assert_eq!(
            WitnessMaskConfig::new(0, 5, 8).unwrap_err(),
            WitnessMaskError::InvalidCanonicCosetLogSize { log_size: 0 }
        );
        // Masked domain not strictly larger than the trace domain.
        assert_eq!(
            WitnessMaskConfig::new(3, 3, 8).unwrap_err(),
            WitnessMaskError::MaskedDomainNotLarger {
                trace_log_size: 3,
                masked_log_size: 3,
            }
        );
    }

    #[test]
    fn leakage_budget_is_fail_closed() {
        let config = WitnessMaskConfig::new(3, 5, 8).unwrap();
        assert!(config.check_leakage_budget(8).is_ok());
        assert_eq!(
            config.check_leakage_budget(9).unwrap_err(),
            WitnessMaskError::PublicLeakageBudgetExceeded {
                randomizer_dimension: 8,
                leakage_budget: 8,
                required: 9,
            }
        );
    }
}
