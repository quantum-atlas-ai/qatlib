/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Foundations.CbmdAnalysis.Core.CosineSeriesIdentity
import Qatlib.Foundations.CbmdAnalysis.Core.CosineAngularComparison

/-!
# Cosine sampling formulas for matrix propagators

This module specializes the cosine-regulator sampling series to wave, Bessel, and Airy
propagators of `L + I • H`. For positive semidefinite `L`, positive definite `H`, and a norm
bound on `H`, it proves absolute summability and explicit inverse-square truncation errors. The
Airy formulas use `airyTimeScale`, as in [WangEtAl2026].

## Main statements

* `wave_cbmd_series`: an absolutely summable wave sampling representation.
* `bessel_cbmd_target_error`: an explicit truncation error for the Bessel representation.
* `airy_cbmd_target_error`: the corresponding Airy error with the transformed time scale.

## References

* [Wang et al., 2026][WangEtAl2026]
-/

namespace Qatlib.Foundations.CbmdAnalysis.Core

set_option autoImplicit false
set_option maxHeartbeats 500000
noncomputable section
namespace CBMD
open Complex
open scoped BigOperators Matrix.Norms.L2Operator ComplexOrder MatrixOrder
variable {n : Type*} [Fintype n] [DecidableEq n]

/-- For positive semidefinite `L`, positive definite `H`, positive `γ` and time with `‖H‖ ≤ γ`,
the weighted wave samples are absolutely summable and reconstruct the target as the
regulator-weighted baseline minus the regulator-weighted sample series [WangEtAl2026]. -/
theorem wave_cbmd_series (L H : Matrix n n ℂ) (hL : L.PosSemidef) (hH : H.PosDef)
    {γ t : ℝ} (hγ : 0 < γ) (ht : 0 < t) (hγH : ‖H‖ ≤ γ) :
    Summable (fun k : ℕ => ‖cosineSampleCoefficient γ t k •
      wavePropagator (L + (cosineSampleScale γ t k : ℂ) • H) (t : ℂ)‖) ∧
    wavePropagator (L + I • H) (t : ℂ) =
      cosineRegulator γ t 1 • wavePropagator L (t : ℂ) -
      cosineRegulator γ t 1 • (∑' k : ℕ, cosineSampleCoefficient γ t k •
        wavePropagator (L + (cosineSampleScale γ t k : ℂ) • H) (t : ℂ)) := by
  have hn := cosineSample_norm_summable hγ ht (waveCosineNumerator L H (t : ℂ))
    (waveCosineNumerator_sample_norm_le_one L H hL hH.posSemidef hγ ht t)
  have hid := cosine_kernel_series_identity hγ ht
    (cosineAngularConstant_pos L H t).le (waveCosineNumerator L H (t : ℂ))
    (waveCosineNumerator_differentiable L H (t : ℂ)) (waveCosineNumerator_sample_norm_le_one L H hL hH.posSemidef hγ ht t) (waveCosineNumerator_circle_comparison L H hH hγ ht hγH)
  simpa only [cosineSample, cosineLCUSum, waveCosineNumerator, cosinePencil_sample,
    mul_one, mul_zero, zero_smul, add_zero] using! And.intro hn hid

/-- Under the positivity and norm hypotheses, truncating the wave sampling formula after index
`K` gives error at most `‖cosineRegulator γ t 1‖ * γ * t ^ 2 / (π ^ 3 * (K + 1 / 2) ^ 2)`. -/
theorem wave_cbmd_target_error (L H : Matrix n n ℂ) (hL : L.PosSemidef) (hH : H.PosDef)
    {γ t : ℝ} (hγ : 0 < γ) (ht : 0 < t) (hγH : ‖H‖ ≤ γ) (K : ℕ) :
    ‖wavePropagator (L + I • H) (t : ℂ) -
      (cosineRegulator γ t 1 • wavePropagator L (t : ℂ) -
        cosineRegulator γ t 1 • (∑ k ∈ Finset.range (K + 1),
          cosineSampleCoefficient γ t k •
            wavePropagator (L + (cosineSampleScale γ t k : ℂ) • H) (t : ℂ)))‖ ≤
      ‖cosineRegulator γ t 1‖ * γ * t ^ 2 /
        (Real.pi ^ 3 * ((K : ℝ) + 1 / 2) ^ 2) := by
  have he := cosineLCU_target_error_le hγ ht
    (cosineAngularConstant_pos L H t).le (waveCosineNumerator L H (t : ℂ))
    (waveCosineNumerator_differentiable L H (t : ℂ)) (waveCosineNumerator_sample_norm_le_one L H hL hH.posSemidef hγ ht t) (waveCosineNumerator_circle_comparison L H hH hγ ht hγH) K
  simpa only [cosineSample, cosineLCUSum, waveCosineNumerator, cosinePencil_sample,
    mul_one, mul_zero, zero_smul, add_zero] using! he

/-- For positive semidefinite `L`, positive definite `H`, positive `γ` and time with `‖H‖ ≤ γ`,
the weighted Bessel samples are absolutely summable and reconstruct the target as the
regulator-weighted baseline minus the regulator-weighted sample series [WangEtAl2026]. -/
theorem bessel_cbmd_series (L H : Matrix n n ℂ) (hL : L.PosSemidef) (hH : H.PosDef)
    {γ t : ℝ} (hγ : 0 < γ) (ht : 0 < t) (hγH : ‖H‖ ≤ γ) :
    Summable (fun k : ℕ => ‖cosineSampleCoefficient γ t k •
      besselPropagator (L + (cosineSampleScale γ t k : ℂ) • H) (t : ℂ)‖) ∧
    besselPropagator (L + I • H) (t : ℂ) =
      cosineRegulator γ t 1 • besselPropagator L (t : ℂ) -
      cosineRegulator γ t 1 • (∑' k : ℕ, cosineSampleCoefficient γ t k •
        besselPropagator (L + (cosineSampleScale γ t k : ℂ) • H) (t : ℂ)) := by
  have hn := cosineSample_norm_summable hγ ht (besselCosineNumerator L H (t : ℂ))
    (besselCosineNumerator_sample_norm_le_one L H hL hH.posSemidef hγ ht t)
  have hid := cosine_kernel_series_identity hγ ht
    (cosineAngularConstant_pos L H t).le (besselCosineNumerator L H (t : ℂ))
    (besselCosineNumerator_differentiable L H (t : ℂ)) (besselCosineNumerator_sample_norm_le_one L H hL hH.posSemidef hγ ht t) (besselCosineNumerator_circle_comparison L H hH hγ ht hγH)
  simpa only [cosineSample, cosineLCUSum, besselCosineNumerator, cosinePencil_sample,
    mul_one, mul_zero, zero_smul, add_zero] using! And.intro hn hid

/-- Under the positivity and norm hypotheses, truncating the Bessel sampling formula after index
`K` gives error at most `‖cosineRegulator γ t 1‖ * γ * t ^ 2 / (π ^ 3 * (K + 1 / 2) ^ 2)`. -/
theorem bessel_cbmd_target_error (L H : Matrix n n ℂ) (hL : L.PosSemidef) (hH : H.PosDef)
    {γ t : ℝ} (hγ : 0 < γ) (ht : 0 < t) (hγH : ‖H‖ ≤ γ) (K : ℕ) :
    ‖besselPropagator (L + I • H) (t : ℂ) -
      (cosineRegulator γ t 1 • besselPropagator L (t : ℂ) -
        cosineRegulator γ t 1 • (∑ k ∈ Finset.range (K + 1),
          cosineSampleCoefficient γ t k •
            besselPropagator (L + (cosineSampleScale γ t k : ℂ) • H) (t : ℂ)))‖ ≤
      ‖cosineRegulator γ t 1‖ * γ * t ^ 2 /
        (Real.pi ^ 3 * ((K : ℝ) + 1 / 2) ^ 2) := by
  have he := cosineLCU_target_error_le hγ ht
    (cosineAngularConstant_pos L H t).le (besselCosineNumerator L H (t : ℂ))
    (besselCosineNumerator_differentiable L H (t : ℂ)) (besselCosineNumerator_sample_norm_le_one L H hL hH.posSemidef hγ ht t) (besselCosineNumerator_circle_comparison L H hH hγ ht hγH) K
  simpa only [cosineSample, cosineLCUSum, besselCosineNumerator, cosinePencil_sample,
    mul_one, mul_zero, zero_smul, add_zero] using! he

/-- For positive semidefinite `L`, positive definite `H`, positive `γ` and time with `‖H‖ ≤ γ`,
the Airy samples using `airyTimeScale t` are absolutely summable and reconstruct the target
from the regulator-weighted baseline and sample series [WangEtAl2026]. -/
theorem airy_cbmd_series (L H : Matrix n n ℂ) (hL : L.PosSemidef) (hH : H.PosDef)
    {γ t : ℝ} (hγ : 0 < γ) (ht : 0 < t) (hγH : ‖H‖ ≤ γ) :
    Summable (fun k : ℕ => ‖cosineSampleCoefficient γ (airyTimeScale t) k •
      airyPropagator (L + (cosineSampleScale γ (airyTimeScale t) k : ℂ) • H) (t : ℂ)‖) ∧
    airyPropagator (L + I • H) (t : ℂ) =
      cosineRegulator γ (airyTimeScale t) 1 • airyPropagator L (t : ℂ) -
      cosineRegulator γ (airyTimeScale t) 1 • (∑' k : ℕ, cosineSampleCoefficient γ (airyTimeScale t) k •
        airyPropagator (L + (cosineSampleScale γ (airyTimeScale t) k : ℂ) • H) (t : ℂ)) := by
  have hn := cosineSample_norm_summable hγ (airyTimeScale_pos_of_pos ht) (airyCosineNumerator L H (t : ℂ))
    (airyCosineNumerator_sample_norm_le_one L H hL hH.posSemidef hγ (airyTimeScale_pos_of_pos ht) t ht.le)
  have hid := cosine_kernel_series_identity hγ (airyTimeScale_pos_of_pos ht)
    (cosineAngularConstant_pos L H (airyTimeScale t)).le (airyCosineNumerator L H (t : ℂ))
    (airyCosineNumerator_differentiable L H (t : ℂ)) (airyCosineNumerator_sample_norm_le_one L H hL hH.posSemidef hγ (airyTimeScale_pos_of_pos ht) t ht.le) (airyCosineNumerator_circle_comparison L H hH hγ ht hγH)
  simpa only [cosineSample, cosineLCUSum, airyCosineNumerator, cosinePencil_sample,
    mul_one, mul_zero, zero_smul, add_zero] using! And.intro hn hid

/-- Under the positivity and norm hypotheses, truncating the Airy sampling formula after index
`K` gives error at most `‖cosineRegulator γ (airyTimeScale t) 1‖ * γ * (airyTimeScale t) ^ 2
/ (π ^ 3 * (K + 1 / 2) ^ 2)`. -/
theorem airy_cbmd_target_error (L H : Matrix n n ℂ) (hL : L.PosSemidef) (hH : H.PosDef)
    {γ t : ℝ} (hγ : 0 < γ) (ht : 0 < t) (hγH : ‖H‖ ≤ γ) (K : ℕ) :
    ‖airyPropagator (L + I • H) (t : ℂ) -
      (cosineRegulator γ (airyTimeScale t) 1 • airyPropagator L (t : ℂ) -
        cosineRegulator γ (airyTimeScale t) 1 • (∑ k ∈ Finset.range (K + 1),
          cosineSampleCoefficient γ (airyTimeScale t) k •
            airyPropagator (L + (cosineSampleScale γ (airyTimeScale t) k : ℂ) • H) (t : ℂ)))‖ ≤
      ‖cosineRegulator γ (airyTimeScale t) 1‖ * γ * (airyTimeScale t) ^ 2 /
        (Real.pi ^ 3 * ((K : ℝ) + 1 / 2) ^ 2) := by
  have he := cosineLCU_target_error_le hγ (airyTimeScale_pos_of_pos ht)
    (cosineAngularConstant_pos L H (airyTimeScale t)).le (airyCosineNumerator L H (t : ℂ))
    (airyCosineNumerator_differentiable L H (t : ℂ)) (airyCosineNumerator_sample_norm_le_one L H hL hH.posSemidef hγ (airyTimeScale_pos_of_pos ht) t ht.le) (airyCosineNumerator_circle_comparison L H hH hγ ht hγH) K
  simpa only [cosineSample, cosineLCUSum, airyCosineNumerator, cosinePencil_sample,
    mul_one, mul_zero, zero_smul, add_zero] using! he

end CBMD

end
end Qatlib.Foundations.CbmdAnalysis.Core
