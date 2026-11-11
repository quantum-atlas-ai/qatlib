/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Foundations.CbmdAnalysis.Core.BesselMixture
import Mathlib.Analysis.RCLike.Sqrt
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Complex

/-!
# Cosine regulators and their sample poles

This module defines `cosineRegulator` through the scalar wave propagator, together with its
sample angles, scales, poles, and residue coefficients. The quadratic cosine identity locates
all regulator zeros and gives their derivatives; additional formulas evaluate the contour
denominator derivatives at zero, one, and the sample poles. These definitions implement the
cosine regulator used in [WangEtAl2026].

## Main statements

* `cosineRegulator_quadratic`: the regulator becomes complex cosine under a quadratic
  substitution.
* `cosineRegulator_eq_zero_iff`: the sample poles are exactly the regulator zeros for positive
  parameters.
* `cosineRegulator_deriv_sample_ne_zero`: all sample zeros are simple.

## References

* [Wang et al., 2026][WangEtAl2026]
-/

set_option warningAsError false

namespace Qatlib.Foundations.CbmdAnalysis.Core

set_option autoImplicit false
noncomputable section
namespace CBMD
open Complex

/-- The half-integer angle `(k + 1 / 2) * π` of the `k`th cosine sample. -/
def cosineSampleAngle (k : ℕ) : ℝ := ((k : ℝ) + 1 / 2) * Real.pi
/-- The real sampling scale `cosineSampleAngle k ^ 2 / (γ * τ ^ 2)`. -/
def cosineSampleScale (γ τ : ℝ) (k : ℕ) : ℝ := cosineSampleAngle k ^ 2 / (γ * τ ^ 2)
/-- The complex sample pole `-I * cosineSampleScale γ τ k`. -/
def cosineSamplePole (γ τ : ℝ) (k : ℕ) : ℂ := -I * (cosineSampleScale γ τ k : ℂ)
/-- The scalar wave propagator at input `I * γ * z` and real time `τ`, viewed as a function of
the complex parameter `z`. -/
def cosineRegulator (γ τ : ℝ) (z : ℂ) : ℂ := wavePropagator (I * (γ : ℂ) * z) (τ : ℂ)
/-- The coefficient `2 * (-1) ^ k / (cosineSampleAngle k * (1 + I * cosineSampleScale γ τ k))`,
with real quantities cast to complex numbers. -/
def cosineSampleCoefficient (γ τ : ℝ) (k : ℕ) : ℂ :=
  2 * (-1) ^ k / ((cosineSampleAngle k : ℂ) * (1 + I * (cosineSampleScale γ τ k : ℂ)))
/-- The product `z * (z - 1) * cosineRegulator γ τ z` defining the cosine contour denominator. -/
def cosineContourDenominator (γ τ : ℝ) (z : ℂ) : ℂ := z * (z - 1) * cosineRegulator γ τ z

/-- Every cosine sample angle is strictly positive. -/
theorem cosineSampleAngle_pos (k : ℕ) : 0 < cosineSampleAngle k := by
  unfold cosineSampleAngle
  positivity

/-- For positive `γ` and `τ`, every cosine sample scale is strictly positive. -/
theorem cosineSampleScale_pos {γ τ : ℝ} (hγ : 0 < γ) (hτ : 0 < τ) (k : ℕ) :
    0 < cosineSampleScale γ τ k := by
  unfold cosineSampleScale
  exact div_pos (sq_pos_of_pos (cosineSampleAngle_pos k)) (mul_pos hγ (sq_pos_of_pos hτ))

/-- The cosine regulator is complex analytic at every point for all real parameters. -/
theorem cosineRegulator_analytic (γ τ : ℝ) (z : ℂ) : AnalyticAt ℂ (cosineRegulator γ τ) z := by
  change AnalyticAt ℂ (fun w => wavePropagator (I * (γ : ℂ) * w) (τ : ℂ)) z
  have h := wave_series_affine_analytic (0 : ℂ) (I * (γ : ℂ)) (τ : ℂ) z
  simpa only [zero_add, smul_eq_mul, mul_comm, wavePropagator] using! h

/-- For nonzero `γ` and `τ`, evaluating the regulator at `(-I / (γ * τ ^ 2)) * q ^ 2` gives `cos
q`. -/
theorem cosineRegulator_quadratic {γ τ : ℝ} (hγ : γ ≠ 0) (hτ : τ ≠ 0) (q : ℂ) :
    cosineRegulator γ τ ((-I / ((γ : ℂ) * (τ : ℂ) ^ 2)) * q ^ 2) = cos q := by
  have hγc : (γ : ℂ) ≠ 0 := by exact_mod_cast hγ
  have hτc : (τ : ℂ) ≠ 0 := by exact_mod_cast hτ
  have he : I * (γ : ℂ) * ((-I / ((γ : ℂ) * (τ : ℂ) ^ 2)) * q ^ 2) =
      (q / (τ : ℂ)) ^ 2 := by
    field_simp
    simp [I_sq]
  rw [cosineRegulator, he, wavePropagator_scalar_square]
  congr 1
  field_simp

/-- Each cosine sample pole is the quadratic image of its sample angle under the factor `-I / (γ
* τ ^ 2)`. -/
private theorem cosineSamplePole_quadratic (γ τ : ℝ) (k : ℕ) :
    cosineSamplePole γ τ k = (-I / ((γ : ℂ) * (τ : ℂ) ^ 2)) * (cosineSampleAngle k : ℂ) ^ 2 := by
  simp only [cosineSamplePole, cosineSampleScale, ofReal_div, ofReal_mul, ofReal_pow]
  ring

/-- The complex cosine of every cosine sample angle is zero. -/
theorem cosineSampleAngle_cos (k : ℕ) : cos (cosineSampleAngle k : ℂ) = 0 := by
  rw [← ofReal_cos]
  have he : cosineSampleAngle k = (k : ℝ) * Real.pi + Real.pi / 2 := by
    unfold cosineSampleAngle
    ring
  rw [he, Real.cos_add_pi_div_two, Real.sin_nat_mul_pi]
  simp

/-- The complex sine of the `k`th cosine sample angle is `(-1) ^ k`. -/
theorem cosineSampleAngle_sin (k : ℕ) : sin (cosineSampleAngle k : ℂ) = (-1) ^ k := by
  rw [← ofReal_sin]
  have he : cosineSampleAngle k = Real.pi / 2 + (k : ℝ) * Real.pi := by
    unfold cosineSampleAngle
    ring
  rw [he, Real.sin_add_nat_mul_pi, Real.sin_pi_div_two, mul_one]
  push_cast
  rfl

/-- For positive parameters, the cosine regulator vanishes at every sample pole. -/
theorem cosineRegulator_sample_zero {γ τ : ℝ} (hγ : 0 < γ) (hτ : 0 < τ) (k : ℕ) :
    cosineRegulator γ τ (cosineSamplePole γ τ k) = 0 := by
  rw [cosineSamplePole_quadratic, cosineRegulator_quadratic hγ.ne' hτ.ne', cosineSampleAngle_cos]

/-- For positive parameters, the cosine regulator vanishes at `z` exactly when `z` is a cosine
sample pole. -/
theorem cosineRegulator_eq_zero_iff {γ τ : ℝ} (hγ : 0 < γ) (hτ : 0 < τ) (z : ℂ) :
    cosineRegulator γ τ z = 0 ↔ ∃ k : ℕ, z = cosineSamplePole γ τ k := by
  constructor
  · intro hz
    let q : ℂ := Complex.sqrt (I * (γ : ℂ) * (τ : ℂ) ^ 2 * z)
    have hq2 : q ^ 2 = I * (γ : ℂ) * (τ : ℂ) ^ 2 * z :=
      Complex.cpow_ofNat_inv_pow _ 2
    have hγc : (γ : ℂ) ≠ 0 := by exact_mod_cast hγ.ne'
    have hτc : (τ : ℂ) ≠ 0 := by exact_mod_cast hτ.ne'
    have hrec : z = (-I / ((γ : ℂ) * (τ : ℂ) ^ 2)) * q ^ 2 := by
      rw [hq2]
      field_simp
      simp [I_sq]
    have hcos : cos q = 0 := by
      rw [hrec, cosineRegulator_quadratic hγ.ne' hτ.ne'] at hz
      exact hz
    obtain ⟨j, hj⟩ := Complex.cos_eq_zero_iff.mp hcos
    cases j with
    | ofNat k =>
      refine ⟨k, ?_⟩
      rw [hrec, hj, cosineSamplePole_quadratic]
      unfold cosineSampleAngle
      push_cast
      simp only [Int.ofNat_eq_natCast, Int.cast_natCast]
      ring
    | negSucc k =>
      refine ⟨k, ?_⟩
      rw [hrec, hj, cosineSamplePole_quadratic]
      unfold cosineSampleAngle
      push_cast
      ring
  · rintro ⟨k, rfl⟩
    exact cosineRegulator_sample_zero hγ hτ k

/-- For positive parameters, the regulator derivative at the `k`th sample pole is `-I * γ * τ ^
2 * (-1) ^ k / (2 * cosineSampleAngle k)`. -/
theorem cosineRegulator_deriv_sample {γ τ : ℝ} (hγ : 0 < γ) (hτ : 0 < τ) (k : ℕ) :
    deriv (cosineRegulator γ τ) (cosineSamplePole γ τ k) =
      -I * (γ : ℂ) * (τ : ℂ) ^ 2 * (-1) ^ k / (2 * (cosineSampleAngle k : ℂ)) := by
  have hγc : (γ : ℂ) ≠ 0 := by exact_mod_cast hγ.ne'
  have hτc : (τ : ℂ) ≠ 0 := by exact_mod_cast hτ.ne'
  have hxc : (cosineSampleAngle k : ℂ) ≠ 0 := by
    exact_mod_cast (cosineSampleAngle_pos k).ne'
  let p : ℂ → ℂ := fun q => (-I / ((γ : ℂ) * (τ : ℂ) ^ 2)) * q ^ 2
  have hp : HasDerivAt p
      ((-I / ((γ : ℂ) * (τ : ℂ) ^ 2)) * (2 * (cosineSampleAngle k : ℂ)))
      (cosineSampleAngle k : ℂ) := by
    simpa [p] using!
      ((hasDerivAt_id (cosineSampleAngle k : ℂ)).pow 2).const_mul
        (-I / ((γ : ℂ) * (τ : ℂ) ^ 2))
  have hc := ((cosineRegulator_analytic γ τ (p (cosineSampleAngle k))).differentiableAt.hasDerivAt).comp
    (cosineSampleAngle k : ℂ) hp
  have heq : cosineRegulator γ τ ∘ p = cos := by
    funext q
    exact cosineRegulator_quadratic hγ.ne' hτ.ne' q
  rw [heq] at hc
  have hder := hc.unique (Complex.hasDerivAt_cos (cosineSampleAngle k : ℂ))
  change deriv (cosineRegulator γ τ) (p (cosineSampleAngle k)) *
      ((-I / ((γ : ℂ) * (τ : ℂ) ^ 2)) * (2 * (cosineSampleAngle k : ℂ))) =
    -sin (cosineSampleAngle k : ℂ) at hder
  have hdp : (-I / ((γ : ℂ) * (τ : ℂ) ^ 2)) * (2 * (cosineSampleAngle k : ℂ)) ≠ 0 := by
    exact mul_ne_zero (div_ne_zero (neg_ne_zero.mpr I_ne_zero)
      (mul_ne_zero hγc (pow_ne_zero _ hτc))) (mul_ne_zero (by norm_num) hxc)
  have he : p (cosineSampleAngle k) = cosineSamplePole γ τ k :=
    (cosineSamplePole_quadratic γ τ k).symm
  rw [he, cosineSampleAngle_sin] at hder
  rw [(eq_div_iff hdp).mpr hder]
  field_simp
  ring_nf
  simp [I_sq]

/-- For positive parameters, the regulator derivative is nonzero at every sample pole. -/
theorem cosineRegulator_deriv_sample_ne_zero {γ τ : ℝ} (hγ : 0 < γ) (hτ : 0 < τ) (k : ℕ) :
    deriv (cosineRegulator γ τ) (cosineSamplePole γ τ k) ≠ 0 := by
  rw [cosineRegulator_deriv_sample hγ hτ]
  have hγc : (γ : ℂ) ≠ 0 := by exact_mod_cast hγ.ne'
  have hτc : (τ : ℂ) ≠ 0 := by exact_mod_cast hτ.ne'
  have hxc : (cosineSampleAngle k : ℂ) ≠ 0 := by
    exact_mod_cast (cosineSampleAngle_pos k).ne'
  exact div_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (neg_ne_zero.mpr I_ne_zero) hγc)
    (pow_ne_zero _ hτc)) (pow_ne_zero _ (by norm_num))) (mul_ne_zero (by norm_num) hxc)

/-- The cosine regulator equals one at zero for every pair of real parameters. -/
theorem cosineRegulator_zero (γ τ : ℝ) : cosineRegulator γ τ 0 = 1 := by
  simp only [cosineRegulator, wavePropagator, mul_zero, smul_zero]
  change (∑' n : ℕ, (((2 * n).factorial : ℂ)⁻¹) • (0 : ℂ) ^ n) = 1
  rw [tsum_eq_single 0]
  · simp
  · intro n hn
    simp [zero_pow hn]

/-- For positive parameters, every cosine sample pole is nonzero. -/
theorem cosineSamplePole_ne_zero {γ τ : ℝ} (hγ : 0 < γ) (hτ : 0 < τ) (k : ℕ) :
    cosineSamplePole γ τ k ≠ 0 := by
  apply mul_ne_zero (neg_ne_zero.mpr I_ne_zero)
  exact_mod_cast (cosineSampleScale_pos hγ hτ k).ne'

/-- No cosine sample pole equals one for any real parameters. -/
theorem cosineSamplePole_ne_one (γ τ : ℝ) (k : ℕ) : cosineSamplePole γ τ k ≠ 1 := by
  intro h
  have hr := congrArg Complex.re h
  simp [cosineSamplePole] at hr

/-- For positive parameters, the cosine regulator is nonzero at one. -/
theorem cosineRegulator_one_ne_zero {γ τ : ℝ} (hγ : 0 < γ) (hτ : 0 < τ) :
    cosineRegulator γ τ 1 ≠ 0 := by
  intro h
  obtain ⟨k, hk⟩ := (cosineRegulator_eq_zero_iff hγ hτ 1).mp h
  exact cosineSamplePole_ne_one γ τ k hk.symm

/-- The cosine contour denominator is complex analytic at every point for all real parameters. -/
theorem cosineContourDenominator_analytic (γ τ : ℝ) (z : ℂ) :
    AnalyticAt ℂ (cosineContourDenominator γ τ) z :=
  (analyticAt_id.mul (analyticAt_id.sub analyticAt_const)).mul (cosineRegulator_analytic γ τ z)

/-- The cosine contour denominator has derivative `-1` at zero. -/
theorem cosineContourDenominator_deriv_zero (γ τ : ℝ) :
    deriv (cosineContourDenominator γ τ) 0 = -1 := by
  have h := (((hasDerivAt_id (0 : ℂ)).mul ((hasDerivAt_id (0 : ℂ)).sub_const 1)).mul
    (cosineRegulator_analytic γ τ 0).differentiableAt.hasDerivAt).deriv
  simpa only [Pi.mul_apply, id_eq, zero_sub, zero_mul, add_zero, mul_zero, one_mul,
    cosineRegulator_zero, mul_one] using! h

/-- The derivative of the cosine contour denominator at one equals the regulator value at one. -/
theorem cosineContourDenominator_deriv_one (γ τ : ℝ) :
    deriv (cosineContourDenominator γ τ) 1 = cosineRegulator γ τ 1 := by
  have h := (((hasDerivAt_id (1 : ℂ)).mul ((hasDerivAt_id (1 : ℂ)).sub_const 1)).mul
    (cosineRegulator_analytic γ τ 1).differentiableAt.hasDerivAt).deriv
  simpa only [Pi.mul_apply, id_eq, sub_self, zero_mul, add_zero, mul_zero, one_mul,
      zero_add] using! h

/-- For positive parameters, the contour denominator derivative at the `k`th sample pole is
`(-1) ^ k * cosineSampleAngle k / 2 * (1 + I * cosineSampleScale γ τ k)`. -/
theorem cosineContourDenominator_deriv_sample {γ τ : ℝ} (hγ : 0 < γ) (hτ : 0 < τ) (k : ℕ) :
    deriv (cosineContourDenominator γ τ) (cosineSamplePole γ τ k) =
      (-1) ^ k * (cosineSampleAngle k : ℂ) / 2 * (1 + I * (cosineSampleScale γ τ k : ℂ)) := by
  have h := (((hasDerivAt_id (cosineSamplePole γ τ k)).mul
    ((hasDerivAt_id (cosineSamplePole γ τ k)).sub_const 1)).mul
    (cosineRegulator_analytic γ τ (cosineSamplePole γ τ k)).differentiableAt.hasDerivAt).deriv
  change deriv (cosineContourDenominator γ τ) (cosineSamplePole γ τ k) = _ at h
  rw [h, cosineRegulator_sample_zero hγ hτ, mul_zero, zero_add,
    cosineRegulator_deriv_sample hγ hτ]
  have hγc : (γ : ℂ) ≠ 0 := by exact_mod_cast hγ.ne'
  have hτc : (τ : ℂ) ≠ 0 := by exact_mod_cast hτ.ne'
  have hxc : (cosineSampleAngle k : ℂ) ≠ 0 := by
    exact_mod_cast (cosineSampleAngle_pos k).ne'
  simp only [cosineSamplePole, cosineSampleScale, ofReal_div, ofReal_pow, ofReal_mul, Pi.mul_apply,
      id_eq]
  field_simp
  ring_nf
  simp [I_sq]
  ring

end CBMD

end
end Qatlib.Foundations.CbmdAnalysis.Core
