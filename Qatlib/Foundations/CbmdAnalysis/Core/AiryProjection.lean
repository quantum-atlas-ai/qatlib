/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Foundations.CbmdAnalysis.Core.MatrixODE
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.RingTheory.RootsOfUnity.Complex

/-!
# Airy functions and cubic projection

This module defines `airyAi` from its two convergent power-series branches and the
gamma-function values of its initial data. Averaging over the cubic roots of unity defines
`airyProjection`, which retains the branch with exponents divisible by three and is identified
with a normalized Airy propagator. This supplies the scalar projection and normalization used in
[WangEtAl2026].

## Main statements

* `airyAi_analytic`: the defined Airy function is analytic at every complex point.
* `airyProjection_eq_series`: cubic projection selects the first series branch.
* `airyProjection_normalized`: division by the value at zero gives `airyPropagator (z ^ 3) 1`.

## References

* [Wang et al., 2026][WangEtAl2026]
-/

set_option warningAsError false

namespace Qatlib.Foundations.CbmdAnalysis.Core

set_option autoImplicit false
noncomputable section
namespace CBMD
open Complex Filter
open scoped Topology BigOperators

/-- The ratio of successive complex norms of the first Airy coefficients equals `((3 * n + 3) *
(3 * n + 2))⁻¹`. -/
private theorem airy_coefficient_ratio (n : ℕ) :
    ‖(airySeriesCoefficient (n + 1) : ℂ)‖ / ‖(airySeriesCoefficient n : ℂ)‖ =
      ((3 * (n : ℝ) + 3) * (3 * (n : ℝ) + 2))⁻¹ := by
  rw [Complex.norm_real, Complex.norm_real,
    Real.norm_of_nonneg (airySeriesCoefficient_pos _).le,
    Real.norm_of_nonneg (airySeriesCoefficient_pos _).le, airySeriesCoefficient_step]
  have ha := ne_of_gt (airySeriesCoefficient_pos n)
  have h1 : 3 * (n : ℝ) + 3 ≠ 0 := by positivity
  have h2 : 3 * (n : ℝ) + 2 ≠ 0 := by positivity
  field_simp

/-- The ratio of successive norms of the first Airy coefficients tends to zero. -/
private theorem airy_coefficient_ratio_tendsto :
    Tendsto (fun n : ℕ => ‖(airySeriesCoefficient n.succ : ℂ)‖ /
      ‖(airySeriesCoefficient n : ℂ)‖) atTop (𝓝 0) := by
  simp_rw [Nat.succ_eq_add_one, airy_coefficient_ratio]
  have hn : Tendsto (fun n : ℕ => (n : ℝ)) atTop atTop := tendsto_natCast_atTop_atTop
  have hm : Tendsto (fun n : ℕ => 3 * (n : ℝ)) atTop atTop :=
    hn.const_mul_atTop (by norm_num)
  have h3 := tendsto_atTop_add_const_right atTop (3 : ℝ) hm
  have h2 := tendsto_atTop_add_const_right atTop (2 : ℝ) hm
  exact tendsto_inv_atTop_zero.comp (h3.atTop_mul_atTop₀ h2)

/-- The Airy initial value `1 / (3 ^ (2 / 3) * Gamma (2 / 3))`. -/
def airyAi0 : ℝ := 1 / ((3 : ℝ) ^ (2 / 3 : ℝ) * Real.Gamma (2 / 3))

/-- The Airy initial derivative `-1 / (3 ^ (1 / 3) * Gamma (1 / 3))`. -/
def airyAiPrime0 : ℝ := -(1 / ((3 : ℝ) ^ (1 / 3 : ℝ) * Real.Gamma (1 / 3)))

/-- The Airy initial value `airyAi0` is strictly positive. -/
theorem airyAi0_pos : 0 < airyAi0 := by
  unfold airyAi0
  positivity

/-- The Airy initial derivative `airyAiPrime0` is strictly negative. -/
theorem airyAiPrime0_neg : airyAiPrime0 < 0 := by
  unfold airyAiPrime0
  exact neg_lt_zero.mpr (by positivity)

/-- The coefficient `1 / (9 ^ n * n! * (4 / 3)ₙ)` of the second Airy series branch, using the
rising factorial. -/
def airySecondCoefficient (n : ℕ) : ℝ :=
  ((9 : ℝ) ^ n * (n.factorial : ℝ) * (ascPochhammer ℝ n).eval (4 / 3))⁻¹

/-- The zeroth coefficient of the second Airy branch is one. -/
@[simp] theorem airySecondCoefficient_zero : airySecondCoefficient 0 = 1 := by
  simp [airySecondCoefficient]

/-- Every coefficient of the second Airy branch is strictly positive. -/
theorem airySecondCoefficient_pos (n : ℕ) : 0 < airySecondCoefficient n := by
  have hp := ascPochhammer_pos n (4 / 3 : ℝ) (by norm_num)
  have hf : (0 : ℝ) < (n.factorial : ℝ) := by exact_mod_cast Nat.factorial_pos n
  unfold airySecondCoefficient
  positivity

/-- Successive second-branch coefficients satisfy division by `(3 * n + 3) * (3 * n + 4)`. -/
theorem airySecondCoefficient_step (n : ℕ) :
    airySecondCoefficient (n + 1) =
      airySecondCoefficient n / ((3 * (n : ℝ) + 3) * (3 * (n : ℝ) + 4)) := by
  unfold airySecondCoefficient
  rw [pow_succ, Nat.factorial_succ, ascPochhammer_succ_eval,
    Nat.cast_mul, Nat.cast_add, Nat.cast_one]
  have hp := ne_of_gt (ascPochhammer_pos n (4 / 3 : ℝ) (by norm_num))
  have hf : (n.factorial : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero n)
  have hn : (n : ℝ) + 1 ≠ 0 := by positivity
  have h1 : 3 * (n : ℝ) + 3 ≠ 0 := by positivity
  have h2 : 3 * (n : ℝ) + 4 ≠ 0 := by positivity
  have h3 : 4 / 3 + (n : ℝ) ≠ 0 := by positivity
  field_simp
  ring

/-- The ratio of successive complex norms of second-branch coefficients is `((3 * n + 3) * (3 *
n + 4))⁻¹`. -/
private theorem airySecondCoefficient_ratio (n : ℕ) :
    ‖(airySecondCoefficient (n + 1) : ℂ)‖ / ‖(airySecondCoefficient n : ℂ)‖ =
      ((3 * (n : ℝ) + 3) * (3 * (n : ℝ) + 4))⁻¹ := by
  rw [Complex.norm_real, Complex.norm_real,
    Real.norm_of_nonneg (airySecondCoefficient_pos _).le,
    Real.norm_of_nonneg (airySecondCoefficient_pos _).le, airySecondCoefficient_step]
  have ha := ne_of_gt (airySecondCoefficient_pos n)
  have h1 : 3 * (n : ℝ) + 3 ≠ 0 := by positivity
  have h2 : 3 * (n : ℝ) + 4 ≠ 0 := by positivity
  field_simp

/-- The ratio of successive norms of second-branch coefficients tends to zero. -/
private theorem airySecondCoefficient_ratio_tendsto :
    Tendsto (fun n : ℕ => ‖(airySecondCoefficient n.succ : ℂ)‖ /
      ‖(airySecondCoefficient n : ℂ)‖) atTop (𝓝 0) := by
  simp_rw [Nat.succ_eq_add_one, airySecondCoefficient_ratio]
  have hn : Tendsto (fun n : ℕ => (n : ℝ)) atTop atTop := tendsto_natCast_atTop_atTop
  have hm : Tendsto (fun n : ℕ => 3 * (n : ℝ)) atTop atTop :=
    hn.const_mul_atTop (by norm_num)
  have h3 := tendsto_atTop_add_const_right atTop (3 : ℝ) hm
  have h4 := tendsto_atTop_add_const_right atTop (4 : ℝ) hm
  exact tendsto_inv_atTop_zero.comp (h3.atTop_mul_atTop₀ h4)

/-- Both Airy coefficient series in powers of `z ^ 3` are summable at every complex `z`. -/
theorem airyAi_branches_summable (z : ℂ) :
    Summable (fun n : ℕ => (airySeriesCoefficient n : ℂ) * (z ^ 3) ^ n) ∧
    Summable (fun n : ℕ => (airySecondCoefficient n : ℂ) * (z ^ 3) ^ n) := by
  constructor
  · exact scalarSeries_summable_of_ratio_zero (fun n => (airySeriesCoefficient n : ℂ))
      (Eventually.of_forall (fun n => ofReal_ne_zero.mpr (airySeriesCoefficient_pos n).ne'))
      Qatlib.Foundations.CbmdAnalysis.Core.CBMD.airy_coefficient_ratio_tendsto (z ^ 3)
  · exact scalarSeries_summable_of_ratio_zero (fun n => (airySecondCoefficient n : ℂ))
      (Eventually.of_forall (fun n => ofReal_ne_zero.mpr (airySecondCoefficient_pos n).ne'))
      airySecondCoefficient_ratio_tendsto (z ^ 3)

/-- The complex Airy function defined by its two power-series branches and initial constants
`airyAi0` and `airyAiPrime0`. -/
def airyAi (z : ℂ) : ℂ :=
  (airyAi0 : ℂ) * (∑' n : ℕ, (airySeriesCoefficient n : ℂ) * (z ^ 3) ^ n) +
    (airyAiPrime0 : ℂ) * z *
      (∑' n : ℕ, (airySecondCoefficient n : ℂ) * (z ^ 3) ^ n)

/-- The Airy function is the sum of its initial-value branch in powers `z ^ (3 * n)` and its
initial-derivative branch multiplied by `z`. -/
theorem airyAi_series (z : ℂ) :
    airyAi z =
      (airyAi0 : ℂ) * (∑' n : ℕ, (airySeriesCoefficient n : ℂ) * z ^ (3 * n)) +
      (airyAiPrime0 : ℂ) * z *
        (∑' n : ℕ, (airySecondCoefficient n : ℂ) * z ^ (3 * n)) := by
  simp only [airyAi, pow_mul]

/-- The function `airyAi` is complex analytic at every point. -/
theorem airyAi_analytic (z : ℂ) : AnalyticAt ℂ airyAi z := by
  have ha := scalarSeries_analytic_of_ratio_zero (fun n => (airySeriesCoefficient n : ℂ))
    (Eventually.of_forall (fun n => ofReal_ne_zero.mpr (airySeriesCoefficient_pos n).ne'))
    Qatlib.Foundations.CbmdAnalysis.Core.CBMD.airy_coefficient_ratio_tendsto (z ^ 3)
  have hb := scalarSeries_analytic_of_ratio_zero (fun n => (airySecondCoefficient n : ℂ))
    (Eventually.of_forall (fun n => ofReal_ne_zero.mpr (airySecondCoefficient_pos n).ne'))
    airySecondCoefficient_ratio_tendsto (z ^ 3)
  exact (analyticAt_const.mul (ha.comp (f := fun w : ℂ => w ^ 3) (analyticAt_id.pow 3))).add
    ((analyticAt_const.mul analyticAt_id).mul (hb.comp (f := fun w : ℂ => w ^ 3) (analyticAt_id.pow 3)))

/-- The value of `airyAi` at zero is `airyAi0`. -/
@[simp] theorem airyAi_zero : airyAi 0 = (airyAi0 : ℂ) := by
  have ht : (∑' n : ℕ, (airySeriesCoefficient n : ℂ) * (0 : ℂ) ^ n) = 1 := by
    rw [tsum_eq_single 0]
    · simp
    · intro n hn
      simp [zero_pow hn]
  simp only [airyAi, zero_pow (by norm_num : 3 ≠ 0), mul_zero, zero_mul, add_zero,
    ht, mul_one]

/-- The Airy function has derivative `airyAiPrime0` at zero. -/
theorem airyAi_hasDerivAt_zero : HasDerivAt airyAi (airyAiPrime0 : ℂ) 0 := by
  have ha := scalarSeries_analytic_of_ratio_zero (fun n => (airySeriesCoefficient n : ℂ))
    (Eventually.of_forall (fun n => ofReal_ne_zero.mpr (airySeriesCoefficient_pos n).ne'))
    Qatlib.Foundations.CbmdAnalysis.Core.CBMD.airy_coefficient_ratio_tendsto ((0 : ℂ) ^ 3)
  have hb := scalarSeries_analytic_of_ratio_zero (fun n => (airySecondCoefficient n : ℂ))
    (Eventually.of_forall (fun n => ofReal_ne_zero.mpr (airySecondCoefficient_pos n).ne'))
    airySecondCoefficient_ratio_tendsto ((0 : ℂ) ^ 3)
  have hc : HasDerivAt (fun z : ℂ => z ^ 3) 0 0 := by
    simpa using! (hasDerivAt_id (0 : ℂ)).pow 3
  have hA : HasDerivAt
      (fun z : ℂ => ∑' n : ℕ, (airySeriesCoefficient n : ℂ) * (z ^ 3) ^ n) 0 0 := by
    simpa only [Function.comp_def, mul_zero] using!
      ha.differentiableAt.hasDerivAt.comp 0 (h := fun z : ℂ => z ^ 3) hc
  have hB : HasDerivAt
      (fun z : ℂ => ∑' n : ℕ, (airySecondCoefficient n : ℂ) * (z ^ 3) ^ n) 0 0 := by
    simpa only [Function.comp_def, mul_zero] using!
      hb.differentiableAt.hasDerivAt.comp 0 (h := fun z : ℂ => z ^ 3) hc
  have ht : (∑' n : ℕ, (airySecondCoefficient n : ℂ) * (0 : ℂ) ^ n) = 1 := by
    rw [tsum_eq_single 0]
    · simp
    · intro n hn
      simp [zero_pow hn]
  have h := ((hasDerivAt_const (0 : ℂ) (airyAi0 : ℂ)).mul hA).add
    (((hasDerivAt_const (0 : ℂ) (airyAiPrime0 : ℂ)).mul (hasDerivAt_id (0 : ℂ))).mul hB)
  simpa only [zero_mul, mul_zero, zero_add, add_zero, mul_one,
    zero_pow (by norm_num : 3 ≠ 0), ht, airyAi] using! h

/-- The derivative of `airyAi` at zero equals `airyAiPrime0`. -/
@[simp] theorem airyAi_deriv_zero : deriv airyAi 0 = (airyAiPrime0 : ℂ) :=
  airyAi_hasDerivAt_zero.deriv

/-- The complex number `exp (2 * π * I / 3)` used for cubic root-of-unity projection. -/
def airyOmega : ℂ := Complex.exp (2 * (Real.pi : ℂ) * I / 3)

/-- The number `airyOmega` is a primitive third root of unity. -/
theorem airyOmega_isPrimitiveRoot : IsPrimitiveRoot airyOmega 3 :=
  Complex.isPrimitiveRoot_exp 3 (by norm_num)

/-- The cube of `airyOmega` is one. -/
theorem airyOmega_cube : airyOmega ^ 3 = 1 := airyOmega_isPrimitiveRoot.pow_eq_one

/-- The three powers `1`, `airyOmega`, and `airyOmega ^ 2` sum to zero. -/
theorem airyOmega_sum : 1 + airyOmega + airyOmega ^ 2 = 0 := by
  have hmul : (airyOmega - 1) * (1 + airyOmega + airyOmega ^ 2) = 0 := by
    calc
      _ = airyOmega ^ 3 - 1 := by ring
      _ = 0 := by rw [airyOmega_cube]; ring
  exact (mul_eq_zero.mp hmul).resolve_left (sub_ne_zero.mpr
    (airyOmega_isPrimitiveRoot.ne_one (by norm_num)))

/-- The average of `airyAi` at `-z`, `-airyOmega * z`, and `-airyOmega ^ 2 * z`. -/
def airyProjection (z : ℂ) : ℂ :=
  (airyAi (-z) + airyAi (-airyOmega * z) + airyAi (-airyOmega ^ 2 * z)) / 3

/-- The cubic Airy projection equals `airyAi0` times the first Airy coefficient series in powers
of `-z ^ 3`. -/
theorem airyProjection_eq_series (z : ℂ) :
    airyProjection z =
      (airyAi0 : ℂ) * ∑' n : ℕ, (airySeriesCoefficient n : ℂ) * (-z ^ 3) ^ n := by
  have h1 : (-z) ^ 3 = -z ^ 3 := by ring
  have h2 : (-airyOmega * z) ^ 3 = -z ^ 3 := by
    rw [mul_pow, neg_pow, airyOmega_cube]
    ring
  have h3 : (-airyOmega ^ 2 * z) ^ 3 = -z ^ 3 := by
    rw [mul_pow, neg_pow, ← pow_mul, show 2 * 3 = 3 * 2 from rfl, pow_mul,
      airyOmega_cube]
    ring
  unfold airyProjection airyAi
  rw [h1, h2, h3]
  have hc := airyOmega_sum
  linear_combination
    -((airyAiPrime0 : ℂ) * z *
      (∑' n : ℕ, (airySecondCoefficient n : ℂ) * (-z ^ 3) ^ n) / 3) * hc

/-- The cubic Airy projection equals `airyAi0` times `airyPropagator (z ^ 3) 1`. -/
theorem airyProjection_eq_propagator (z : ℂ) :
    airyProjection z = (airyAi0 : ℂ) * airyPropagator (z ^ 3) 1 := by
  rw [airyProjection_eq_series]
  simp only [airyPropagator, one_pow, smul_eq_mul, neg_one_mul]

/-- The cubic Airy projection at zero equals `airyAi0`. -/
@[simp] theorem airyProjection_zero : airyProjection 0 = (airyAi0 : ℂ) := by
  simp only [airyProjection, neg_zero, mul_zero, airyAi_zero]
  ring

/-- The norm of the cubic Airy projection at zero is `airyAi0`. -/
theorem airyProjection_zero_norm : ‖airyProjection 0‖ = airyAi0 := by
  rw [airyProjection_zero, Complex.norm_real, Real.norm_of_nonneg airyAi0_pos.le]

/-- Dividing the cubic Airy projection by its value at zero gives `airyPropagator (z ^ 3) 1`. -/
theorem airyProjection_normalized (z : ℂ) :
    airyProjection z / airyProjection 0 = airyPropagator (z ^ 3) 1 := by
  rw [airyProjection_eq_propagator, airyProjection_zero]
  exact mul_div_cancel_left₀ _ (Complex.ofReal_ne_zero.mpr airyAi0_pos.ne')

/-- The norm of the cubic Airy projection is `airyAi0` times the norm of `airyPropagator (z ^ 3)
1`. -/
theorem airyProjection_norm (z : ℂ) :
    ‖airyProjection z‖ = airyAi0 * ‖airyPropagator (z ^ 3) 1‖ := by
  rw [airyProjection_eq_propagator, norm_mul, Complex.norm_real,
    Real.norm_of_nonneg airyAi0_pos.le]

end CBMD

end
end Qatlib.Foundations.CbmdAnalysis.Core
