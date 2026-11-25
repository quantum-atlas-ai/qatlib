/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Papers.KnottedLight08.CurlEigenstate.HopfTimeKernel
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Sinc

import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith

/-!
# The radial Hopf pulse kernel at the origin

The radial sine factor in the spectral integral extends continuously to
zero radius as `k * sinc (rk)`. Dominated convergence gives the same
rational profile at every radius.
-/

@[expose] public section
set_option autoImplicit false

namespace Qatlib.Papers.KnottedLight08.CurlEigenstate

open Filter MeasureTheory Set

/-- The complex spectral denominator has no zeros at real radius and time. -/
theorem hopf_time_radial_denominator_ne_zero (r t : ℝ) :
    (1 + Complex.I * (t : ℂ)) ^ 2 + (r : ℂ) ^ 2 ≠ 0 := by
  intro he
  have him := congrArg Complex.im he
  simp [pow_two, Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im] at him
  have ht : t = 0 := by linarith
  subst t
  have hre := congrArg Complex.re he
  simp [pow_two, Complex.add_re, Complex.mul_re] at hre
  nlinarith [sq_nonneg r]

/-- The time-phased radial integral across the whole real radius range,
with the value at zero supplied by the sinc kernel. -/
theorem integral_hopf_time_radial (r t : ℝ) :
    (∫ k in Ioi (0 : ℝ), Complex.exp (-(1 + Complex.I * (t : ℂ)) * (k : ℂ)) *
      ((k * Real.sinc (r * k) : ℝ) : ℂ)) =
      1 / ((1 + Complex.I * (t : ℂ)) ^ 2 + (r : ℂ) ^ 2) := by
  let z : ℂ := 1 + Complex.I * (t : ℂ)
  let μ := volume.restrict (Ioi (0 : ℝ))
  let F := fun r k : ℝ => Complex.exp (-z * (k : ℂ)) * ((k * Real.sinc (r * k) : ℝ) : ℂ)
  let G := fun r : ℝ => (1 : ℂ) / (z ^ 2 + (r : ℂ) ^ 2)
  have hz : z.re = 1 := by
    simp [z, Complex.add_re, Complex.mul_re]
  have hD (r : ℝ) : z ^ 2 + (r : ℂ) ^ 2 ≠ 0 := hopf_time_radial_denominator_ne_zero r t
  have hG : Continuous G :=
    continuous_const.div (continuous_const.add (Complex.continuous_ofReal.pow 2)) hD
  have hF : Continuous (fun r : ℝ => ∫ k, F r k ∂μ) := by
    apply continuous_of_dominated (bound := fun k : ℝ => Real.exp (-k) * k)
    · intro r
      have hs : Continuous (fun k : ℝ => Real.sinc (r * k)) :=
        Real.continuous_sinc.comp (continuous_const.mul continuous_id)
      exact ((Complex.continuous_exp.comp (continuous_const.mul Complex.continuous_ofReal)).mul
        (Complex.continuous_ofReal.comp (continuous_id.mul hs))).aestronglyMeasurable
    · intro r
      filter_upwards [ae_restrict_mem (μ := volume) measurableSet_Ioi] with k hk
      have hk₀ : 0 < k := hk
      have hRe : (-z * (k : ℂ)).re = -k := by
        rw [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero,
          Complex.neg_re, hz, neg_one_mul]
      change ‖Complex.exp (-z * (k : ℂ)) * ((k * Real.sinc (r * k) : ℝ) : ℂ)‖ ≤ _
      rw [norm_mul, Complex.norm_exp, hRe, Complex.norm_real, Real.norm_eq_abs, abs_mul,
        abs_of_pos hk₀]
      exact mul_le_mul_of_nonneg_left
        (mul_le_of_le_one_right hk₀.le (Real.abs_sinc_le_one _)) (Real.exp_pos _).le
    · change IntegrableOn (fun k : ℝ => Real.exp (-k) * k) (Ioi 0)
      simpa [show (2 : ℝ) - 1 = 1 by norm_num, Real.rpow_one] using
        (Real.GammaIntegral_convergent (s := 2) (by norm_num))
    · exact Eventually.of_forall fun k =>
        continuous_const.mul (Complex.continuous_ofReal.comp
          (continuous_const.mul (Real.continuous_sinc.comp (continuous_id.mul_const k))))
  have he : EqOn (fun r : ℝ => ∫ k, F r k ∂μ) G ({0}ᶜ : Set ℝ) := by
    intro r hr
    have hr₀ : r ≠ 0 := hr
    have hrC : (r : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hr₀
    have hEq : F r = fun k : ℝ =>
        (Complex.exp (-z * (k : ℂ)) * (Real.sin (r * k) : ℂ)) / (r : ℂ) := by
      funext k
      by_cases hk : k = 0
      · simp [F, hk]
      · have hR : k * Real.sinc (r * k) = Real.sin (r * k) / r := by
          rw [Real.sinc_of_ne_zero (mul_ne_zero hr₀ hk)]
          field_simp [hr₀, hk]
        change Complex.exp (-z * (k : ℂ)) * ((k * Real.sinc (r * k) : ℝ) : ℂ) = _
        rw [hR, Complex.ofReal_div, mul_div_assoc]
    change (∫ k, F r k ∂μ) = G r
    rw [hEq, integral_div]
    change ((∫ k in Ioi (0 : ℝ), Complex.exp (-z * (k : ℂ)) * (Real.sin (r * k) : ℂ)) /
      (r : ℂ)) = G r
    rw [integral_hopf_time_mul_sin]
    change ((r : ℂ) / (z ^ 2 + (r : ℂ) ^ 2)) / (r : ℂ) = 1 / (z ^ 2 + (r : ℂ) ^ 2)
    field_simp [hrC, hD r]
  exact congrFun (Continuous.ext_on (dense_compl_singleton (0 : ℝ)) hF hG he) r

end Qatlib.Papers.KnottedLight08.CurlEigenstate
