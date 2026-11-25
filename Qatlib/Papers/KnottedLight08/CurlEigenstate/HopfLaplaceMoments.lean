/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals

import Mathlib.Analysis.Complex.RealDeriv
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring

/-!
# Complex Laplace moments for the Hopf pulse

The frequency integrals in the dipole multipole and its curl use
polynomial weights against a damped complex exponential. Both the
absolute convergence and the moment formula hold throughout the
right half-plane.
-/

@[expose] public section
set_option autoImplicit false

namespace Qatlib.Papers.KnottedLight08.CurlEigenstate

open Filter MeasureTheory Set
open scoped Topology

/-- Every polynomial complex Laplace moment is absolutely integrable
when the real part of the damping parameter is positive. -/
theorem integrableOn_hopf_laplace_moment {a : ℂ} (ha : 0 < a.re) (n : ℕ) :
    IntegrableOn (fun x : ℝ => (x : ℂ) ^ n * Complex.exp (-a * (x : ℂ))) (Ioi 0) := by
  have hΓ : IntegrableOn (fun x : ℝ => Real.exp (-x) * x ^ n) (Ioi 0) := by
    have hn : 0 < (n : ℝ) + 1 := by positivity
    simpa only [add_sub_cancel_right, Real.rpow_natCast] using Real.GammaIntegral_convergent hn
  have hΓ' : IntegrableOn (fun x : ℝ => Real.exp (-(a.re * x)) * (a.re * x) ^ n)
      (Ioi 0) := by
    refine (integrableOn_Ioi_comp_mul_left_iff (fun x : ℝ => Real.exp (-x) * x ^ n) 0 ha).2 ?_
    simpa only [mul_zero] using hΓ
  have hc : Continuous (fun x : ℝ => (x : ℂ) ^ n * Complex.exp (-a * (x : ℂ))) := by
    fun_prop
  refine (integrable_norm_iff hc.aestronglyMeasurable).1 ?_
  have hscaled : IntegrableOn
      (fun x : ℝ => (a.re ^ n)⁻¹ * (Real.exp (-(a.re * x)) * (a.re * x) ^ n)) (Ioi 0) :=
    hΓ'.const_mul _
  refine hscaled.congr_fun ?_ measurableSet_Ioi
  intro x hx
  change (a.re ^ n)⁻¹ * (Real.exp (-(a.re * x)) * (a.re * x) ^ n) =
    ‖(x : ℂ) ^ n * Complex.exp (-a * (x : ℂ))‖
  have hre : (-a * (x : ℂ)).re = -(a.re * x) := by
    simp [Complex.mul_re]
  rw [norm_mul, norm_pow, Complex.norm_real, Real.norm_of_nonneg hx.le,
    Complex.norm_exp, hre, mul_pow]
  field_simp [ha.ne']

/-- The exact polynomial Laplace moment for a complex damping parameter. -/
theorem integral_hopf_laplace_moment {a : ℂ} (ha : 0 < a.re) (n : ℕ) :
    (∫ x in Ioi (0 : ℝ), (x : ℂ) ^ n * Complex.exp (-a * (x : ℂ))) =
      (n.factorial : ℂ) / a ^ (n + 1) := by
  have ha₀ : a ≠ 0 := by
    intro h
    simp [h] at ha
  induction n with
  | zero =>
    simp only [pow_zero, one_mul, Nat.factorial_zero, Nat.cast_one, zero_add, pow_one]
    rw [integral_exp_mul_complex_Ioi (a := -a) (by simpa)]
    simp
  | succ n ih =>
    let f := fun x : ℝ => (x : ℂ) ^ (n + 1) * Complex.exp (-a * (x : ℂ))
    let g := fun x : ℝ => (x : ℂ) ^ n * Complex.exp (-a * (x : ℂ))
    let c : ℂ := (n : ℂ) + 1
    have hderiv (x : ℝ) : HasDerivAt f (c * g x + -a * f x) x := by
      have hx : HasDerivAt (fun s : ℝ => (s : ℂ)) (1 : ℂ) x := (hasDerivAt_id x).ofReal_comp
      refine ((hx.pow (n + 1)).mul ((hx.const_mul (-a)).cexp)).congr_deriv ?_
      simp only [Pi.pow_apply, Nat.add_sub_cancel, Nat.cast_add, Nat.cast_one, mul_one]
      dsimp only [c, f, g]
      ring
    have hlim : Tendsto f atTop (𝓝 0) := by
      rw [tendsto_zero_iff_norm_tendsto_zero]
      refine (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero
        ((n + 1 : ℕ) : ℝ) a.re ha).congr' ?_
      filter_upwards [eventually_ge_atTop (0 : ℝ)] with x hx
      simp [f, norm_pow, Complex.norm_real, Real.norm_of_nonneg hx,
        Complex.norm_exp, Complex.mul_re]
      simpa only [Nat.cast_add, Nat.cast_one] using Real.rpow_natCast x (n + 1)
    have hgn : IntegrableOn g (Ioi 0) := integrableOn_hopf_laplace_moment ha n
    have hfn : IntegrableOn f (Ioi 0) := integrableOn_hopf_laplace_moment ha (n + 1)
    have hD := integral_Ioi_of_hasDerivAt_of_tendsto' (a := 0) (fun x _ => hderiv x)
      ((hgn.const_mul c).add (hfn.const_mul (-a))) hlim
    have hf₀ : f 0 = 0 := by simp [f]
    rw [hf₀, sub_zero, integral_add (hgn.const_mul c) (hfn.const_mul (-a)),
      integral_const_mul, integral_const_mul] at hD
    have hgval : (∫ x in Ioi (0 : ℝ), g x) = (n.factorial : ℂ) / a ^ (n + 1) := ih
    rw [hgval] at hD
    have hstep : a * (∫ x in Ioi (0 : ℝ), f x) =
        c * ((n.factorial : ℂ) / a ^ (n + 1)) := by
      linear_combination -hD
    change (∫ x in Ioi (0 : ℝ), f x) = ((n + 1).factorial : ℂ) / a ^ (n + 1 + 1)
    apply (eq_div_iff (pow_ne_zero _ ha₀)).2
    rw [pow_succ, Nat.factorial_succ, Nat.cast_mul, Nat.cast_add, Nat.cast_one]
    change (∫ x in Ioi (0 : ℝ), f x) * (a ^ (n + 1) * a) = c * (n.factorial : ℂ)
    calc
      _ = (a * (∫ x in Ioi (0 : ℝ), f x)) * a ^ (n + 1) := by ring
      _ = _ := by
        rw [hstep, mul_assoc, div_mul_cancel₀ _ (pow_ne_zero _ ha₀)]

end Qatlib.Papers.KnottedLight08.CurlEigenstate
