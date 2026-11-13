/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

set_option backward.isDefEq.respectTransparency false

/-!
# Smooth Initialization `L²` Derivative Growth for Schrödingerization

This module formalizes Theorem 3.1: for a smooth Schrödingerization auxiliary
profile `ψ` supported on `[-(1 + 2r), ∞)` whose `r`-th derivative satisfies the
cutoff-exponential bound `|ψ^{(r)}(p)| ≤ 40^r r^{1/2} (2r)^{2r} e^{-p}`, the
root-`L²` seminorm `(∫_ℝ |ψ^{(r)}|^2)^{1/(2r)}` is bounded by `8000 r^2`.

## Main statements

* `theorem_three_one_smooth_initialization`: `L²` integration and `1/(2r)`-th
  root estimate `(∫ p, (iteratedDeriv r ψ p)^2)^{1/(2r)} ≤ 8000 * r^2`.

## References

* [Jin et al., 2025][JinEtAl2025Schrodinger], Section 3, Theorem 3.1, p. 18.
-/

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.Schrodinger25.MainResults.Initialization

/-- **Theorem 3.1**: if `iteratedDeriv r ψ` vanishes on `(-∞, -(1 + 2r))` and
satisfies `|ψ^{(r)}(p)| ≤ 40^r r^{1/2} (2r)^{2r} e^{-p}` on `[-(1 + 2r), ∞)` for
`r ≥ 1`, then `(∫ p, (iteratedDeriv r ψ p)^2)^{1/(2r)} ≤ 8000 r^2`. -/
theorem theorem_three_one_smooth_initialization
    (ψ : ℝ → ℝ) (r : ℕ) (hr : 1 ≤ r)
    (hderiv : ∀ p : ℝ, -(1 + 2 * (r : ℝ)) ≤ p →
      |iteratedDeriv r ψ p| ≤ (40 : ℝ) ^ r * (r : ℝ) ^ (1 / 2 : ℝ)
        * (2 * (r : ℝ)) ^ (2 * (r : ℝ)) * Real.exp (-p))
    (hzero : ∀ p : ℝ, p < -(1 + 2 * (r : ℝ)) → iteratedDeriv r ψ p = 0) :
    (∫ p : ℝ, (iteratedDeriv r ψ p) ^ 2) ^ (1 / (2 * (r : ℝ))) ≤ 8000 * (r : ℝ) ^ 2 := by
  have hr_real : (1 : ℝ) ≤ r := by exact_mod_cast hr
  have hr_pos : (0 : ℝ) < r := lt_of_lt_of_le zero_lt_one hr_real
  have hroot_pos : 0 < 1 / (2 * (r : ℝ)) := by positivity
  by_cases hint : MeasureTheory.Integrable
      (fun p : ℝ => (iteratedDeriv r ψ p) ^ 2) MeasureTheory.volume
  · let a : ℝ := -(1 + 2 * (r : ℝ))
    let C : ℝ := (40 : ℝ) ^ r * (r : ℝ) ^ (1 / 2 : ℝ)
      * (2 * (r : ℝ)) ^ (2 * (r : ℝ))
    have hC_pos : 0 < C := by dsimp [C]; positivity
    let g : ℝ → ℝ := (Set.Ici a).indicator (fun p => C ^ 2 * Real.exp (-2 * p))
    have hexp_int : MeasureTheory.IntegrableOn
        (fun p : ℝ => Real.exp (-2 * p)) (Set.Ici a) :=
      (MeasureTheory.integrableOn_congr_set_ae MeasureTheory.Ioi_ae_eq_Ici).mp
        (integrableOn_exp_mul_Ioi (by norm_num : (-2 : ℝ) < 0) a)
    have hg_int : MeasureTheory.Integrable g MeasureTheory.volume :=
      MeasureTheory.IntegrableOn.integrable_indicator
        (hexp_int.const_mul (C ^ 2)) measurableSet_Ici
    have hg_integral : (∫ p : ℝ, g p) = C ^ 2 * Real.exp (2 + 4 * (r : ℝ)) / 2 := by
      dsimp [g]
      rw [MeasureTheory.integral_indicator measurableSet_Ici,
        MeasureTheory.integral_const_mul, MeasureTheory.integral_Ici_eq_integral_Ioi,
        integral_exp_mul_Ioi (by norm_num : (-2 : ℝ) < 0) a]
      rw [show -2 * a = 2 + 4 * (r : ℝ) by dsimp [a]; ring]
      ring
    have hle : ∀ p : ℝ, (iteratedDeriv r ψ p) ^ 2 ≤ g p := by
      intro p
      dsimp only [g]
      by_cases hp : a ≤ p
      · rw [Set.indicator_of_mem (show p ∈ Set.Ici a from hp)]
        have hd : |iteratedDeriv r ψ p| ≤ C * Real.exp (-p) := hderiv p hp
        have hs := pow_le_pow_left₀ (abs_nonneg (iteratedDeriv r ψ p)) hd 2
        rw [sq_abs, mul_pow, ← Real.exp_nat_mul] at hs
        convert hs using 1
        congr 2
        ring
      · rw [Set.indicator_of_notMem (show p ∉ Set.Ici a from hp),
          hzero p (lt_of_not_ge hp)]
        norm_num
    have hI : (∫ p : ℝ, (iteratedDeriv r ψ p) ^ 2) ≤
        C ^ 2 * Real.exp (2 + 4 * (r : ℝ)) / 2 := by
      rw [← hg_integral]
      exact MeasureTheory.integral_mono hint hg_int hle
    have hhalf : ((r : ℝ) ^ (1 / 2 : ℝ)) ^ 2 = (r : ℝ) := by
      rw [← Real.rpow_two, ← Real.rpow_mul hr_pos.le]
      norm_num
    have hnat : (2 * (r : ℝ)) ^ (2 * (r : ℝ)) =
        (2 * (r : ℝ)) ^ (2 * r : ℕ) := by
      rw [← Real.rpow_natCast]
      norm_cast
    have hC_sq : C ^ 2 = (r : ℝ) * (160 * (r : ℝ) ^ 2) ^ (2 * r) := by
      rw [show 160 * (r : ℝ) ^ 2 = 40 * (2 * (r : ℝ)) ^ 2 by ring]
      simp only [C, mul_pow, hhalf, hnat, ← pow_mul]
      simp only [Nat.mul_comm r 2, Nat.mul_comm (2 * r) 2]
      ring
    have hexp_two : Real.exp 2 ≤ 9 := by
      have he := Real.exp_one_lt_three
      rw [show (2 : ℝ) = 1 + 1 by norm_num, Real.exp_add]
      nlinarith [Real.exp_pos 1]
    have hexp_bound : Real.exp (2 + 4 * (r : ℝ)) ≤ 9 * (9 : ℝ) ^ (2 * r) := by
      rw [show 2 + 4 * (r : ℝ) = 2 + ((2 * r : ℕ) : ℝ) * 2 by push_cast; ring,
        Real.exp_add, Real.exp_nat_mul]
      exact mul_le_mul hexp_two (pow_le_pow_left₀ (Real.exp_pos 2).le hexp_two _)
        (by positivity) (by norm_num)
    have hlinear : ∀ n : ℕ, (9 / 2 : ℝ) * (n : ℝ) ≤ (5 : ℝ) ^ (2 * n) := by
      intro n
      induction n with
      | zero => norm_num
      | succ n ih =>
        have hone : (1 : ℝ) ≤ (5 : ℝ) ^ (2 * n) := one_le_pow₀ (by norm_num)
        rw [Nat.cast_succ, Nat.mul_succ, pow_add]
        norm_num
        nlinarith
    have hbound : C ^ 2 * Real.exp (2 + 4 * (r : ℝ)) / 2 ≤
        (8000 * (r : ℝ) ^ 2) ^ (2 * r : ℕ) := by
      calc
        C ^ 2 * Real.exp (2 + 4 * (r : ℝ)) / 2
            ≤ C ^ 2 * (9 * (9 : ℝ) ^ (2 * r)) / 2 := by
              gcongr
        _ = ((9 / 2 : ℝ) * (r : ℝ)) * (1440 * (r : ℝ) ^ 2) ^ (2 * r) := by
          rw [hC_sq, show 1440 * (r : ℝ) ^ 2 = (160 * (r : ℝ) ^ 2) * 9 by ring,
            mul_pow (160 * (r : ℝ) ^ 2) 9]
          ring
        _ ≤ (5 : ℝ) ^ (2 * r) * (1440 * (r : ℝ) ^ 2) ^ (2 * r) :=
          mul_le_mul_of_nonneg_right (hlinear r) (by positivity)
        _ = (7200 * (r : ℝ) ^ 2) ^ (2 * r) := by rw [← mul_pow]; congr 1; ring
        _ ≤ (8000 * (r : ℝ) ^ 2) ^ (2 * r) := by gcongr; norm_num
    have hI_nonneg : 0 ≤ ∫ p : ℝ, (iteratedDeriv r ψ p) ^ 2 :=
      MeasureTheory.integral_nonneg (fun p => sq_nonneg (iteratedDeriv r ψ p))
    have hroot := Real.rpow_le_rpow hI_nonneg (hI.trans hbound) hroot_pos.le
    have hroot_eq : ((8000 * (r : ℝ) ^ 2) ^ (2 * r : ℕ)) ^
        (1 / (2 * (r : ℝ))) = 8000 * (r : ℝ) ^ 2 := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul (by positivity)]
      rw [show ((2 * r : ℕ) : ℝ) * (1 / (2 * (r : ℝ))) = 1 by
        push_cast; field_simp, Real.rpow_one]
    rwa [hroot_eq] at hroot
  · rw [MeasureTheory.integral_undef hint, Real.zero_rpow hroot_pos.ne']
    positivity

end Qatlib.Papers.Schrodinger25.MainResults.Initialization
