/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Analysis.Calculus.Taylor
import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Qatlib.Concepts.SignalPrimitive.GridGradient.GridGradientConsumers
set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false
noncomputable section

open scoped BigOperators
open Set

namespace Qatlib.Concepts.GradientOracle.C2GradientAlg

lemma taylor_one_eval (f : ℝ → ℝ) (s : Set ℝ) (x y : ℝ) :
    taylorWithinEval f 1 s x y = f x + iteratedDerivWithin 1 f s x * (y - x) := by
  rw [taylorWithinEval_succ, taylor_within_zero_eval]
  simp
  ring

lemma within_deriv_eq (f : ℝ → ℝ) (n : ℕ) (x y : ℝ) (hxy : x ≠ y)
    (hf : ContDiffAt ℝ n f x) :
    iteratedDerivWithin n f (uIcc x y) x = iteratedDeriv n f x := by
  apply iteratedDerivWithin_eq_iteratedDeriv
  · rw [uIcc]
    apply uniqueDiffOn_Icc
    rcases lt_or_gt_of_ne hxy with h | h
    · rwa [inf_eq_left.mpr h.le, sup_eq_right.mpr h.le]
    · rwa [inf_eq_right.mpr h.le, sup_eq_left.mpr h.le]
  · exact hf
  · exact left_mem_uIcc

theorem phase_error_bound (N m l R E r e : ℝ) (hN : 0 ≤ N) (hm : 0 < m) (hl : 0 < l)
    (hR : 0 ≤ R) (hE : 0 ≤ E) (hr : |r| ≤ R) (he : |e| ≤ E) :
    |(2 * Real.pi * N / (m * l)) * (r + e)| ≤ 2 * Real.pi * N * (R + E) / (m * l) := by
  have hc : 0 < 2 * Real.pi := by positivity
  have hml : 0 < m * l := mul_pos hm hl
  have hnum : 0 ≤ 2 * Real.pi * N := mul_nonneg hc.le hN
  have hcoef : 0 ≤ 2 * Real.pi * N / (m * l) := div_nonneg hnum hml.le
  have hre : |r + e| ≤ R + E := by
    calc |r + e| ≤ |r| + |e| := abs_add_le _ _
      _ ≤ R + E := add_le_add hr he
  calc |(2 * Real.pi * N / (m * l)) * (r + e)|
      = (2 * Real.pi * N / (m * l)) * |r + e| := by
        rw [abs_mul, abs_of_nonneg hcoef]
    _ ≤ (2 * Real.pi * N / (m * l)) * (R + E) :=
        mul_le_mul_of_nonneg_left hre hcoef
    _ = 2 * Real.pi * N * (R + E) / (m * l) := by ring

theorem quadratic_remainder_bound (f : ℝ → ℝ) (x h B : ℝ)
    (hC : ContDiff ℝ 2 f) (hB : ∀ t, |iteratedDeriv 2 f t| ≤ B) (hh : h ≠ 0) :
    |f (x + h) - f x - iteratedDeriv 1 f x * h| ≤ B * h ^ 2 / 2 := by
  obtain ⟨ξ, _, hT⟩ :=
    taylor_mean_remainder_lagrange_iteratedDeriv (f := f) (x := x + h) (x₀ := x)
      (n := 1) (by intro he; exact hh (by linarith [he])) hC.contDiffOn
  rw [taylor_one_eval] at hT
  rw [within_deriv_eq f 1 x (x + h) (by intro he; exact hh (by linarith [he])
    : x ≠ x + h) ((hC.of_le (by decide)).contDiffAt)] at hT
  have hsub : x + h - x = h := by ring
  rw [hsub] at hT
  norm_num at hT
  have hgoal : f (x + h) - f x - iteratedDeriv 1 f x * h =
      iteratedDeriv 2 f ξ * h ^ 2 / 2 := by
    rw [iteratedDeriv_one]
    rw [← hT]; ring
  rw [hgoal]
  have hsq : (0 : ℝ) ≤ h ^ 2 := sq_nonneg h
  calc |iteratedDeriv 2 f ξ * h ^ 2 / 2|
      = |iteratedDeriv 2 f ξ| * h ^ 2 / 2 := by
        rw [abs_div, abs_mul, abs_of_nonneg hsq, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
    _ ≤ B * h ^ 2 / 2 := by
        have hle : |iteratedDeriv 2 f ξ| ≤ B := hB ξ
        nlinarith [hsq]

theorem cube_sum_sq_le {d : ℕ} (h : Fin d → ℝ) (l : ℝ) (hl : 0 ≤ l)
    (hb : ∀ i, |h i| ≤ l / 2) :
    ∑ i, (h i) ^ 2 ≤ d * l ^ 2 / 4 := by
  have hb2 : ∀ i, (h i) ^ 2 ≤ l ^ 2 / 4 := by
    intro i
    have hi := abs_le.mp (hb i)
    have h1 : 0 ≤ l / 2 - h i := by linarith [hi.2]
    have h2 : 0 ≤ l / 2 + h i := by linarith [hi.1]
    have hp : 0 ≤ (l / 2 - h i) * (l / 2 + h i) := mul_nonneg h1 h2
    nlinarith [hp]
  calc ∑ i, (h i) ^ 2 ≤ ∑ _i : Fin d, l ^ 2 / 4 :=
        Finset.sum_le_sum (fun i _ => hb2 i)
    _ = d * (l ^ 2 / 4) := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    _ = d * l ^ 2 / 4 := by ring

theorem cube_remainder_bound {d : ℕ} (r B l : ℝ) (h : Fin d → ℝ)
    (hl : 0 ≤ l) (hB : 0 ≤ B) (hb : ∀ i, |h i| ≤ l / 2)
    (hrem : |r| ≤ B / 2 * ∑ i, (h i) ^ 2) :
    |r| ≤ B * d * l ^ 2 / 8 := by
  have hsum := cube_sum_sq_le h l hl hb
  calc |r| ≤ B / 2 * ∑ i, (h i) ^ 2 := hrem
    _ ≤ B / 2 * (d * l ^ 2 / 4) :=
        mul_le_mul_of_nonneg_left hsum (by positivity)
    _ = B * d * l ^ 2 / 8 := by ring

theorem cube_taylor_remainder {d : ℕ} (f : EuclideanSpace ℝ (Fin d) → ℝ)
    (x : EuclideanSpace ℝ (Fin d)) (B l : ℝ) (h : Fin d → ℝ)
    (hf : ContDiff ℝ 2 f) (hB : 0 ≤ B)
    (hessian : ∀ y, ‖fderiv ℝ (fderiv ℝ f) y‖ ≤ B)
    (hl : 0 ≤ l) (hb : ∀ i, |h i| ≤ l / 2) :
    |f (x + WithLp.toLp 2 h) - f x - (fderiv ℝ f x) (WithLp.toLp 2 h)| ≤
      B * d * l ^ 2 / 8 := by
  apply cube_remainder_bound _ B l h hl hB hb
  have hrem :=
    Qatlib.Concepts.SignalPrimitive.GridGradient.gradient_second_derivative_remainder
      d f x (WithLp.toLp 2 h) B hf hB hessian
  calc
    |f (x + WithLp.toLp 2 h) - f x - (fderiv ℝ f x) (WithLp.toLp 2 h)| ≤
        B * ‖WithLp.toLp 2 h‖ ^ 2 / 2 := by
      simpa [Real.norm_eq_abs] using! hrem
    _ = B / 2 * ∑ i, h i ^ 2 := by
      rw [EuclideanSpace.norm_sq_eq]
      simp only [Real.norm_eq_abs, sq_abs]
      ring

end Qatlib.Concepts.GradientOracle.C2GradientAlg
