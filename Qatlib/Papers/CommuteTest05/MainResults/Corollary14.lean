/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Algebra.BigOperators.Field
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Analysis.SpecialFunctions.Pow.Real

set_option autoImplicit false
noncomputable section

open scoped BigOperators

namespace Qatlib.Papers.CommuteTest05.MainResults.Corollary14

theorem corollary14_deviation_time_bound
    {κ : Type*} [Fintype κ] (ν lam θ : κ → ℝ) (ρ : ℝ)
    (hν : ∑ k, ν k ^ 2 = 1)
    (hlam0 : ∀ k, 0 ≤ lam k)
    (hθ0 : ∀ k, 0 < θ k) (hθπ : ∀ k, θ k ≤ Real.pi / 2)
    (hcos : ∀ k, Real.cos (θ k) = |lam k|)
    (hlamρ : ∀ k, lam k ≤ ρ) (hρ : ρ < 1) :
    100 * (∑ k, ν k ^ 2 / θ k) ≤ 100 / Real.sqrt (1 - ρ) := by
  have hρpos : 0 < 1 - ρ := by linarith
  have hsqrtρpos : 0 < Real.sqrt (1 - ρ) := Real.sqrt_pos.mpr hρpos
  have hterm : ∀ k, ν k ^ 2 / θ k ≤ ν k ^ 2 / Real.sqrt (1 - ρ) := by
    intro k
    have hlam1 : lam k < 1 := lt_of_le_of_lt (hlamρ k) hρ
    have hθlepi : θ k ≤ Real.pi := by linarith [hθπ k, Real.pi_pos]
    have hsin := Real.sin_eq_sqrt_one_sub_cos_sq (le_of_lt (hθ0 k)) hθlepi
    have hcos2 : Real.cos (θ k) ^ 2 = lam k ^ 2 := by rw [hcos k, sq_abs]
    have hlam2 : lam k ^ 2 ≤ lam k := by nlinarith [hlam0 k, hlam1]
    have hrootpos : 0 < Real.sqrt (1 - lam k) :=
      Real.sqrt_pos.mpr (by linarith)
    have hsqrtle : Real.sqrt (1 - lam k) ≤ Real.sqrt (1 - lam k ^ 2) :=
      Real.sqrt_le_sqrt (by linarith)
    have hsinle : Real.sin (θ k) ≤ θ k := Real.sin_le (le_of_lt (hθ0 k))
    have hθge : Real.sqrt (1 - lam k) ≤ θ k := by
      rw [hsin, hcos2] at hsinle
      exact hsqrtle.trans hsinle
    have hrootρpos : 0 < Real.sqrt (1 - ρ) := hsqrtρpos
    have hsqrtρle : Real.sqrt (1 - ρ) ≤ Real.sqrt (1 - lam k) :=
      Real.sqrt_le_sqrt (by linarith [hlamρ k])
    exact (div_le_div_of_nonneg_left (sq_nonneg _) hrootpos hθge).trans
      (div_le_div_of_nonneg_left (sq_nonneg _) hrootρpos hsqrtρle)
  have hsum : ∑ k, ν k ^ 2 / θ k ≤ ∑ k, ν k ^ 2 / Real.sqrt (1 - ρ) :=
    Finset.sum_le_sum fun k _ => hterm k
  have hsum2 : (∑ k, ν k ^ 2 / Real.sqrt (1 - ρ)) =
      1 / Real.sqrt (1 - ρ) := by
    rw [← Finset.sum_div, hν]
  rw [hsum2] at hsum
  have hfin : 100 * (∑ k, ν k ^ 2 / θ k) ≤
      100 * (1 / Real.sqrt (1 - ρ)) :=
    mul_le_mul_of_nonneg_left hsum (by norm_num)
  calc 100 * (∑ k, ν k ^ 2 / θ k)
      ≤ 100 * (1 / Real.sqrt (1 - ρ)) := hfin
    _ = 100 / Real.sqrt (1 - ρ) := by rw [mul_one_div]

end Qatlib.Papers.CommuteTest05.MainResults.Corollary14
