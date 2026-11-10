/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.SearchStopping.GroverSuccess.Section2HalfIterationsSubgoalStat
set_option backward.isDefEq.respectTransparency false
set_option warningAsError false

namespace Qatlib.Concepts.SearchStopping.GroverSuccess

open Qatlib.Concepts.SearchStopping.KnownCount

private theorem sin_sq_half_first_window {x : ℝ}
    (hx : Real.pi / 4 ≤ x) (hx2 : x ≤ Real.pi / 2) : 1 / 2 ≤ Real.sin x ^ 2 := by
  have hsin : Real.sqrt 2 / 2 ≤ Real.sin x := by
    rw [← Real.sin_pi_div_four]
    apply Real.monotoneOn_sin
      ⟨by linarith [Real.pi_pos], by linarith [Real.pi_pos]⟩
      ⟨by linarith [Real.pi_pos], hx2⟩ hx
  have hs := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)
  nlinarith [Real.sqrt_nonneg 2]

theorem sin_sq_half_window {x : ℝ} (hx : Real.pi / 4 ≤ x) (hx3 : x ≤ 3 * Real.pi / 4) :
    1 / 2 ≤ Real.sin x ^ 2 := by
  by_cases hx2 : x ≤ Real.pi / 2
  · exact sin_sq_half_first_window hx hx2
  · have h := sin_sq_half_first_window
      (show Real.pi / 4 ≤ Real.pi - x by linarith)
      (show Real.pi - x ≤ Real.pi / 2 by linarith)
    simpa using h

theorem half_budget_angle (θ : ℝ) (hθ : 0 < θ) (hθupper : θ < Real.pi / 2) :
    ∃ k : ℕ, (k : ℝ) ≤ Real.pi / (8 * θ) + 1 ∧
      1 / 2 ≤ Real.sin ((2 * (k : ℝ) + 1) * θ)^2 := by
  by_cases hsmall : θ < Real.pi / 12
  · let q : ℝ := Real.pi / (8 * θ)
    let k : ℕ := Nat.ceil q
    have hq0 : 0 ≤ q := by positivity
    have hlo : q ≤ (k : ℝ) := Nat.le_ceil q
    have hhi : (k : ℝ) < q + 1 := Nat.ceil_lt_add_one hq0
    have hprod : q * θ = Real.pi / 8 := by
      dsimp [q]
      field_simp
    have hloθ := mul_le_mul_of_nonneg_right hlo hθ.le
    have hhiθ := mul_lt_mul_of_pos_right hhi hθ
    refine ⟨k, hhi.le, sin_sq_half_window ?_ ?_⟩
    · nlinarith
    · nlinarith [Real.pi_pos]
  · by_cases hmid : θ ≤ Real.pi / 4
    · refine ⟨1, ?_, sin_sq_half_window ?_ ?_⟩
      · have hq : 0 ≤ Real.pi / (8 * θ) := by positivity
        norm_num
        linarith
      · norm_num
        linarith
      · norm_num
        linarith
    · refine ⟨0, ?_, ?_⟩
      · simp only [Nat.cast_zero]
        positivity
      · simp only [Nat.cast_zero, mul_zero, zero_add, one_mul]
        exact sin_sq_half_window (by linarith) (by linarith [Real.pi_pos])

theorem section2HalfIterationsSubgoal : Section2HalfIterationsSubgoal := by
  intro I _ _ hN A θ hθ hθupper hangle
  have hs : Real.sin θ ≠ 0 := (Real.sin_pos_of_pos_of_lt_pi hθ (by linarith [Real.pi_pos])).ne'
  have hc : Real.cos θ ≠ 0 :=
    (Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos], hθupper⟩).ne'
  obtain ⟨k, hk, hsuccess⟩ := half_budget_angle θ hθ hθupper
  refine ⟨k, hk, ?_⟩
  rw [measureProb_groverState hN A θ hangle hs hc k]
  exact hsuccess

end Qatlib.Concepts.SearchStopping.GroverSuccess
