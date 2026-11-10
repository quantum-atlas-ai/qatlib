/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.JuntaLearning07.MainResults.JuntaLearningAlgorithm
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Tactic
set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false
set_option maxHeartbeats 1000000
noncomputable section

namespace Qatlib.Papers.JuntaLearning07.MainResults

open scoped BigOperators

variable {Ω : Type} [Fintype Ω]

def weightedMean (w : Ω → ℝ) (X : Ω → ℝ) : ℝ := ∑ o, w o * X o

theorem weightedMarkov (w : Ω → ℝ) (hw0 : ∀ o, 0 ≤ w o) (_hw1 : ∑ o, w o = 1)
    (X : Ω → ℝ) (hX0 : ∀ o, 0 ≤ X o) {t a : ℝ} (ht : 0 < t)
    (hmean : weightedMean w X < a) :
    weightedMean w (fun o => if t ≤ X o then 1 else 0) ≤ a / t := by
  have hkey : t * weightedMean w (fun o => if t ≤ X o then 1 else 0) ≤
      weightedMean w X := by
    unfold weightedMean
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro o _
    change t * (w o * (if t ≤ X o then 1 else 0)) ≤ w o * X o
    by_cases h : t ≤ X o
    · rw [if_pos h]
      nlinarith [hw0 o]
    · rw [if_neg h]
      nlinarith [hw0 o, hX0 o]
  have hle : weightedMean w (fun o => if t ≤ X o then 1 else 0) ≤ weightedMean w X / t := by
    rw [le_div_iff₀ ht, mul_comm]
    exact hkey
  have h2 : weightedMean w X / t < a / t := div_lt_div_of_pos_right hmean ht
  exact le_trans hle (le_of_lt h2)

theorem coverage_ge (w : Ω → ℝ) (hw0 : ∀ o, 0 ≤ w o) (hw1 : ∑ o, w o = 1)
    (err : Ω → ℝ) (herr0 : ∀ o, 0 ≤ err o) {ε : ℝ} (hε : 0 < ε)
    (hmean : weightedMean w err < ε / 10) :
    (7 / 10 : ℝ) ≤ weightedMean w (fun o => if err o < ε / 3 then 1 else 0) := by
  have ht : (0 : ℝ) < ε / 3 := by linarith
  have hmarkov := weightedMarkov w hw0 hw1 err herr0 ht hmean
  have hcompl : weightedMean w (fun o => if err o < ε / 3 then 1 else 0) +
      weightedMean w (fun o => if ε / 3 ≤ err o then 1 else 0) = 1 := by
    unfold weightedMean
    rw [← Finset.sum_add_distrib]
    trans ∑ o, w o
    · apply Finset.sum_congr rfl
      intro o _
      change w o * (if err o < ε / 3 then (1 : ℝ) else 0) +
        w o * (if ε / 3 ≤ err o then 1 else 0) = w o
      by_cases h : err o < ε / 3
      · rw [if_pos h, if_neg (not_le.mpr h)]; ring
      · rw [if_neg h, if_pos (le_of_not_gt h)]; ring
    · exact hw1
  have hratio : (ε / 10) / (ε / 3) = 3 / 10 := by
    field_simp
  have hle : weightedMean w (fun o => if ε / 3 ≤ err o then 1 else 0) ≤ 3 / 10 := by
    calc weightedMean w (fun o => if ε / 3 ≤ err o then 1 else 0) ≤ (ε / 10) / (ε / 3) := hmarkov
      _ = 3 / 10 := hratio
  linarith

theorem agree_fraction_ge (w : Ω → ℝ) (hw0 : ∀ o, 0 ≤ w o) (hw1 : ∑ o, w o = 1)
    (err : Ω → ℝ) (herr0 : ∀ o, 0 ≤ err o) {ε : ℝ} (hε : 0 < ε)
    (hmean : weightedMean w err < ε / 10) :
    (7 / 10 : ℝ) ≤ weightedMean w (fun o => if 1 - ε / 3 < 1 - err o then 1 else 0) := by
  have hle : (fun o => if 1 - ε / 3 < 1 - err o then (1 : ℝ) else 0) =
      (fun o => if err o < ε / 3 then 1 else 0) := by
    funext o
    have : 1 - ε / 3 < 1 - err o ↔ err o < ε / 3 := by constructor <;> intro h <;> linarith
    by_cases h : err o < ε / 3
    · rw [if_pos (this.mpr h), if_pos h]
    · rw [if_neg (fun hh => h (this.mp hh)), if_neg h]
  rw [hle]
  exact coverage_ge w hw0 hw1 err herr0 hε hmean

variable {n : ℕ}

theorem stage2_error_bound (f H : (Fin n → Bool) → Bool) (S : Finset (Fin n → Bool))
    {ε : ℝ} (hε : 0 < ε)
    (hout : uniformExpect (fun x => if x ∈ S then (0 : ℝ) else 1) ≤ ε / 3)
    (hin : uniformExpect (fun x => if x ∈ S then (if H x = f x then (0 : ℝ) else 1) else 0)
      ≤ ε / 3) :
    disagreement f H < ε := by
  have hpoint : ∀ x, (if f x = H x then (0 : ℝ) else 1) ≤
      (if x ∈ S then (0 : ℝ) else 1) +
        (if x ∈ S then (if H x = f x then (0 : ℝ) else 1) else 0) := by
    intro x
    by_cases hx : x ∈ S
    · rw [if_pos hx, if_pos hx, zero_add]
      by_cases h : H x = f x
      · rw [if_pos h, if_pos h.symm]
      · rw [if_neg h, if_neg (fun hh => h hh.symm)]
    · rw [if_neg hx, if_neg hx, add_zero]
      by_cases h : f x = H x <;> simp [h]
  have hsum : disagreement f H ≤
      uniformExpect (fun x => if x ∈ S then (0 : ℝ) else 1) +
        uniformExpect (fun x => if x ∈ S then (if H x = f x then (0 : ℝ) else 1) else 0) := by
    have hsum' : (∑ x : Fin n → Bool, (if f x = H x then (0 : ℝ) else 1)) ≤
        ∑ x : Fin n → Bool,
          ((if x ∈ S then (0 : ℝ) else 1) +
            (if x ∈ S then (if H x = f x then (0 : ℝ) else 1) else 0)) :=
      Finset.sum_le_sum (fun x _ => hpoint x)
    rw [Finset.sum_add_distrib] at hsum'
    unfold disagreement uniformExpect
    have hinv : (0 : ℝ) ≤ ((2 : ℝ) ^ n)⁻¹ := by positivity
    calc ((2 : ℝ) ^ n)⁻¹ * ∑ x : Fin n → Bool, (if f x = H x then (0 : ℝ) else 1)
        ≤ ((2 : ℝ) ^ n)⁻¹ *
            ((∑ x : Fin n → Bool, (if x ∈ S then (0 : ℝ) else 1)) +
              ∑ x : Fin n → Bool,
                (if x ∈ S then (if H x = f x then (0 : ℝ) else 1) else 0)) :=
          mul_le_mul_of_nonneg_left hsum' hinv
      _ = ((2 : ℝ) ^ n)⁻¹ * (∑ x : Fin n → Bool, (if x ∈ S then (0 : ℝ) else 1)) +
            ((2 : ℝ) ^ n)⁻¹ *
              ∑ x : Fin n → Bool,
                (if x ∈ S then (if H x = f x then (0 : ℝ) else 1) else 0) := by
          ring
  have htwo : disagreement f H ≤ 2 * ε / 3 := by
    rw [show (2 : ℝ) * ε / 3 = ε / 3 + ε / 3 by ring]
    exact le_trans hsum (add_le_add hout hin)
  nlinarith

end Qatlib.Papers.JuntaLearning07.MainResults
