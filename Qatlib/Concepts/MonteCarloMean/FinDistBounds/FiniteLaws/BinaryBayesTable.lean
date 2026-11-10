/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

set_option autoImplicit false
namespace Qatlib.Concepts.MonteCarloMean.FinDistBounds.BinaryBayesTable
open scoped BigOperators
noncomputable section

theorem abs_max_sub_max_le (a₁ a₂ b₁ b₂ : ℝ) :
    |max a₁ a₂ - max b₁ b₂| ≤ |a₁ - b₁| + |a₂ - b₂| := by
  rcases le_total a₁ a₂ with ha | ha
  · rcases le_total b₁ b₂ with hb | hb
    · simp only [max_eq_right ha, max_eq_right hb]
      linarith [abs_nonneg (a₁ - b₁)]
    · simp only [max_eq_right ha, max_eq_left hb]
      rcases le_total a₂ b₁ with hc | hc
      · have h1 : a₂ - b₁ ≤ 0 := by linarith
        have h2 : a₁ - b₁ ≤ 0 := by linarith
        have e1 : |a₂ - b₁| = b₁ - a₂ := by rw [abs_of_nonpos h1]; ring
        have e2 : |a₁ - b₁| = b₁ - a₁ := by rw [abs_of_nonpos h2]; ring
        rw [e1, e2]
        linarith [abs_nonneg (a₂ - b₂)]
      · have h1 : 0 ≤ a₂ - b₁ := by linarith
        have h2 : 0 ≤ a₂ - b₂ := by linarith
        have e1 : |a₂ - b₁| = a₂ - b₁ := by rw [abs_of_nonneg h1]
        have e2 : |a₂ - b₂| = a₂ - b₂ := abs_of_nonneg h2
        rw [e1, e2]
        linarith [abs_nonneg (a₁ - b₁)]
  · rcases le_total b₁ b₂ with hb | hb
    · simp only [max_eq_left ha, max_eq_right hb]
      rcases le_total a₁ b₂ with hc | hc
      · have h1 : a₁ - b₂ ≤ 0 := by linarith
        have h2 : a₂ - b₂ ≤ 0 := by linarith
        have e1 : |a₁ - b₂| = b₂ - a₁ := by rw [abs_of_nonpos h1]; ring
        have e2 : |a₂ - b₂| = b₂ - a₂ := by rw [abs_of_nonpos h2]; ring
        rw [e1, e2]
        linarith [abs_nonneg (a₁ - b₁)]
      · have h1 : 0 ≤ a₁ - b₂ := by linarith
        have h2 : 0 ≤ a₁ - b₁ := by linarith
        have e1 : |a₁ - b₂| = a₁ - b₂ := by rw [abs_of_nonneg h1]
        have e2 : |a₁ - b₁| = a₁ - b₁ := by rw [abs_of_nonneg h2]
        rw [e1, e2]
        linarith [abs_nonneg (a₂ - b₂)]
    · simp only [max_eq_left ha, max_eq_left hb]
      linarith [abs_nonneg (a₂ - b₂)]

variable {X : Type*} [Fintype X]

def accTab (P : X → Bool → ℝ) : ℝ :=
  ∑ x : X, max (P x false) (P x true)

theorem accTab_lipschitz (P Q : X → Bool → ℝ) :
    |accTab P - accTab Q| ≤
      ∑ x : X,
        (|P x false - Q x false| + |P x true - Q x true|) := by
  have key : ∀ x : X,
      |max (P x false) (P x true) - max (Q x false) (Q x true)|
        ≤ |P x false - Q x false| + |P x true - Q x true| :=
    fun x => abs_max_sub_max_le _ _ _ _
  have hsum : accTab P - accTab Q
      = ∑ x : X, (max (P x false) (P x true)
          - max (Q x false) (Q x true)) := by
    simp only [accTab]
    rw [← Finset.sum_sub_distrib]
  rw [hsum]
  calc |∑ x : X, (max (P x false) (P x true)
          - max (Q x false) (Q x true))|
      ≤ ∑ x : X,
          |max (P x false) (P x true) - max (Q x false) (Q x true)| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ x : X,
          (|P x false - Q x false| + |P x true - Q x true|) :=
        Finset.sum_le_sum fun x _ => key x

end
end Qatlib.Concepts.MonteCarloMean.FinDistBounds.BinaryBayesTable
