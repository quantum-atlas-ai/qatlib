/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.Complex.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic

set_option autoImplicit false

open scoped BigOperators
open Real

namespace Qatlib.Papers.AffineHSP02.MainResults

noncomputable section

def phase (p : ℕ) (m b : ℤ) : ℝ := 2 * π * ((m * b : ℤ) : ℝ) / (p : ℝ)

def xPlus (p : ℕ) (m b : ℤ) : ℝ := (1 + Real.cos (phase p m b)) / 2

def xMinus (p : ℕ) (m b : ℤ) : ℝ := (1 - Real.cos (phase p m b)) / 2

def yPlus (p : ℕ) (m b : ℤ) : ℝ := (1 + Real.sin (phase p m b)) / 2

def yMinus (p : ℕ) (m b : ℤ) : ℝ := (1 - Real.sin (phase p m b)) / 2

theorem phase_neg_b (p : ℕ) (m b : ℤ) : phase p m (-b) = -phase p m b := by
  unfold phase
  have : m * -b = -(m * b) := by ring
  rw [this]
  push_cast
  ring

theorem xPlus_neg_b (p : ℕ) (m b : ℤ) : xPlus p m (-b) = xPlus p m b := by
  unfold xPlus
  rw [phase_neg_b, Real.cos_neg]

theorem xMinus_neg_b (p : ℕ) (m b : ℤ) : xMinus p m (-b) = xMinus p m b := by
  unfold xMinus
  rw [phase_neg_b, Real.cos_neg]

theorem yPlus_neg_b (p : ℕ) (m b : ℤ) : yPlus p m (-b) = yMinus p m b := by
  unfold yPlus yMinus
  rw [phase_neg_b, Real.sin_neg]
  ring

theorem yMinus_neg_b (p : ℕ) (m b : ℤ) : yMinus p m (-b) = yPlus p m b := by
  unfold yPlus yMinus
  rw [phase_neg_b, Real.sin_neg]
  ring

theorem xOutcomes_sum (p : ℕ) (m b : ℤ) : xPlus p m b + xMinus p m b = 1 := by
  unfold xPlus xMinus
  ring

theorem yOutcomes_sum (p : ℕ) (m b : ℤ) : yPlus p m b + yMinus p m b = 1 := by
  unfold yPlus yMinus
  ring

def measProb (p : ℕ) (m b : ℤ) (q : Bool × Bool) : ℝ :=
  if q.1 then (if q.2 then xPlus p m b else xMinus p m b) / 2
  else (if q.2 then yPlus p m b else yMinus p m b) / 2

theorem measProb_sum (p : ℕ) (m b : ℤ) :
    ∑ q : Bool × Bool, measProb p m b q = 1 := by
  have hx := xOutcomes_sum p m b
  have hy := yOutcomes_sum p m b
  simp only [Fintype.sum_prod_type, Fintype.sum_bool, measProb, Bool.false_eq_true,
    if_true, if_false]
  nlinarith [hx, hy]

theorem measProb_X_neg_b (p : ℕ) (m b : ℤ) (s : Bool) :
    measProb p m (-b) (true, s) = measProb p m b (true, s) := by
  cases s <;> simp [measProb, xPlus_neg_b, xMinus_neg_b]

theorem measProb_Y_neg_b (p : ℕ) (m b : ℤ) (s : Bool) :
    measProb p m (-b) (false, s) = measProb p m b (false, !s) := by
  cases s <;> simp [measProb, yPlus_neg_b, yMinus_neg_b]

theorem measProb_ne_neg_b (p : ℕ) (m b : ℤ)
    (hsin : Real.sin (phase p m b) ≠ 0) : measProb p m b ≠ measProb p m (-b) := by
  intro h
  have hY : measProb p m b (false, true) = measProb p m (-b) (false, true) := by
    rw [h]
  rw [measProb_Y_neg_b, Bool.not_true] at hY
  simp only [measProb, Bool.false_eq_true, if_false, if_true] at hY
  have hsin0 : Real.sin (phase p m b) = 0 := by
    unfold yPlus yMinus at hY
    linarith
  exact hsin hsin0

def tvDist {α : Type*} [Fintype α] (P Q : α → ℝ) : ℝ :=
  (1 / 2) * ∑ a, |P a - Q a|

theorem tvDist_pos_of_ne {α : Type*} [Fintype α] {P Q : α → ℝ} (h : P ≠ Q) :
    0 < tvDist P Q := by
  obtain ⟨a, ha⟩ := Function.ne_iff.mp h
  unfold tvDist
  have hnonneg : ∀ a ∈ (Finset.univ : Finset α), 0 ≤ |P a - Q a| := by
    intro a _; positivity
  have hpos : 0 < |P a - Q a| := abs_pos.mpr (sub_ne_zero.mpr ha)
  have hsum := Finset.sum_pos' hnonneg ⟨a, Finset.mem_univ a, hpos⟩
  linarith

theorem twoQuadrature_tv_pos (p : ℕ) (m b : ℤ) (hsin : Real.sin (phase p m b) ≠ 0) :
    0 < tvDist (measProb p m b) (measProb p m (-b)) :=
  tvDist_pos_of_ne (measProb_ne_neg_b p m b hsin)

end

end Qatlib.Papers.AffineHSP02.MainResults
