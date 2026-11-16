/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Mathlib.LinearAlgebra.UnitaryGroup
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Algebra.Order.BigOperators.Group.Finset

@[expose] public section


/-! # Actual unitary column mass and finite mixture pigeonhole bounds

The estimates use actual squared complex matrix entries. Neither a final
probability bound nor a doubly stochastic matrix is supplied as a premise.
-/

set_option autoImplicit false
noncomputable section
open scoped BigOperators ComplexConjugate Matrix
namespace Qatlib.Concepts.BosonFock.BosonOperators.Pigeonhole

/-- A genuine finite unitary column has total squared complex mass one. -/
theorem columnMass {I : Type*} [Fintype I] [DecidableEq I]
    (U : Matrix I I ℂ) (hU : U ∈ Matrix.unitaryGroup I ℂ) (y : I) :
    ∑ x, Complex.normSq (U x y) = 1 := by
  have h : ∑ x, Uᴴ y x * U x y = 1 := by
    have h0 := congrFun (congrFun (Matrix.mem_unitaryGroup_iff'.mp hU) y) y
    simpa [Matrix.mul_apply] using h0
  have hc : ((∑ x, Complex.normSq (U x y) : ℝ) : ℂ) = 1 := by
    rw [← h]
    simp only [Matrix.conjTranspose_apply]
    push_cast
    apply Finset.sum_congr rfl
    intro x _
    exact Complex.normSq_eq_conj_mul_self
  exact Complex.ofReal_inj.mp (by simpa using hc)

/-- Any selected rows carry at most one unit of each genuine unitary column mass. -/
theorem columnPart {I : Type*} [Fintype I] [DecidableEq I]
    (U : Matrix I I ℂ) (hU : U ∈ Matrix.unitaryGroup I ℂ)
    (G : Finset I) (y : I) : ∑ x ∈ G, Complex.normSq (U x y) ≤ 1 := by
  rw [← columnMass U hU y]
  exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ G)
    (fun x _ _ => Complex.normSq_nonneg (U x y))

/-- The full selected row-to-column mass is bounded by the number of selected columns. -/
theorem partialMass {I : Type*} [Fintype I] [DecidableEq I]
    (U : Matrix I I ℂ) (hU : U ∈ Matrix.unitaryGroup I ℂ) (G B : Finset I) :
    (∑ x ∈ G, ∑ y ∈ B, Complex.normSq (U x y)) ≤ (B.card : ℝ) := by
  rw [Finset.sum_comm]
  calc
    _ ≤ ∑ y ∈ B, (1 : ℝ) := Finset.sum_le_sum fun y _ => columnPart U hU G y
    _ = _ := by simp

/-- The genuine uniformly averaged transition mass satisfies the unitary pigeonhole bound. -/
theorem uniformMass {I : Type*} [Fintype I] [DecidableEq I]
    (U : Matrix I I ℂ) (hU : U ∈ Matrix.unitaryGroup I ℂ) (G B : Finset I) :
    (∑ x ∈ G, ∑ y ∈ B, Complex.normSq (U x y)) / (G.card : ℝ) ≤
      (B.card : ℝ) / (G.card : ℝ) :=
  div_le_div_of_nonneg_right (partialMass U hU G B) (Nat.cast_nonneg _)

/-- Every finite probability mixture of genuine unitaries has the same averaged mass bound. -/
theorem mixtureMass {I J : Type*} [Fintype I] [DecidableEq I] [Fintype J]
    (V : J → Matrix I I ℂ) (w : J → ℝ)
    (hw : ∀ t, 0 ≤ w t) (hw1 : ∑ t, w t = 1)
    (hV : ∀ t, V t ∈ Matrix.unitaryGroup I ℂ) (G B : Finset I) :
    (∑ t, w t * (∑ x ∈ G, ∑ y ∈ B, Complex.normSq (V t x y))) / (G.card : ℝ)
      ≤ (B.card : ℝ) / (G.card : ℝ) := by
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
  calc
    _ ≤ ∑ t, w t * (B.card : ℝ) := Finset.sum_le_sum fun t _ =>
      mul_le_mul_of_nonneg_left (partialMass (V t) (hV t) G B) (hw t)
    _ = _ := by rw [← Finset.sum_mul, hw1, one_mul]

end Qatlib.Concepts.BosonFock.BosonOperators.Pigeonhole
