/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Basic.Real.Basic
import Mathlib.Tactic

/-!
# A signless kernel on an actual finite vertex sector

The matrix below is constructed from the edge weights on the specified sector.
Its diagonal is the weighted degree. A bipartition gives an explicit nonzero
alternating vector annihilated by every row, provided the graph has no loops.
-/

@[expose] public section

set_option autoImplicit false

open scoped BigOperators

namespace Qatlib.Papers.KhovanovHom25.MainResults.SectorKernel

/-- The alternating vector determined by a genuine two-coloring. -/
def sign {α : Type*} (color : α → Bool) (v : α) : ℝ := if color v then 1 else -1

/-- Every coordinate of the alternating vector is nonzero. -/
theorem sign_ne_zero {α : Type*} (color : α → Bool) (v : α) : sign color v ≠ 0 := by
  unfold sign
  split <;> norm_num

/-- An edge between different colors reverses the alternating vector. -/
theorem sign_flip {α : Type*} (color : α → Bool) {v u : α}
    (h : color v ≠ color u) : sign color u = - sign color v := by
  unfold sign
  cases hv : color v <;> cases hu : color u <;> simp_all

/-- The signless Laplacian, with degree computed inside the fixed vertex sector. -/
noncomputable def matrix {α : Type*} [DecidableEq α] (S : Finset α)
    (w : α → α → ℝ) (v u : α) : ℝ :=
  if v = u then ∑ z ∈ S, w v z else w v u

/-- A row of the signless matrix is its degree term plus its weighted neighbor sum. -/
theorem row_expand {α : Type*} [DecidableEq α] (S : Finset α) (w : α → α → ℝ)
    (x : α → ℝ) (v : α) (hv : v ∈ S) (hdiag : w v v = 0) :
    ∑ u ∈ S, matrix S w v u * x u =
      (∑ u ∈ S, w v u) * x v + ∑ u ∈ S, w v u * x u := by
  have heq : ∀ u : α, matrix S w v u * x u =
      (if v = u then (∑ z ∈ S, w v z) * x v else 0) + w v u * x u := by
    intro u
    by_cases h : v = u
    · subst u
      simp [matrix, hdiag]
    · simp only [matrix, ite_eq_right h, zero_add]
  simp_rw [heq]
  rw [Finset.sum_add_distrib]
  simp only [Finset.sum_ite_eq, hv, ite_eq_left]

/-- Every row annihilates the explicit alternating vector of a loop-free bipartite sector. -/
theorem row_zero {α : Type*} [DecidableEq α] (S : Finset α) (w : α → α → ℝ)
    (color : α → Bool) (v : α) (hv : v ∈ S) (hdiag : w v v = 0)
    (hcolor : ∀ u ∈ S, w v u ≠ 0 → color v ≠ color u) :
    ∑ u ∈ S, matrix S w v u * sign color u = 0 := by
  rw [row_expand S w (sign color) v hv hdiag]
  have heq : ∀ u ∈ S, w v u * sign color u = -(w v u * sign color v) := by
    intro u hu
    by_cases h : w v u = 0
    · rw [h, zero_mul, zero_mul, neg_zero]
    · rw [sign_flip color (hcolor u hu h), mul_neg]
  rw [Finset.sum_congr rfl heq, Finset.sum_neg_distrib, ← Finset.sum_mul]
  exact add_neg_cancel _

end Qatlib.Papers.KhovanovHom25.MainResults.SectorKernel
