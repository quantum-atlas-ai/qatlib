/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Analysis.Complex.Basic
import Mathlib.Data.Matrix.Basic
import Mathlib.LinearAlgebra.Matrix.Hermitian

/-!
# Translation invariance and finite group algebras

For a finite additive commutative group, this module defines the shift matrices `shift` and
their linear combinations `groupAlgebraElem`. It characterizes matrices in this group algebra
both by commutation with every shift and by simultaneous translation invariance of their row and
column indices, as in [HunzikerEtAl2003].

## Main statements

* `groupAlgebraElem_apply`: The entry formula v(y - z).
* `commute_iff_eq_groupAlgebraElem`: Commutation with shifts characterizes the group algebra.
* `commute_iff_translation_invariant`: Commutation with shifts is equivalent to translation
  invariance.

## References

* [Hunziker et al., 2003][HunzikerEtAl2003]
-/

set_option autoImplicit false

namespace Qatlib.Papers.QLearningGeom03.MainResults

open Matrix
open scoped Matrix

variable {G : Type*} [AddCommGroup G] [Fintype G] [DecidableEq G]

/-- The permutation matrix for translation by `g` on a finite additive commutative group. -/
noncomputable def shift (g : G) : Matrix G G ℂ := fun y z => if y = z + g then 1 else 0

/-- The group-algebra matrix obtained by summing the shift matrices with coefficients `v`. -/
noncomputable def groupAlgebraElem (v : G → ℂ) : Matrix G G ℂ :=
  ∑ g, v g • shift g

/-- Multiplication of shift matrices corresponds to addition of their translation parameters. -/
lemma shift_mul_shift (g h : G) : shift g * shift h = shift (g + h) := by
  ext y z
  rw [Matrix.mul_apply]
  rw [Finset.sum_eq_single (z + h)]
  · simp [shift, show z + h + g = z + (g + h) by abel]
  · intro w _ hw
    simp [shift, hw]
  · intro hmem
    exact absurd (Finset.mem_univ _) hmem

/-- The (y, z) entry of `groupAlgebraElem v` is `v (y - z)`. -/
lemma groupAlgebraElem_apply (v : G → ℂ) (y z : G) :
    groupAlgebraElem v y z = v (y - z) := by
  rw [groupAlgebraElem, Matrix.sum_apply]
  simp only [Matrix.smul_apply, smul_eq_mul, shift]
  rw [Finset.sum_eq_single (y - z)]
  · simp [show z + (y - z) = y by abel]
  · intro w _ hw
    have hne : y ≠ z + w := fun hcon => hw (by rw [hcon]; abel)
    simp [hne]
  · intro hmem
    exact absurd (Finset.mem_univ _) hmem

/-- A matrix commutes with every shift if and only if it is a group-algebra matrix, as in
[HunzikerEtAl2003]. -/
theorem commute_iff_eq_groupAlgebraElem (A : Matrix G G ℂ) :
    (∀ g, A * shift g = shift g * A) ↔ ∃ v : G → ℂ, A = groupAlgebraElem v := by
  constructor
  · intro h
    refine ⟨fun g => A g 0, ?_⟩
    ext y z
    rw [groupAlgebraElem_apply]
    have hentry := congrFun (congrFun (h z) y) 0
    have h1 : (A * shift z) y 0 = A y z := by
      rw [Matrix.mul_apply]
      rw [Finset.sum_eq_single z]
      · simp [shift]
      · intro w _ hw
        simp [shift, hw]
      · intro hmem
        exact absurd (Finset.mem_univ _) hmem
    have h2 : (shift z * A) y 0 = A (y - z) 0 := by
      rw [Matrix.mul_apply]
      rw [Finset.sum_eq_single (y - z)]
      · have hz : shift z y (y - z) = 1 := by
          unfold shift
          rw [ite_eq_left (show y = (y - z) + z by abel)]
        rw [hz, one_mul]
      · intro w _ hw
        have hne : y ≠ w + z := fun hcon => hw (by rw [hcon]; abel)
        have hz : shift z y w = 0 := by
          unfold shift
          rw [ite_eq_right hne]
        rw [hz, zero_mul]
      · intro hmem
        exact absurd (Finset.mem_univ _) hmem
    rw [h1, h2] at hentry
    exact hentry
  · rintro ⟨v, rfl⟩ g
    rw [groupAlgebraElem, Finset.sum_mul, Finset.mul_sum]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [Matrix.smul_mul, Matrix.mul_smul, shift_mul_shift, shift_mul_shift, add_comm]

/-- A matrix commutes with every shift if and only if its entries are unchanged by simultaneous
translation of both indices, as in [HunzikerEtAl2003]. -/
theorem commute_iff_translation_invariant (A : Matrix G G ℂ) :
    (∀ g, A * shift g = shift g * A) ↔ ∀ (g x c : G), A (x + g) (c + g) = A x c := by
  constructor
  · intro h g x c
    have hcomm := congrFun (congrFun (h g) (x + g)) c
    have h1 : (A * shift g) (x + g) c = A (x + g) (c + g) := by
      rw [Matrix.mul_apply]
      rw [Finset.sum_eq_single (c + g)]
      · simp [shift]
      · intro w _ hw
        simp [shift, hw]
      · intro hmem
        exact absurd (Finset.mem_univ _) hmem
    have h2 : (shift g * A) (x + g) c = A (x + g - g) c := by
      rw [Matrix.mul_apply]
      rw [Finset.sum_eq_single (x + g - g)]
      · simp [shift]
      · intro w _ hw
        have hne : x + g ≠ w + g := fun hcon => hw (by rw [hcon]; abel)
        have hz : shift g (x + g) w = 0 := by
          unfold shift
          rw [ite_eq_right hne]
        rw [hz, zero_mul]
      · intro hmem
        exact absurd (Finset.mem_univ _) hmem
    rw [h1, h2] at hcomm
    rwa [add_sub_cancel_right] at hcomm
  · intro h g
    ext y c
    rw [Matrix.mul_apply, Matrix.mul_apply]
    rw [Finset.sum_eq_single (c + g)]
    · rw [Finset.sum_eq_single (y - g)]
      · have hc : shift g (c + g) c = 1 := by simp [shift]
        have hy : shift g y (y - g) = 1 := by
          unfold shift
          rw [ite_eq_left (show y = (y - g) + g by abel)]
        rw [hc, hy, mul_one, one_mul]
        rw [← h g (y - g) c, show (y - g) + g = y by abel]
      · intro w _ hw
        have hne : y ≠ w + g := fun hcon => hw (by rw [hcon]; abel)
        simp [shift, hne]
      · intro hmem
        exact absurd (Finset.mem_univ _) hmem
    · intro w _ hw
      simp [shift, hw]
    · intro hmem
      exact absurd (Finset.mem_univ _) hmem

end Qatlib.Papers.QLearningGeom03.MainResults
