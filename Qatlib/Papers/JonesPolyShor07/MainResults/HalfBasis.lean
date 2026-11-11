/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Defs
import Mathlib.Algebra.Group.Monoid
import Mathlib.Algebra.GroupWithZero.Defs
import Mathlib.Algebra.Notation.Defs
import Mathlib.Algebra.Ring.Defs
import Mathlib.Basic.Complex.Basic
import Mathlib.Basic.SetLike.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Defs
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fintype.Defs
import Mathlib.Data.Matrix.Diagonal
import Mathlib.Data.Matrix.Mul
import Mathlib.LinearAlgebra.Matrix.Defs
import Mathlib.Tactic

/-!
# Matrices acting on a prescribed coordinate subset

`ActsOnSubset` requires a matrix to equal the identity outside a selected finite set and to have
zero entries between that set and its complement. The module proves that the identity satisfies
this condition and that the condition is closed under multiplication. See [ShorJordan2008].

## Main statements

* `actsOnSubset_one`: The identity matrix satisfies `ActsOnSubset S` for every finite subset S.
* `actsOnSubset_mul`: The product of two matrices satisfying `ActsOnSubset S` also satisfies
  `ActsOnSubset S`.

## References

* [Shor and Jordan, 2008][ShorJordan2008]
-/

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.JonesPolyShor07.MainResults.HalfBasis

open Matrix

/-- The matrix equals the identity on the complement of S and has zero entries between S and its
complement; see [ShorJordan2008]. -/
def ActsOnSubset {m : ℕ} (S : Finset (Fin m)) (U : Matrix (Fin m) (Fin m) ℂ) : Prop :=
  (∀ i j, i ∉ S → j ∉ S → U i j = if i = j then 1 else 0) ∧
    (∀ i j, i ∉ S → j ∈ S → U i j = 0) ∧
      (∀ i j, i ∈ S → j ∉ S → U i j = 0)

/-- The identity matrix satisfies `ActsOnSubset S` for every finite subset S; see
[ShorJordan2008]. -/
theorem actsOnSubset_one {m : ℕ} (S : Finset (Fin m)) :
    ActsOnSubset S (1 : Matrix (Fin m) (Fin m) ℂ) := by
  refine ⟨?_, ?_, ?_⟩
  · intro i j _ _; simp [Matrix.one_apply]
  · intro i j hi hj
    have hij : i ≠ j := fun h => hi (h ▸ hj)
    simp [hij]
  · intro i j hi hj
    have hij : i ≠ j := fun h => hj (h ▸ hi)
    simp [hij]

/-- The product of two matrices satisfying `ActsOnSubset S` also satisfies `ActsOnSubset S`; see
[ShorJordan2008]. -/
theorem actsOnSubset_mul {m : ℕ} {S : Finset (Fin m)} {U V : Matrix (Fin m) (Fin m) ℂ}
    (hU : ActsOnSubset S U) (hV : ActsOnSubset S V) : ActsOnSubset S (U * V) := by
  refine ⟨?_, ?_, ?_⟩
  · intro i j hi hj
    rw [Matrix.mul_apply, Finset.sum_eq_single i]
    · rw [hU.1 i i hi hi, hV.1 i j hi hj]
      simp
    · intro k _ hk
      by_cases hkS : k ∈ S
      · rw [hU.2.1 i k hi hkS, zero_mul]
      · rw [hU.1 i k hi hkS, if_neg (fun h : i = k => hk h.symm), zero_mul]
    · intro h
      exact absurd (Finset.mem_univ i) h
  · intro i j hi hj
    rw [Matrix.mul_apply, Finset.sum_eq_single i]
    · rw [hU.1 i i hi hi, hV.2.1 i j hi hj]
      simp
    · intro k _ hk
      by_cases hkS : k ∈ S
      · rw [hU.2.1 i k hi hkS, zero_mul]
      · rw [hU.1 i k hi hkS, if_neg (fun h : i = k => hk h.symm), zero_mul]
    · intro h
      exact absurd (Finset.mem_univ i) h
  · intro i j hi hj
    rw [Matrix.mul_apply, Finset.sum_eq_single j]
    · rw [hU.2.2 i j hi hj, zero_mul]
    · intro k _ hk
      by_cases hkS : k ∈ S
      · rw [hV.2.2 k j hkS hj, mul_zero]
      · rw [hV.1 k j hkS hj, if_neg (fun h : k = j => hk h), mul_zero]
    · intro h
      exact absurd (Finset.mem_univ j) h

end Qatlib.Papers.JonesPolyShor07.MainResults.HalfBasis
