/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.Trainability23.HaarAverages.HaarInfrastructure

/-!
# Conjugation identities for matrix units

This module establishes entrywise and composition identities for conjugating a matrix unit by a
complex matrix and its adjoint. These algebraic identities prepare the matrix-unit calculations
used in Haar averages for the trainability analysis of [RudolphEtAl2024].

## Main statements

* `conj_single_apply`: expresses a conjugated matrix-unit entry as a product of two matrix
  entries.
* `conj_single_star_mul`: factors conjugation by a product into successive conjugations.

## References

* [Rudolph et al., 2024][RudolphEtAl2024]
-/

set_option warningAsError false

namespace Qatlib.Papers.Trainability23.HaarAverages

open scoped BigOperators Matrix

/-- The `(i, j)` entry of `U * E_ab * Uᴴ` equals `U i a` times the complex conjugate of `U j b`,
where `E_ab` is the matrix unit. -/
theorem conj_single_apply {n : Type*} [Fintype n] [DecidableEq n]
    (U : Matrix n n ℂ) (a b i j : n) :
    (U * Matrix.single a b (1 : ℂ) * star U) i j = U i a * star (U j b) := by
  have hsingle : ∀ (l k : n),
      Matrix.single a b (1 : ℂ) l k = if a = l ∧ b = k then 1 else 0 := by
    intro l k
    simp [Matrix.single, Matrix.of_apply]
  have hinner : ∀ k : n, (∑ l, U i l * Matrix.single a b (1 : ℂ) l k)
      = if b = k then U i a else 0 := by
    intro k
    by_cases hk : b = k
    · subst hk
      rw [Finset.sum_eq_single a]
      · rw [hsingle a b, if_pos ⟨rfl, rfl⟩, mul_one, if_pos rfl]
      · intro l _ hl
        rw [hsingle l b, if_neg (fun h => hl h.1.symm), mul_zero]
      · intro ha
        exact absurd (Finset.mem_univ a) ha
    · have hz : (∑ l, U i l * Matrix.single a b (1 : ℂ) l k) = 0 :=
        Finset.sum_eq_zero fun l _ => by
          rw [hsingle l k, if_neg (fun h => hk h.2), mul_zero]
      rw [hz, if_neg hk]
  simp only [Matrix.mul_apply]
  rw [Finset.sum_congr rfl fun k _ => by rw [hinner k]]
  rw [Finset.sum_eq_single b]
  · rw [if_pos rfl]
    simp [Matrix.star_apply]
  · intro k _ hk
    rw [if_neg (fun h => hk h.symm), zero_mul]
  · intro hb
    exact absurd (Finset.mem_univ b) hb

/-- Conjugating a matrix unit by `U * V` and its adjoint equals first conjugating by `V` and its
adjoint, then by `U` and its adjoint. -/
theorem conj_single_star_mul {n : Type*} [Fintype n] [DecidableEq n]
    (U V : Matrix n n ℂ) (a b : n) :
    (U * V) * Matrix.single a b (1 : ℂ) * star (U * V)
      = U * (V * Matrix.single a b (1 : ℂ) * star V) * star U := by
  rw [star_mul]
  simp only [Matrix.mul_assoc]

end Qatlib.Papers.Trainability23.HaarAverages
