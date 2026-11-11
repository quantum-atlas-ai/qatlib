/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.GroupTheory.GroupAction.MultipleTransitivity

/-!
# Indices of pointwise stabilizers

Multiple pretransitivity determines the index of a pointwise stabilizer by a descending
factorial. The one-, two-, and three-point specializations recover the stabilizer-index
identities used in Lemma 1 of [DenneyMooreRussell2008].

## Main statements

* `lemma1_index_of_fixingSubgroup`: a set of `j` points has stabilizer index equal to the
  corresponding descending factorial.
* `lemma1_three_point`: three distinct points give index `n * (n − 1) * (n − 2)`.

## References

* [Denney et al., 2008][DenneyMooreRussell2008]
-/

set_option autoImplicit false
noncomputable section

open MulAction

namespace Qatlib.Papers.PSL2ConjStab08.MainResults.StabilizerIndex

variable {G Ω : Type*} [Group G] [MulAction G Ω]

/-- For a finite `k`-multiply pretransitive action with `j ≤ k ≤ Nat.card Ω`, the pointwise
stabilizer of a set of cardinality `j` has index `(Nat.card Ω).descFactorial j`. See
[DenneyMooreRussell2008]. -/
theorem lemma1_index_of_fixingSubgroup [Finite Ω]
    {k j : ℕ} (hjk : j ≤ k) (hkΩ : k ≤ Nat.card Ω)
    (hMk : IsMultiplyPretransitive G Ω k)
    (S : Set Ω) (hS : S.ncard = j) :
    (fixingSubgroup G S).index = (Nat.card Ω).descFactorial j := by

  have hMj : IsMultiplyPretransitive G Ω j :=
    isMultiplyPretransitive_of_le hjk hkΩ
  have hMS : IsMultiplyPretransitive G Ω S.ncard := hS ▸ hMj

  rw [IsMultiplyPretransitive.index_of_fixingSubgroup_eq S hMS,
    Nat.descFactorial_eq_factorial_mul_choose]
  rw [hS, Nat.mul_comm]

/-- The pointwise stabilizer of a singleton equals the stabilizer of its unique point. -/
theorem fixingSubgroup_singleton_eq_stabilizer (α : Ω) :
    fixingSubgroup G ({α} : Set Ω) = stabilizer G α := by
  ext g
  simp only [mem_fixingSubgroup_iff, Set.mem_singleton_iff, mem_stabilizer_iff,
    forall_eq]

/-- In a finite three-multiply pretransitive action on at least three points, a point stabilizer
has index `Nat.card Ω`. See [DenneyMooreRussell2008]. -/
theorem lemma1_one_point [Finite Ω] (h3 : IsMultiplyPretransitive G Ω 3)
    (hcard : 3 ≤ Nat.card Ω) (α : Ω) :
    (stabilizer G α).index = Nat.card Ω := by
  have hM1 : IsMultiplyPretransitive G Ω 1 :=
    isMultiplyPretransitive_of_le (by norm_num) hcard
  have h := lemma1_index_of_fixingSubgroup (G := G) (Ω := Ω) (k := 1) (j := 1)
    (by norm_num) (by omega) hM1 ({α} : Set Ω) (Set.ncard_singleton α)
  rw [fixingSubgroup_singleton_eq_stabilizer] at h
  simpa using h

/-- In a finite three-multiply pretransitive action on at least three points, the pointwise
stabilizer of two distinct points has index `Nat.card Ω * (Nat.card Ω − 1)`. See
[DenneyMooreRussell2008]. -/
theorem lemma1_two_point [Finite Ω] (h3 : IsMultiplyPretransitive G Ω 3)
    (hcard : 3 ≤ Nat.card Ω) {α β : Ω} (hαβ : α ≠ β) :
    (fixingSubgroup G ({α, β} : Set Ω)).index = Nat.card Ω * (Nat.card Ω - 1) := by
  have hM2 : IsMultiplyPretransitive G Ω 2 :=
    isMultiplyPretransitive_of_le (by norm_num) hcard
  have h := lemma1_index_of_fixingSubgroup (G := G) (Ω := Ω) (k := 2) (j := 2)
    (by norm_num) (by omega) hM2 ({α, β} : Set Ω) (Set.ncard_pair hαβ)
  rw [h]
  simp only [Nat.descFactorial_succ, Nat.descFactorial_zero, Nat.sub_zero, Nat.mul_one]
  ring

/-- In a finite three-multiply pretransitive action on at least three points, the pointwise
stabilizer of three distinct points has index `Nat.card Ω * (Nat.card Ω − 1) * (Nat.card Ω −
2)`. See [DenneyMooreRussell2008]. -/
theorem lemma1_three_point [Finite Ω] (h3 : IsMultiplyPretransitive G Ω 3)
    (hcard : 3 ≤ Nat.card Ω) {α β γ : Ω} (hαβ : α ≠ β) (hαγ : α ≠ γ)
    (hβγ : β ≠ γ) :
    (fixingSubgroup G ({α, β, γ} : Set Ω)).index =
      Nat.card Ω * (Nat.card Ω - 1) * (Nat.card Ω - 2) := by
  have h := lemma1_index_of_fixingSubgroup (G := G) (Ω := Ω) (k := 3) (j := 3)
    (by norm_num) hcard h3 ({α, β, γ} : Set Ω) (by
      rw [Set.ncard_insert_of_notMem (by simp [hαβ, hαγ]),
        Set.ncard_pair hβγ])
  rw [h]
  simp only [Nat.descFactorial_succ, Nat.descFactorial_zero, Nat.sub_zero, Nat.mul_one]
  ring

end Qatlib.Papers.PSL2ConjStab08.MainResults.StabilizerIndex
