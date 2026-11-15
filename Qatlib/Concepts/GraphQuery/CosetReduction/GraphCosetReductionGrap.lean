/-
Copyright (c) 2026 Quantum Atlas Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quantum Atlas Contributors
-/

module

public import Qatlib.Concepts.GraphQuery.CosetReduction.GraphCosetReductionStat

@[expose] public section

set_option autoImplicit false

namespace Qatlib.Concepts.GraphQuery.CosetReduction

open scoped Pointwise

variable {V : Type*}

/-- Characterizes membership of a conjugated lifted permutation in the color subgroup by
preservation of matrix entries. -/
theorem lifted_mem_color_iff (A B : BoolMatrix V) (p : Equiv.Perm V) :
    flipMatrix B * liftPerm p * (flipMatrix A)⁻¹ ∈ colorSubgroup V ↔
      ∀ i j, B (p i) (p j) = A i j := by
  change (∀ x : Position V,
    ((flipMatrix B * liftPerm p * (flipMatrix A)⁻¹) x).2 = x.2) ↔ _
  constructor
  · intro h i j
    have hb := h ((i,j),false)
    change xor (xor false (A i j)) (B (p i) (p j)) = false at hb
    cases hA : A i j <;> cases hB : B (p i) (p j) <;> simp_all
  · intro h x
    rcases x with ⟨⟨i,j⟩,b⟩
    change xor (xor b (A i j)) (B (p i) (p j)) = b
    rw [h i j]
    simp

/-- Characterizes membership in the encoded coset by the existence of a lifted vertex
permutation. -/
theorem mem_encoded_coset_iff (A B : BoolMatrix V) (k : Equiv.Perm (Position V)) :
    k ∈ cosetRepresentative A B •
        (encodedSubgroup A : Set (Equiv.Perm (Position V))) ↔
      ∃ p : Equiv.Perm V, k = flipMatrix B * liftPerm p * (flipMatrix A)⁻¹ := by
  constructor
  · intro hk
    rcases Set.mem_smul_set.mp hk with ⟨s, hs, hsk⟩
    rcases Subgroup.mem_map.mp hs with ⟨d, hd, rfl⟩
    rcases hd with ⟨p, rfl⟩
    refine ⟨p, ?_⟩
    change (flipMatrix B * (flipMatrix A)⁻¹) *
      (flipMatrix A * liftPerm p * (flipMatrix A)⁻¹) = k at hsk
    simpa only [mul_assoc, inv_mul_cancel_left] using hsk.symm
  · rintro ⟨p, rfl⟩
    apply Set.mem_smul_set.mpr
    refine ⟨(MulAut.conj (flipMatrix A)) (liftPerm p), ?_, ?_⟩
    · exact Subgroup.mem_map.mpr ⟨liftPerm p, ⟨p, rfl⟩, rfl⟩
    · change (flipMatrix B * (flipMatrix A)⁻¹) *
        (flipMatrix A * liftPerm p * (flipMatrix A)⁻¹) =
        flipMatrix B * liftPerm p * (flipMatrix A)⁻¹
      simp only [mul_assoc, inv_mul_cancel_left]

/-- Establishes the graph coset reduction specified by `GraphCosetReduction`. -/
theorem graphCosetReduction : GraphCosetReduction := by
  intro V A B
  constructor
  · rintro ⟨p, hp⟩
    refine ⟨flipMatrix B * liftPerm p * (flipMatrix A)⁻¹, ?_, ?_⟩
    · exact (lifted_mem_color_iff A B p).mpr hp
    · exact (mem_encoded_coset_iff A B _).mpr ⟨p, rfl⟩
  · rintro ⟨k, hk, hcoset⟩
    rcases (mem_encoded_coset_iff A B k).mp hcoset with ⟨p, rfl⟩
    exact ⟨p, (lifted_mem_color_iff A B p).mp hk⟩

end Qatlib.Concepts.GraphQuery.CosetReduction
