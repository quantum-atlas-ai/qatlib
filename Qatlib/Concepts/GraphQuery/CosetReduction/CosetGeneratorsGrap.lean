/-
Copyright (c) 2026 Quantum Atlas Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quantum Atlas Contributors
-/

module

public import Qatlib.Concepts.GraphQuery.CosetReduction.CosetGeneratorsStat

@[expose] public section

set_option autoImplicit false

namespace Qatlib.Concepts.GraphQuery.CosetReduction

/-- Shows that the encoded generators generate exactly `encodedSubgroup`. -/
private theorem encodedGenerator_closure (n : ℕ) (A : BoolMatrix (Fin n)) :
    Subgroup.closure (Set.range (encodedGenerator A)) = encodedSubgroup A := by
  classical
  let C := Subgroup.closure (Set.range (encodedGenerator A))
  let f : Equiv.Perm (Fin n) →* Equiv.Perm (Position (Fin n)) :=
    (MulAut.conj (flipMatrix A)).toMonoidHom.comp (liftHom (Fin n))
  have hf (p : Equiv.Perm (Fin n)) : f p ∈ C := by
    induction p using Equiv.Perm.swap_induction_on with
    | one => simpa only [map_one] using C.one_mem
    | swap_mul p i j _ ih =>
      rw [map_mul]
      apply C.mul_mem _ ih
      exact Subgroup.subset_closure ⟨(i, j), rfl⟩
  apply le_antisymm
  · apply (Subgroup.closure_le (encodedSubgroup A)).mpr
    rintro p ⟨ij, rfl⟩
    exact Subgroup.mem_map.mpr
      ⟨liftPerm (Equiv.swap ij.1 ij.2), ⟨Equiv.swap ij.1 ij.2, rfl⟩, rfl⟩
  · intro p hp
    rcases Subgroup.mem_map.mp hp with ⟨q, hq, rfl⟩
    rcases hq with ⟨r, rfl⟩
    exact hf r

/-- Shows that the color generators generate exactly `colorSubgroup`. -/
private theorem colorGenerator_closure (n : ℕ) :
    Subgroup.closure (Set.range (colorGenerator n)) = colorSubgroup (Fin n) := by
  classical
  let S : Set (Equiv.Perm (Position (Fin n))) :=
    {p | ∃ x y : Position (Fin n), x.2 = y.2 ∧ x ≠ y ∧ Equiv.swap x y = p}
  have hS : ∀ p ∈ S, p.IsSwap := by
    rintro p ⟨x, y, _, hxy, rfl⟩
    exact ⟨x, y, hxy, rfl⟩
  have hSrange : S ⊆ Set.range (colorGenerator n) := by
    rintro p ⟨⟨a, b⟩, ⟨c, d⟩, hcolor, _, rfl⟩
    change b = d at hcolor
    subst d
    exact ⟨((a, c), b), rfl⟩
  apply le_antisymm
  · apply (Subgroup.closure_le (colorSubgroup (Fin n))).mpr
    rintro p ⟨z, rfl⟩
    intro x
    change (Equiv.swap (z.1.1, z.2) (z.1.2, z.2) x).2 = x.2
    by_cases hleft : x = (z.1.1, z.2)
    · subst x
      simp only [Equiv.swap_apply_left]
    by_cases hright : x = (z.1.2, z.2)
    · subst x
      simp only [Equiv.swap_apply_right]
    rw [Equiv.swap_apply_of_ne_of_ne hleft hright]
  · intro p hp
    apply Subgroup.closure_mono hSrange
    apply (mem_closure_isSwap hS).mpr
    refine ⟨Set.toFinite _, ?_⟩
    intro x
    by_cases hfix : p x = x
    · refine ⟨⟨1, (Subgroup.closure S).one_mem⟩, ?_⟩
      simpa only [Equiv.Perm.smul_def, Equiv.Perm.one_apply] using! hfix.symm
    · refine ⟨⟨Equiv.swap x (p x), Subgroup.subset_closure ?_⟩, ?_⟩
      · exact ⟨x, p x, (hp x).symm, Ne.symm hfix, rfl⟩
      · exact Equiv.swap_apply_left x (p x)

/-- Establishes the coset generator construction specified by `CosetGenerators`. -/
theorem cosetGenerators : CosetGenerators := by
  intro n A
  refine ⟨encodedGenerator_closure n A, colorGenerator_closure n, ?_, ?_, ?_⟩ <;>
    simp [Position, VertexSwapIndex, ColorSwapIndex, Fintype.card_prod,
      pow_succ, mul_comm, mul_left_comm, mul_assoc]

end Qatlib.Concepts.GraphQuery.CosetReduction
