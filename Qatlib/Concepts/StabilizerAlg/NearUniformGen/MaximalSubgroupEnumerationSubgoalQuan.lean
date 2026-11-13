/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.StabilizerAlg.NearUniformGen.MaximalSubgroupEnumerationSubgoalStat

/-!
# Character kernels and finite subgroup covers

`aspCharacterKernel` is the subgroup on which a complex additive character equals one. Finite
abelian duality supplies a nontrivial character vanishing on any proper subgroup, and
`maximalSubgroupEnumerationSubgoal` uses character kernels to construct a proper-subgroup cover
with fewer members than group elements. For background, see [Kitaev1995].

## Main statements

* `asp_proper_subgroup_character`: places each proper subgroup inside the kernel of a nontrivial
  character.
* `maximalSubgroupEnumerationSubgoal`: proves the existence and cardinality bound of a finite
  proper-subgroup cover.

## References

* [Kitaev, 1995][Kitaev1995]
-/

open Qatlib.Concepts.HspRecovery.BackendAudit
open Qatlib.Concepts.QuditTeleport.TeleportCore

set_option autoImplicit false
namespace Qatlib.Concepts.StabilizerAlg.NearUniformGen
open scoped Classical

/-- The additive subgroup of elements on which the complex additive character takes the value
one. -/
def aspCharacterKernel {H : Type*} [AddCommGroup H] (χ : AddChar H ℂ) : AddSubgroup H where
  carrier := {x | χ x=1}
  zero_mem' := χ.map_zero_eq_one
  add_mem' := by intro a b ha hb; change χ (a+b)=1; rw [χ.map_add_eq_mul, ha, hb, one_mul]
  neg_mem' := by intro a ha; change χ (-a)=1; rw [χ.map_neg_eq_inv, ha, inv_one]

/-- The kernel of a nontrivial complex additive character is not the whole group. -/
theorem aspCharacterKernel_ne_top {H : Type*} [AddCommGroup H] (χ : AddChar H ℂ)
    (hχ : χ ≠ 0) : aspCharacterKernel χ ≠ ⊤ := by
  intro he
  apply hχ
  ext x
  have hx : x ∈ aspCharacterKernel χ := by rw [he]; trivial
  simpa using! hx

/-- Every proper subgroup of a finite abelian group is contained in the kernel of a nontrivial
complex additive character. -/
theorem asp_proper_subgroup_character {H : Type*} [AddCommGroup H] [Fintype H]
    (L : AddSubgroup H) (hL : L < ⊤) :
    ∃ χ : AddChar H ℂ, χ ≠ 0 ∧ L ≤ aspCharacterKernel χ := by
  have hx : ∃ x : H, x ∉ L := by
    by_contra hn
    push Not at hn
    apply hL.ne
    ext x
    simp [hn x]
  obtain ⟨x,hx⟩ := hx
  have hnot : AddChar.doubleDualEmb x ∉ characterAnnihilator (characterAnnihilator L) := by
    intro he
    exact hx ((Qatlib.Concepts.HspRecovery.BackendAudit.doubleDualEmb_mem_characterAnnihilator_characterAnnihilator_iff L x).mp he)
  rw [mem_characterAnnihilator] at hnot
  push Not at hnot
  obtain ⟨χ,hχ⟩ := hnot
  change (χ : AddChar H ℂ) x ≠ 1 at hχ
  refine ⟨χ, ?_, ?_⟩
  · intro he
    simp [he] at hχ
  · intro y hy
    exact (mem_characterAnnihilator L (χ : AddChar H ℂ)).mp χ.property ⟨y,hy⟩

/-- Every finite abelian group has a finite family of proper subgroups covering all proper
subgroups by containment, with family cardinality strictly smaller than the group
cardinality. -/
theorem maximalSubgroupEnumerationSubgoal : MaximalSubgroupEnumerationSubgoal := by
  intro H _ _
  letI : Fintype (AddSubgroup H) := Fintype.ofInjective
    (fun L : AddSubgroup H => (L : Set H)) SetLike.coe_injective
  let maxs : Finset (AddSubgroup H) := Finset.univ.filter IsCoatom
  have hco (L : ↥maxs) : IsCoatom (L : AddSubgroup H) := (Finset.mem_filter.mp L.property).2
  have hproper (L : ↥maxs) : (L : AddSubgroup H) < ⊤ := (hco L).lt_top
  have hchars (L : ↥maxs) := asp_proper_subgroup_character (L : AddSubgroup H) (hproper L)
  let f : ↥maxs → AddChar H ℂ := fun L => Classical.choose (hchars L)
  have hfn (L : ↥maxs) : f L ≠ 0 := (Classical.choose_spec (hchars L)).1
  have hfle (L : ↥maxs) : (L : AddSubgroup H) ≤ aspCharacterKernel (f L) :=
    (Classical.choose_spec (hchars L)).2
  have hker (L : ↥maxs) : (L : AddSubgroup H)=aspCharacterKernel (f L) := by
    apply le_antisymm (hfle L)
    exact (isCoatom_iff_ge_of_le.mp (hco L)).2 _
      (aspCharacterKernel_ne_top (f L) (hfn L)) (hfle L)
  have hfi : Function.Injective f := by
    intro L K he
    apply Subtype.ext
    rw [hker L, hker K, he]
  have hzero : (0 : AddChar H ℂ) ∉ Set.range f := by
    rintro ⟨L,he⟩
    exact hfn L he
  have hcard := Fintype.card_lt_of_injective_of_notMem f hfi hzero
  refine ⟨maxs, ?_, ?_, ?_⟩
  · intro L hL
    exact (Finset.mem_filter.mp hL).2.lt_top
  · intro K hK
    obtain ⟨L,hL,hKL⟩ := (eq_top_or_exists_le_coatom K).resolve_left hK.ne
    exact ⟨L, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hL⟩, hKL⟩
  · simpa only [Fintype.card_coe, AddChar.card_eq] using hcard

end Qatlib.Concepts.StabilizerAlg.NearUniformGen
