/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.QueryComplexity.DegreeMethod.SensitivityDefinitions

/-!
# Sensitive blocks and bounded certificates

This module develops the combinatorics of disjoint sensitive blocks and minimum
certificates for Boolean functions. These quantities support comparisons between
decision-tree complexity and polynomial degree in [BealsEtAl2001].

`MinimalSensitive` isolates inclusion-minimal blocks. A maximal family of disjoint
minimal blocks yields a certificate whose size is bounded by squared block sensitivity.

## Main statements

* `sensitiveFamily_card_le`: disjoint sensitive families are bounded by block sensitivity.
* `minimal_sensitive_card_le`: minimal sensitive blocks have bounded cardinality.
* `bounded_certificate`: every input has a certificate of size at most squared block
  sensitivity.

## References

* [Beals et al., 2001][BealsEtAl2001]
-/

set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false

noncomputable section
open Qatlib.Concepts.QueryComplexity.DegreeMethod

namespace Qatlib.Concepts.QueryComplexity.DegreeMethod.SensitivityCombinatorics
open Qatlib
open scoped Classical

variable {N : ℕ}

/-- A finite family of sensitive blocks at `x` whose distinct members are pairwise disjoint. -/
def SensitiveFamily (f : (Fin N → Bool) → Bool) (x : Fin N → Bool)
    (F : Finset (Finset (Fin N))) : Prop :=
  (∀ B ∈ F, BlockSensitive f x B) ∧
    ∀ B ∈ F, ∀ C ∈ F, B ≠ C → B ∩ C = ∅

/-- Block sensitivity at a fixed input is at most global block sensitivity. -/
lemma blockSensitivityAt_le (f : (Fin N → Bool) → Bool) (x : Fin N → Bool) :
    blockSensitivityAt f x ≤ blockSensitivity f := by
  exact Finset.le_sup (f := id) (Finset.mem_image.mpr ⟨x, Finset.mem_univ x, rfl⟩)

/-- The cardinality of any disjoint sensitive-block family is at most global block sensitivity. -/
lemma sensitiveFamily_card_le (f : (Fin N → Bool) → Bool) (x : Fin N → Bool)
    (F : Finset (Finset (Fin N))) (hF : SensitiveFamily f x F) :
    F.card ≤ blockSensitivity f := by
  have hat : F.card ≤ blockSensitivityAt f x := by
    unfold blockSensitivityAt
    apply Finset.le_sup (f := Finset.card)
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ F, hF⟩
  exact hat.trans (blockSensitivityAt_le f x)

/-- Flipping the empty block leaves the input unchanged. -/
@[simp] lemma flipBlock_empty (x : Fin N → Bool) : flipBlock x ∅ = x := by
  funext i
  simp [flipBlock]

/-- Every sensitive block is nonempty. -/
lemma sensitive_nonempty {f : (Fin N → Bool) → Bool} {x : Fin N → Bool}
    {B : Finset (Fin N)} (h : BlockSensitive f x B) : B.Nonempty := by
  apply Finset.nonempty_iff_ne_empty.mpr
  intro he
  simp [BlockSensitive, he] at h

/-- The subset of `S` on which Boolean inputs `x` and `y` differ. -/
def differing (x y : Fin N → Bool) (S : Finset (Fin N)) : Finset (Fin N) :=
  S.filter fun i => x i ≠ y i

/-- The coordinates on which two inputs differ within `S` form a subset of `S`. -/
lemma differing_subset (x y : Fin N → Bool) (S : Finset (Fin N)) :
    differing x y S ⊆ S := Finset.filter_subset _ _

/-- Flipping the differing coordinates within `S` makes `x` agree with `y` at every coordinate
in `S`. -/
lemma flip_differing_on (x y : Fin N → Bool) (S : Finset (Fin N))
    (i : Fin N) (hi : i ∈ S) : flipBlock x (differing x y S) i = y i := by
  simp only [flipBlock, differing, Finset.mem_filter, hi, true_and]
  cases hx : x i <;> cases hy : y i <;> simp

/-- Flipping all coordinates on which two Boolean inputs differ transforms the first input into
the second. -/
lemma flip_differing_univ (x y : Fin N → Bool) : flipBlock x (differing x y Finset.univ) = y := by
  funext i
  exact flip_differing_on x y Finset.univ i (Finset.mem_univ i)

/-- If two inputs agree on `K`, their differing coordinates within any set `S` are disjoint from
`K`. -/
lemma differing_disjoint {x y : Fin N → Bool} {S K : Finset (Fin N)}
    (h : ∀ i ∈ K, x i = y i) : differing x y S ∩ K = ∅ := by
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro i hi
  obtain ⟨hiS, hiK⟩ := Finset.mem_inter.mp hi
  exact (Finset.mem_filter.mp hiS).2 (h i hiK)

/-- Adding a sensitive block disjoint from every existing block preserves the sensitive-family
property and increases its cardinality by one. -/
lemma sensitiveFamily_insert {f : (Fin N → Bool) → Bool} {x : Fin N → Bool}
    {F : Finset (Finset (Fin N))} {B : Finset (Fin N)}
    (hF : SensitiveFamily f x F) (hB : BlockSensitive f x B)
    (hd : ∀ C ∈ F, B ∩ C = ∅) :
    SensitiveFamily f x (insert B F) ∧ (insert B F).card = F.card + 1 := by
  have hn : B ∉ F := by
    intro hm
    have he := hd B hm
    simp only [Finset.inter_self] at he
    exact (sensitive_nonempty hB).ne_empty he
  refine ⟨⟨?_, ?_⟩, Finset.card_insert_of_notMem hn⟩
  · intro C hC
    rcases Finset.mem_insert.mp hC with rfl | hC
    · exact hB
    · exact hF.1 C hC
  · intro C hC D hD hne
    rcases Finset.mem_insert.mp hC with hCB | hCF
    · subst C
      rcases Finset.mem_insert.mp hD with hDB | hDF
      · exact (hne hDB.symm).elim
      · exact hd D hDF
    · rcases Finset.mem_insert.mp hD with hDB | hDF
      · subst D
        rw [Finset.inter_comm]
        exact hd C hCF
      · exact hF.2 C hCF D hDF hne

/-- The minimum certificate size at an input is at most the size of any certificate for that
input. -/
lemma certificateSizeAt_le {f : (Fin N → Bool) → Bool} {x : Fin N → Bool}
    {S : Finset (Fin N)} (hS : IsCertificateFor f x S) : certificateSizeAt f x ≤ S.card := by
  apply Nat.sInf_le
  exact Finset.mem_image.mpr ⟨S, Finset.mem_filter.mpr ⟨Finset.mem_univ S, hS⟩, rfl⟩

/-- The minimum certificate size at a fixed input is at most global certificate complexity. -/
lemma certificateSizeAt_le_global (f : (Fin N → Bool) → Bool) (x : Fin N → Bool) :
    certificateSizeAt f x ≤ certificateComplexity f := by
  exact Finset.le_sup (f := id) (Finset.mem_image.mpr ⟨x, Finset.mem_univ x, rfl⟩)

/-- At an input where `f` is true, the minimum certificate size is at most one-certificate
complexity. -/
lemma certificateSizeAt_le_one {f : (Fin N → Bool) → Bool} {x : Fin N → Bool}
    (hx : f x = true) : certificateSizeAt f x ≤ oneCertificateComplexity f := by
  exact Finset.le_sup (f := id) (Finset.mem_image.mpr
    ⟨x, Finset.mem_filter.mpr ⟨Finset.mem_univ x, hx⟩, rfl⟩)

/-- Every Boolean input possesses a certificate realizing its minimum certificate size. -/
lemma certificate_minimum (f : (Fin N → Bool) → Bool) (x : Fin N → Bool) :
    ∃ S, IsCertificateFor f x S ∧ S.card = certificateSizeAt f x := by
  have hu : IsCertificateFor f x Finset.univ := by
    intro y hy
    have he : y = x := funext fun i => hy i (Finset.mem_univ i)
    rw [he]
  have hn : ((Finset.univ.filter fun S : Finset (Fin N) => IsCertificateFor f x S).image
      Finset.card : Set ℕ).Nonempty :=
    ⟨Finset.univ.card, Finset.mem_image.mpr
      ⟨Finset.univ, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hu⟩, rfl⟩⟩
  obtain ⟨S, hS, hcard⟩ := Finset.mem_image.mp (Nat.sInf_mem hn)
  exact ⟨S, (Finset.mem_filter.mp hS).2, hcard⟩

/-- A sensitive block containing no proper sensitive subset at the given input. -/
def MinimalSensitive (f : (Fin N → Bool) → Bool) (x : Fin N → Bool)
    (B : Finset (Fin N)) : Prop :=
  BlockSensitive f x B ∧ ∀ C, C ⊂ B → ¬ BlockSensitive f x C

/-- Every sensitive block contains an inclusion-minimal sensitive block. -/
lemma minimal_sensitive_subset {f : (Fin N → Bool) → Bool} {x : Fin N → Bool}
    {B : Finset (Fin N)} (hB : BlockSensitive f x B) :
    ∃ C, C ⊆ B ∧ MinimalSensitive f x C := by
  let T := B.powerset.filter (BlockSensitive f x)
  have hn : T.Nonempty := ⟨B, by simp [T, hB]⟩
  obtain ⟨C, hC, hmin⟩ := Finset.exists_min_image T Finset.card hn
  have hmem := Finset.mem_filter.mp hC
  refine ⟨C, Finset.mem_powerset.mp hmem.1, hmem.2, ?_⟩
  intro D hD hd
  have hDT : D ∈ T := Finset.mem_filter.mpr
    ⟨Finset.mem_powerset.mpr (hD.1.trans (Finset.mem_powerset.mp hmem.1)), hd⟩
  have hle := hmin D hDT
  have hlt := Finset.card_lt_card hD
  omega

/-- Flipping a block and then flipping one of its coordinates equals flipping the block with
that coordinate erased. -/
lemma flip_erase_singleton (x : Fin N → Bool) (B : Finset (Fin N))
    (i : Fin N) (hi : i ∈ B) :
    flipBlock (flipBlock x B) {i} = flipBlock x (B.erase i) := by
  funext j
  by_cases hj : j = i
  · subst j
    simp [flipBlock, hi]
  · simp [flipBlock, hj]

/-- The cardinality of an inclusion-minimal sensitive block is at most global block sensitivity. -/
lemma minimal_sensitive_card_le {f : (Fin N → Bool) → Bool} {x : Fin N → Bool}
    {B : Finset (Fin N)} (hB : MinimalSensitive f x B) : B.card ≤ blockSensitivity f := by
  let F := B.image fun i => ({i} : Finset (Fin N))
  have hF : SensitiveFamily f (flipBlock x B) F := by
    constructor
    · intro C hC
      obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hC
      have herase := hB.2 (B.erase i) (Finset.erase_ssubset hi)
      have he : f x = f (flipBlock x (B.erase i)) := by
        simpa only [BlockSensitive, not_not] using herase
      unfold BlockSensitive
      rw [flip_erase_singleton x B i hi, ← he]
      exact hB.1.symm
    · intro C hC D hD hne
      obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hC
      obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hD
      have hij : i ≠ j := fun h => hne (h ▸ rfl)
      simp [hij]
  have hcard : F.card = B.card := Finset.card_image_iff.mpr (by
    intro i _ j _ h
    simpa using h)
  rw [← hcard]
  exact sensitiveFamily_card_le f (flipBlock x B) F hF

/-- Every input possesses a certificate of size at most the square of the function's block
sensitivity. -/
lemma bounded_certificate (f : (Fin N → Bool) → Bool) (x : Fin N → Bool) :
    ∃ S, IsCertificateFor f x S ∧ S.card ≤ blockSensitivity f ^ 2 := by
  let T := Finset.univ.filter fun F : Finset (Finset (Fin N)) =>
    SensitiveFamily f x F ∧ ∀ B ∈ F, MinimalSensitive f x B
  have hn : T.Nonempty := ⟨∅, by simp [T, SensitiveFamily, Set.PairwiseDisjoint]⟩
  obtain ⟨F, hF, hmax⟩ := Finset.exists_max_image T Finset.card hn
  have hFs := (Finset.mem_filter.mp hF).2
  let S := F.biUnion id
  refine ⟨S, ?_, ?_⟩
  · intro y hy
    by_contra hneq
    have hdiff : BlockSensitive f x (differing x y Finset.univ) := by
      simpa [BlockSensitive, flip_differing_univ, ne_comm] using hneq
    obtain ⟨B, hBsub, hBmin⟩ := minimal_sensitive_subset hdiff
    have hd : ∀ C ∈ F, B ∩ C = ∅ := by
      intro C hC
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro i hi
      obtain ⟨hiB, hiC⟩ := Finset.mem_inter.mp hi
      have hiy : x i ≠ y i := (Finset.mem_filter.mp (hBsub hiB)).2
      have hiS : i ∈ S := Finset.mem_biUnion.mpr ⟨C, hC, hiC⟩
      exact hiy (hy i hiS).symm
    have hext := sensitiveFamily_insert hFs.1 hBmin.1 hd
    have hnew : insert B F ∈ T := by
      refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, hext.1, ?_⟩
      intro C hC
      rcases Finset.mem_insert.mp hC with rfl | hC
      · exact hBmin
      · exact hFs.2 C hC
    have hle := hmax (insert B F) hnew
    rw [hext.2] at hle
    omega
  · calc
      S.card ≤ ∑ B ∈ F, B.card := Finset.card_biUnion_le
      _ ≤ ∑ _B ∈ F, blockSensitivity f :=
        Finset.sum_le_sum fun B hB => minimal_sensitive_card_le (hFs.2 B hB)
      _ = F.card * blockSensitivity f := by simp
      _ ≤ blockSensitivity f * blockSensitivity f :=
        Nat.mul_le_mul_right _ (sensitiveFamily_card_le f x F hFs.1)
      _ = blockSensitivity f ^ 2 := (pow_two _).symm

end Qatlib.Concepts.QueryComplexity.DegreeMethod.SensitivityCombinatorics
