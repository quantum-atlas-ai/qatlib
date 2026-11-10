/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.QueryComplexity.DegreeMethod.SensitivityDefinitions
set_option backward.isDefEq.respectTransparency false
set_option warningAsError false

set_option autoImplicit false

noncomputable section
open Qatlib.Concepts.QueryComplexity.DegreeMethod

namespace Qatlib.Concepts.QueryComplexity.DegreeMethod.SensitivityCombinatorics
open Qatlib
open scoped Classical

variable {N : ℕ}

def SensitiveFamily (f : (Fin N → Bool) → Bool) (x : Fin N → Bool)
    (F : Finset (Finset (Fin N))) : Prop :=
  (∀ B ∈ F, BlockSensitive f x B) ∧
    ∀ B ∈ F, ∀ C ∈ F, B ≠ C → B ∩ C = ∅

lemma blockSensitivityAt_le (f : (Fin N → Bool) → Bool) (x : Fin N → Bool) :
    blockSensitivityAt f x ≤ blockSensitivity f := by
  exact Finset.le_sup (f := id) (Finset.mem_image.mpr ⟨x, Finset.mem_univ x, rfl⟩)

lemma sensitiveFamily_card_le (f : (Fin N → Bool) → Bool) (x : Fin N → Bool)
    (F : Finset (Finset (Fin N))) (hF : SensitiveFamily f x F) :
    F.card ≤ blockSensitivity f := by
  have hat : F.card ≤ blockSensitivityAt f x := by
    unfold blockSensitivityAt
    apply Finset.le_sup (f := Finset.card)
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ F, hF⟩
  exact hat.trans (blockSensitivityAt_le f x)

@[simp] lemma flipBlock_empty (x : Fin N → Bool) : flipBlock x ∅ = x := by
  funext i
  simp [flipBlock]

lemma sensitive_nonempty {f : (Fin N → Bool) → Bool} {x : Fin N → Bool}
    {B : Finset (Fin N)} (h : BlockSensitive f x B) : B.Nonempty := by
  apply Finset.nonempty_iff_ne_empty.mpr
  intro he
  simp [BlockSensitive, he] at h

def differing (x y : Fin N → Bool) (S : Finset (Fin N)) : Finset (Fin N) :=
  S.filter fun i => x i ≠ y i

lemma differing_subset (x y : Fin N → Bool) (S : Finset (Fin N)) :
    differing x y S ⊆ S := Finset.filter_subset _ _

lemma flip_differing_on (x y : Fin N → Bool) (S : Finset (Fin N))
    (i : Fin N) (hi : i ∈ S) : flipBlock x (differing x y S) i = y i := by
  simp only [flipBlock, differing, Finset.mem_filter, hi, true_and]
  cases hx : x i <;> cases hy : y i <;> simp

lemma flip_differing_univ (x y : Fin N → Bool) : flipBlock x (differing x y Finset.univ) = y := by
  funext i
  exact flip_differing_on x y Finset.univ i (Finset.mem_univ i)

lemma differing_disjoint {x y : Fin N → Bool} {S K : Finset (Fin N)}
    (h : ∀ i ∈ K, x i = y i) : differing x y S ∩ K = ∅ := by
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro i hi
  obtain ⟨hiS, hiK⟩ := Finset.mem_inter.mp hi
  exact (Finset.mem_filter.mp hiS).2 (h i hiK)

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

lemma certificateSizeAt_le {f : (Fin N → Bool) → Bool} {x : Fin N → Bool}
    {S : Finset (Fin N)} (hS : IsCertificateFor f x S) : certificateSizeAt f x ≤ S.card := by
  apply Nat.sInf_le
  exact Finset.mem_image.mpr ⟨S, Finset.mem_filter.mpr ⟨Finset.mem_univ S, hS⟩, rfl⟩

lemma certificateSizeAt_le_global (f : (Fin N → Bool) → Bool) (x : Fin N → Bool) :
    certificateSizeAt f x ≤ certificateComplexity f := by
  exact Finset.le_sup (f := id) (Finset.mem_image.mpr ⟨x, Finset.mem_univ x, rfl⟩)

lemma certificateSizeAt_le_one {f : (Fin N → Bool) → Bool} {x : Fin N → Bool}
    (hx : f x = true) : certificateSizeAt f x ≤ oneCertificateComplexity f := by
  exact Finset.le_sup (f := id) (Finset.mem_image.mpr
    ⟨x, Finset.mem_filter.mpr ⟨Finset.mem_univ x, hx⟩, rfl⟩)

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

def MinimalSensitive (f : (Fin N → Bool) → Bool) (x : Fin N → Bool)
    (B : Finset (Fin N)) : Prop :=
  BlockSensitive f x B ∧ ∀ C, C ⊂ B → ¬ BlockSensitive f x C

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

lemma flip_erase_singleton (x : Fin N → Bool) (B : Finset (Fin N))
    (i : Fin N) (hi : i ∈ B) :
    flipBlock (flipBlock x B) {i} = flipBlock x (B.erase i) := by
  funext j
  by_cases hj : j = i
  · subst j
    simp [flipBlock, hi]
  · simp [flipBlock, hj]

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
