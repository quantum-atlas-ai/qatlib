/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.StabilizerAlg.NearUniformGen.NearUniformGenerationSubgoalStat
import Qatlib.Concepts.StabilizerAlg.NearUniformGen.MaximalSubgroupEnumerationSubgoalQuan
set_option warningAsError false

open Qatlib.Concepts.MonteCarloMean.FinDistBounds.FinDist

open Qatlib.Concepts.MonteCarloMean.FinDistBounds

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
namespace Qatlib.Concepts.StabilizerAlg.NearUniformGen
open scoped BigOperators Classical

theorem asp_probability_congr {X : Type*} [Fintype X] [DecidableEq X]
    (l : ℕ) (μ : FinDist X) (E F : (Fin l → X) → Prop)
    [DecidablePred E] [DecidablePred F] (hEF : ∀ hs, E hs ↔ F hs) :
    FinDist.probEvent μ E=FinDist.probEvent μ F := by
  unfold FinDist.probEvent
  apply Finset.sum_congr
  · ext hs
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact hEF hs
  · intro hs _
    rfl

theorem asp_probability_mono {X : Type*} [Fintype X] [DecidableEq X]
    (l : ℕ) (μ : FinDist X) (E F : (Fin l → X) → Prop)
    [DecidablePred E] [DecidablePred F] (hEF : ∀ hs, E hs → F hs) :
    FinDist.probEvent μ E ≤ FinDist.probEvent μ F := by
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · intro hs hhs
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hEF hs (Finset.mem_filter.mp hhs).2⟩
  · intro hs _ _
    exact Finset.prod_nonneg (fun i _ => μ.nonneg (hs i))

theorem asp_probability_union {X J : Type*} [Fintype X] [DecidableEq X] [Fintype J]
    (l : ℕ) (μ : FinDist X) (E : J → (Fin l → X) → Prop)
    [∀ j, DecidablePred (E j)] [DecidablePred (fun hs => ∃ j, E j hs)] :
    FinDist.probEvent μ (fun hs => ∃ j, E j hs) ≤ ∑ j, FinDist.probEvent μ (E j) := by
  let e := Fintype.equivFin J
  have hu := FinDist.union_bound μ (fun a : Fin (Fintype.card J) => E (e.symm a))
  have he : (fun hs : Fin l → X => ∃ a : Fin (Fintype.card J), E (e.symm a) hs)=
      (fun hs => ∃ j : J, E j hs) := by
    funext hs
    apply propext
    constructor
    · rintro ⟨a,ha⟩; exact ⟨e.symm a,ha⟩
    · rintro ⟨j,hj⟩; exact ⟨e j,by simpa using hj⟩
  simp only [he] at hu
  rw [e.symm.sum_comp (fun j => FinDist.probEvent μ (E j))] at hu
  exact hu

theorem asp_probability_coordinate {X : Type*} [Fintype X] [DecidableEq X]
    (l : ℕ) (μ : FinDist X) (i : Fin l) (A : Finset X) :
    FinDist.probEvent μ (fun hs : Fin l → X => hs i ∈ A)=∑ x ∈ A, μ.prob x := by
  unfold FinDist.probEvent
  rw [Finset.sum_filter]
  calc
    _ = ∑ hs : Fin l → X, μ.probOf hs*(if hs i ∈ A then 1 else 0) := by
      apply Finset.sum_congr rfl
      intro hs _
      by_cases ha : hs i ∈ A <;> simp [ha]
    _ = ∑ x : X, μ.prob x*(if x ∈ A then 1 else 0) :=
      FinDist.expect_coord μ i (fun x => if x ∈ A then (1 : ℝ) else 0)
    _ = _ := by simp only [mul_ite, mul_one, mul_zero, Finset.sum_ite_mem, Finset.univ_inter]

theorem asp_probability_all {X : Type*} [Fintype X] [DecidableEq X]
    (l : ℕ) (μ : FinDist X) (A : Finset X) :
    FinDist.probEvent μ (fun hs : Fin l → X => ∀ i, hs i ∈ A)=(∑ x ∈ A, μ.prob x)^l := by
  have hi (hs : Fin l → X) : (∏ i, (if hs i ∈ A then (1 : ℝ) else 0))=
      if ∀ i, hs i ∈ A then 1 else 0 := by
    by_cases ha : ∀ i, hs i ∈ A
    · simp [ha]
    · rw [if_neg ha]
      obtain ⟨i,hi⟩ := not_forall.mp ha
      apply Finset.prod_eq_zero (Finset.mem_univ i)
      simp [hi]
  unfold FinDist.probEvent
  rw [Finset.sum_filter]
  calc
    _ = ∑ hs : Fin l → X, μ.probOf hs*∏ i, (if hs i ∈ A then (1 : ℝ) else 0) := by
      apply Finset.sum_congr rfl
      intro hs _
      rw [hi]
      by_cases ha : ∀ i, hs i ∈ A <;> simp [ha]
    _ = ∏ _i : Fin l, (∑ x : X, μ.prob x*(if x ∈ A then (1 : ℝ) else 0)) :=
      FinDist.expect_prod μ (fun _ x => if x ∈ A then (1 : ℝ) else 0)
    _ = _ := by
      simp only [mul_ite, mul_one, mul_zero, Finset.sum_ite_mem, Finset.univ_inter, Finset.prod_const,
        Finset.card_univ, Fintype.card_fin]

theorem asp_proper_subgroup_card_half {H : Type*} [AddCommGroup H] [Fintype H]
    (L : AddSubgroup H) (hL : L < ⊤) : 2*Fintype.card L ≤ Fintype.card H := by
  have hi : 2 ≤ L.index := by have := L.one_lt_index_of_ne_top hL.ne; omega
  have h := Nat.mul_le_mul_left (Fintype.card L) hi
  have hc := L.card_mul_index
  rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card] at hc
  nlinarith

theorem asp_subtype_mass {G : Type*} [AddCommGroup G] [Fintype G] [DecidableEq G]
    (H : AddSubgroup G) (μ : FinDist G) (A : Finset ↥H) :
    (∑ x ∈ A.image (fun h : H => (h : G)), μ.prob x)=∑ h ∈ A, μ.prob (h : G) := by
  rw [Finset.sum_image]
  intro a _ b _ he
  exact Subtype.ext he

theorem nearUniformGenerationSubgoal : NearUniformGenerationSubgoal := by
  intro l G _ _ _ H μ δ hδ hnear
  obtain ⟨maxs,hproper,hcover,hcount⟩ := maximalSubgroupEnumerationSubgoal ↥H
  let AH : Finset G := Finset.univ.image (fun x : H => (x : G))
  let A : AddSubgroup ↥H → Finset G := fun L =>
    (L : Set ↥H).toFinset.image (fun x : H => (x : G))
  have hcardpos : (0 : ℝ) < Fintype.card ↥H := by exact_mod_cast Fintype.card_pos (α := ↥H)
  have hAH : (∑ x ∈ AH, μ.prob x) ≥ 1-δ := by
    have hn := (abs_le.mp (hnear Finset.univ)).1
    rw [Finset.card_univ, div_self hcardpos.ne'] at hn
    rw [asp_subtype_mass]
    linarith
  have hbad : (∑ x ∈ AHᶜ, μ.prob x) ≤ δ := by
    have ht : (∑ x ∈ AH, μ.prob x)+(∑ x ∈ AHᶜ, μ.prob x)=1 := by
      rw [Finset.sum_add_sum_compl, μ.sum_one]
    linarith
  have hA (L : ↥maxs) : (∑ x ∈ A L, μ.prob x) ≤ 1/2+δ := by
    have hn := (abs_le.mp (hnear ((L : AddSubgroup ↥H) : Set ↥H).toFinset)).2
    have hc : (2 : ℝ)*Fintype.card (L : AddSubgroup ↥H) ≤ Fintype.card ↥H := by
      exact_mod_cast asp_proper_subgroup_card_half (L : AddSubgroup ↥H) (hproper L L.property)
    have hf : (Fintype.card (L : AddSubgroup ↥H) : ℝ)/(Fintype.card ↥H : ℝ) ≤ 1/2 := by
      apply (div_le_iff₀ hcardpos).mpr
      linarith
    dsimp [A]
    rw [asp_subtype_mass]
    have hcardL : ((L : AddSubgroup ↥H) : Set ↥H).toFinset.card=
        Fintype.card (L : AddSubgroup ↥H) := by
      rw [Set.toFinset_card]
      exact Fintype.card_congr (Equiv.refl _)
    rw [hcardL] at hn
    linarith
  let E : (Fin l ⊕ ↥maxs) → (Fin l → G) → Prop := fun j hs =>
    Sum.elim (fun i => hs i ∈ AHᶜ) (fun L : ↥maxs => ∀ i, hs i ∈ A L) j
  have hfailure (hs : Fin l → G) (hfail : AddSubgroup.closure (Set.range hs) ≠ H) :
      ∃ j, E j hs := by
    by_cases hh : ∀ i, hs i ∈ H
    · let K := AddSubgroup.closure (Set.range hs)
      have hKH : K ≤ H := by
        apply (AddSubgroup.closure_le H).mpr
        rintro x ⟨i,rfl⟩
        exact hh i
      have hKproper : K.comap H.subtype < ⊤ := by
        apply lt_top_iff_ne_top.mpr
        intro he
        apply hfail
        apply le_antisymm hKH
        intro x hx
        have hm : (⟨x,hx⟩ : H) ∈ K.comap H.subtype := by rw [he]; trivial
        exact hm
      obtain ⟨L,hL,hKL⟩ := hcover (K.comap H.subtype) hKproper
      refine ⟨Sum.inr ⟨L,hL⟩, ?_⟩
      intro i
      apply Finset.mem_image.mpr
      refine ⟨⟨hs i,hh i⟩, ?_, rfl⟩
      apply Set.mem_toFinset.mpr
      apply hKL
      exact AddSubgroup.subset_closure ⟨i,rfl⟩
    · obtain ⟨i,hi⟩ := not_forall.mp hh
      refine ⟨Sum.inl i, ?_⟩
      apply Finset.mem_compl.mpr
      intro he
      obtain ⟨x,_hx,hxe⟩ := Finset.mem_image.mp he
      exact hi (hxe ▸ x.property)
  have hbound (j : Fin l ⊕ ↥maxs) : FinDist.probEvent μ (E j) ≤
      Sum.elim (fun _ : Fin l => δ) (fun _ : ↥maxs => (1/2+δ)^l) j := by
    cases j with
    | inl i =>
      have hh : FinDist.probEvent μ (fun hs : Fin l → G => hs i ∈ AHᶜ) ≤ δ := by
        rw [asp_probability_coordinate]
        exact hbad
      have hp := asp_probability_congr l μ (E (Sum.inl i))
        (fun hs => hs i ∈ AHᶜ) (fun _ => Iff.rfl)
      exact hp.le.trans hh
    | inr L =>
      have hh : FinDist.probEvent μ (fun hs : Fin l → G => ∀ i, hs i ∈ A L) ≤ (1/2+δ)^l := by
        rw [asp_probability_all]
        exact pow_le_pow_left₀ (Finset.sum_nonneg (fun x _ => μ.nonneg x)) (hA L) l
      have hp := asp_probability_congr l μ (E (Sum.inr L))
        (fun hs => ∀ i, hs i ∈ A L) (fun _ => Iff.rfl)
      exact hp.le.trans hh
  refine ⟨maxs,hproper,hcover,hcount,?_⟩
  calc
    _ ≤ FinDist.probEvent μ (fun hs : Fin l → G => ∃ j, E j hs) :=
      asp_probability_mono l μ _ _ hfailure
    _ ≤ ∑ j : Fin l ⊕ ↥maxs, FinDist.probEvent μ (E j) := asp_probability_union l μ E
    _ ≤ ∑ j : Fin l ⊕ ↥maxs,
        Sum.elim (fun _ : Fin l => δ) (fun _ : ↥maxs => (1/2+δ)^l) j :=
      Finset.sum_le_sum (fun j _ => hbound j)
    _ = _ := by
      rw [Fintype.sum_sum_type]
      simp only [Sum.elim_inl, Sum.elim_inr, Finset.sum_const, Finset.card_univ,
        Fintype.card_fin, Fintype.card_coe, nsmul_eq_mul]

end Qatlib.Concepts.StabilizerAlg.NearUniformGen
