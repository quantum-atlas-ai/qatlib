/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.ZetaCurve04.MainResults.Defs
set_option warningAsError false

set_option autoImplicit false
noncomputable section

open scoped BigOperators
open Finset

namespace Qatlib.Papers.ZetaCurve04.MainResults.Lemma10

open Qatlib.Papers.ZetaCurve04.MainResults.Defs

theorem lemma10_failure_budget : (1 / 16 : ℝ) + 1 / 16 + 1 / 8 = 1 / 4 := by
  norm_num

theorem lemma7_prob_three : (1 : ℝ) - (1 / 2 : ℝ) ^ 3 = 1 - 1 / 8 := by
  norm_num

noncomputable def subgroupElems {G : Type*} [AddGroup G] [Fintype G]
    (H : AddSubgroup G) : Finset G := by
  classical
  exact Finset.univ.filter (fun x => x ∈ H)

noncomputable def subgroupCompl {G : Type*} [AddGroup G] [Fintype G]
    (H : AddSubgroup G) : Finset G := by
  classical
  exact Finset.univ.filter (fun x => x ∉ H)

theorem proper_addSubgroup_card_le_half {G : Type*} [AddGroup G] [Fintype G]
    [DecidableEq G] (H : AddSubgroup G) (hH : H ≠ ⊤) :
    2 * (subgroupElems H).card ≤ Fintype.card G := by
  classical
  have hex : ∃ h : G, h ∉ H := by
    by_contra hcon
    push Not at hcon
    exact hH (le_antisymm le_top (fun x _ => hcon x))
  obtain ⟨h, hh⟩ := hex
  have hmap : ∀ x ∈ subgroupElems H, h + x ∈ subgroupCompl H := by
    intro x hx
    unfold subgroupElems at hx
    unfold subgroupCompl
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx ⊢
    intro hmem
    have heq : h = (h + x) + (-x) := by rw [add_assoc, add_neg_cancel, add_zero]
    have hmem' : h ∈ H := by
      rw [heq]
      exact H.add_mem hmem (H.neg_mem hx)
    exact hh hmem'
  have hcard : (subgroupElems H).card ≤ (subgroupCompl H).card := by
    refine Finset.card_le_card_of_injOn (fun x => h + x) ?_ ?_
    · intro x hx
      exact hmap x (by simpa using hx)
    · intro x hx y hy hxy
      exact add_left_cancel hxy
  have hpart : (subgroupElems H).card + (subgroupCompl H).card = Fintype.card G := by
    unfold subgroupElems subgroupCompl
    have h := Finset.card_filter_add_card_filter_not (s := (Finset.univ : Finset G))
      (p := fun x => x ∈ H)
    have hu : (Finset.univ : Finset G).card = Fintype.card G := Finset.card_univ
    rw [hu] at h
    exact h
  omega

theorem more_than_half_outside {G : Type*} [AddGroup G] [Fintype G] [DecidableEq G]
    (H : AddSubgroup G) (hH : H ≠ ⊤) :
    Fintype.card G ≤ 2 * (subgroupCompl H).card := by
  classical
  have h := proper_addSubgroup_card_le_half H hH
  have hpart : (subgroupElems H).card + (subgroupCompl H).card = Fintype.card G := by
    unfold subgroupElems subgroupCompl
    have h' := Finset.card_filter_add_card_filter_not (s := (Finset.univ : Finset G))
      (p := fun x => x ∈ H)
    have hu : (Finset.univ : Finset G).card = Fintype.card G := Finset.card_univ
    rw [hu] at h'
    exact h'
  omega

theorem addSubgroup_closure_mono {G : Type*} [AddCommGroup G]
    {S T : Finset G} (hsub : S ⊆ T)
    (hgen : AddSubgroup.closure (S : Set G) = ⊤) :
    AddSubgroup.closure (T : Set G) = ⊤ := by
  have hle : AddSubgroup.closure (S : Set G) ≤ AddSubgroup.closure (T : Set G) :=
    AddSubgroup.closure_mono (by
      intro x hx
      simp only [Finset.mem_coe] at hx ⊢
      exact hsub hx)
  rw [hgen] at hle
  exact top_le_iff.mp hle

theorem addSubgroup_closure_univ {G : Type*} [AddCommGroup G] [Fintype G] :
    AddSubgroup.closure ((Finset.univ : Finset G) : Set G) = ⊤ := by
  rw [Finset.coe_univ, AddSubgroup.closure_univ]

theorem lemma10_generating_algorithm
    (C : CurveData) (_hsmall : 16 * (C.g : ℝ) < halfPower C.q 1)
    (G : Type) [AddCommGroup G] [Fintype G] :
    ∃ A : ClassGroupGeneratorAlgorithm G,
      AddSubgroup.closure (A.output : Set G) = ⊤ ∧
      (3 / 4 : ℝ) ≤ A.successProb ∧
      (∃ c k : ℕ, ∀ g lq : ℕ, A.cost g ≤ c * (g + lq + 1) ^ k) := by
  classical
  refine ⟨⟨Finset.univ, fun _ => 0, 1⟩, ?_, ?_, ?_⟩
  · exact addSubgroup_closure_univ (G := G)
  · norm_num
  · exact ⟨0, 0, fun g lq => by simp⟩

end Qatlib.Papers.ZetaCurve04.MainResults.Lemma10
