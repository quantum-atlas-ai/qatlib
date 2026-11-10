/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.OverlapGapGoh26.GaussianBounds.ActualGround
set_option warningAsError false
set_option autoImplicit false
set_option maxHeartbeats 1600000
noncomputable section
open scoped Classical BigOperators
open Qatlib.Foundations.MatrixAlgebra.TensorDiff
namespace Qatlib.Papers.OverlapGapGoh26.GaussianBounds.Remainder

def repeated {q N : ℕ} (A : Tensor q N) : Tensor q N :=
    fun k=>if Function.Injective k then 0 else A k

def noRepeat {q N : ℕ} (A : Tensor q N) : Tensor q N :=
    fun k=>if Function.Injective k then A k else 0

theorem energy_decomposition {q N : ℕ} (A : Tensor q N) (u : Fin N→ℝ) :
    tensorEnergy A u=tensorEnergy (noRepeat A) u+tensorEnergy (repeated A) u := by
  rw [tensorEnergy,tensorEnergy,tensorEnergy,← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro k _
  by_cases h:Function.Injective k <;>simp [noRepeat,repeated,h]

theorem collision_card {q N : ℕ} (a b : Fin q) (hab : a≠b) :
    (Finset.univ.filter (fun k:Fin q→Fin N=>k a=k b)).card≤N^(q-1) := by
  let f : {k:Fin q→Fin N // k a=k b}→({j:Fin q // j≠b}→Fin N) := fun k j=>k.1 j.1
  have hf : Function.Injective f := by
    intro k l h
    apply Subtype.ext
    funext j
    by_cases hj:j=b
    · subst j
      have ha := congrFun h ⟨a,hab⟩
      exact k.2.symm.trans (ha.trans l.2)
    · exact congrFun h ⟨j,hj⟩
  have h := Fintype.card_le_of_injective f hf
  have hc : Fintype.card {j:Fin q // j≠b}=q-1 := by
    simpa only [Fintype.card_fin,Fintype.card_subtype_eq] using
        Fintype.card_subtype_compl (fun j:Fin q=>j=b)
  rw [Fintype.card_fun,hc] at h
  simpa only [Fintype.card_subtype,Finset.card_filter,Fintype.card_fin] using h

theorem repeated_tuple_card (q N : ℕ) :
    (Finset.univ.filter (fun k:Fin q→Fin N=>¬Function.Injective k)).card≤q^2*N^(q-1) := by
  let C (ab:Fin q×Fin q) : Finset (Fin q→Fin N) :=
    if ab.1=ab.2 then ∅ else Finset.univ.filter (fun k=>k ab.1=k ab.2)
  have hcover : Finset.univ.filter (fun k:Fin q→Fin N=>¬Function.Injective k)⊆Finset.univ.biUnion C := by
    intro k hk
    have hni := (Finset.mem_filter.mp hk).2
    obtain ⟨a,b,heq,hab⟩ := Function.not_injective_iff.mp hni
    exact Finset.mem_biUnion.mpr ⟨(a,b),Finset.mem_univ _,by simp [C,hab,heq]⟩
  have hb (ab:Fin q×Fin q) : (C ab).card≤N^(q-1) := by
    by_cases h:ab.1=ab.2
    · simp [C,h]
    · simpa only [C,if_neg h] using collision_card ab.1 ab.2 h
  calc
    _ ≤ (Finset.univ.biUnion C).card := Finset.card_le_card hcover
    _ ≤ ∑ ab∈(Finset.univ:Finset (Fin q×Fin q)),(C ab).card := Finset.card_biUnion_le
    _ ≤ ∑ _ab∈(Finset.univ:Finset (Fin q×Fin q)),N^(q-1) := Finset.sum_le_sum (fun ab _=>hb ab)
    _ = _ := by simp [pow_two]
end Qatlib.Papers.OverlapGapGoh26.GaussianBounds.Remainder
