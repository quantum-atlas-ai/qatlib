/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.NonabelianHSP98.MainResults.VectorModel.PerpGroup
set_option warningAsError false

set_option autoImplicit false

namespace Qatlib.Papers.NonabelianHSP98.MainResults.Corollary47

open Qatlib.Papers.NonabelianHSP98.MainResults.WreathGroup
open Qatlib.Papers.NonabelianHSP98.MainResults.WreathGroup.Wreath
open Qatlib.Papers.NonabelianHSP98.MainResults.Pairing
open Qatlib.Papers.NonabelianHSP98.MainResults.VectorModel.Orthogonal
open Qatlib.Papers.NonabelianHSP98.MainResults.VectorModel.PerpGroup

variable {n : ℕ}

theorem corollary_4_7_a (U : Subgroup (Wreath n)) :
    perpSub (conjSub U) = swapFun '' perpSub U := by
  ext g
  constructor
  · intro hg
    refine ⟨swapFun g, ?_, swapFun_swapFun g⟩
    intro v hv
    have h1 : mu (swapFun g) v = mu g (swapFun v) := by
      simpa using (mu_swapFun_swapFun (swapFun g) v).symm
    rw [h1]
    exact hg (swapFun v) (mem_conjSub.mpr ⟨v, hv, rfl⟩)
  · rintro ⟨h, hh, rfl⟩
    intro u hu
    obtain ⟨v, hv, rfl⟩ := mem_conjSub.mp hu
    rw [mu_swapFun_swapFun]
    exact hh v hv

theorem conjSub_inf_self (U : Subgroup (Wreath n)) :
    conjSub (U ⊓ conjSub U) = U ⊓ conjSub U := by
  ext g
  constructor
  · rintro ⟨u, ⟨huU, huC⟩, rfl⟩
    obtain ⟨v, hv, hveq⟩ := mem_conjSub.mp huC
    refine ⟨?_, ?_⟩
    · rw [← hveq, swapFun_swapFun]; exact hv
    · exact mem_conjSub.mpr ⟨u, huU, rfl⟩
  · rintro ⟨hgU, hgC⟩
    obtain ⟨v, hv, hveq⟩ := mem_conjSub.mp hgC
    refine mem_conjSub.mpr ⟨swapFun g, ⟨?_, ?_⟩, swapFun_swapFun g⟩
    · rw [← hveq, swapFun_swapFun]; exact hv
    · exact mem_conjSub.mpr ⟨g, hgU, rfl⟩

theorem corollary_4_7_b (U : Subgroup (Wreath n)) :
    perpSub (U ⊓ conjSub U)
      = (Subgroup.closure (perpSub U ∪ perpSub (conjSub U)) : Set (Wreath n)) := by
  have hbal : ∀ g ∈ U ⊓ conjSub U, swapFun g ∈ U ⊓ conjSub U :=
    balanced_of_conjSub_eq (U ⊓ conjSub U) (conjSub_inf_self U)
  apply le_antisymm
  · have hKperp_U :
        perp (Subgroup.closure (perpSub U ∪ perpSub (conjSub U)) : Set (Wreath n))
          ⊆ (U : Set (Wreath n)) := by
      have hgen : perpSub U ⊆
          (Subgroup.closure (perpSub U ∪ perpSub (conjSub U)) : Set (Wreath n)) :=
        fun x hx => Subgroup.subset_closure (Or.inl hx)
      have h2 := perp_mono hgen
      rwa [perpSub_perpSub U] at h2
    have hKperp_V :
        perp (Subgroup.closure (perpSub U ∪ perpSub (conjSub U)) : Set (Wreath n))
          ⊆ (conjSub U : Set (Wreath n)) := by
      have hgen : perpSub (conjSub U) ⊆
          (Subgroup.closure (perpSub U ∪ perpSub (conjSub U)) : Set (Wreath n)) :=
        fun x hx => Subgroup.subset_closure (Or.inr hx)
      have h2 := perp_mono hgen
      rwa [perpSub_perpSub (conjSub U)] at h2
    have hKperp_W :
        perp (Subgroup.closure (perpSub U ∪ perpSub (conjSub U)) : Set (Wreath n))
          ⊆ ((U ⊓ conjSub U : Subgroup (Wreath n)) : Set (Wreath n)) := by
      intro x hx
      exact ⟨hKperp_U hx, hKperp_V hx⟩
    have h2 : perp ((U ⊓ conjSub U : Subgroup (Wreath n)) : Set (Wreath n))
        ⊆ perp (perpSub (Subgroup.closure (perpSub U ∪ perpSub (conjSub U)))) := by
      simpa only [perpSub] using perp_mono hKperp_W
    have h3 : perp ((U ⊓ conjSub U : Subgroup (Wreath n)) : Set (Wreath n))
        ⊆ (Subgroup.closure (perpSub U ∪ perpSub (conjSub U)) : Set (Wreath n)) := by
      rwa [perpSub_perpSub (Subgroup.closure (perpSub U ∪ perpSub (conjSub U)))] at h2
    exact h3
  · have hcl : Subgroup.closure (perpSub U ∪ perpSub (conjSub U))
        ≤ perpGroup (U ⊓ conjSub U) hbal := by
      rw [Subgroup.closure_le]
      intro x hx
      rcases hx with hx | hx
      · exact perp_mono (fun y hy => hy.1) hx
      · exact perp_mono (fun y hy => hy.2) hx
    intro x hx
    exact hcl hx

theorem corollary_4_7_c (U V : Subgroup (Wreath n))
    (hU : conjSub U = U) (hV : conjSub V = V)
    (h : perpSub U = perpSub V) : U = V := by
  have h1 : (U : Set (Wreath n)) = (V : Set (Wreath n)) := by
    rw [← perpSub_perpSub U, ← perpSub_perpSub V, h]
  ext x
  exact Set.ext_iff.mp h1 x

theorem corollary_4_7_d (U V : Subgroup (Wreath n))
    (hU : conjSub U = U) (hV : conjSub V = V) :
    U ≤ V ↔ perpSub V ⊆ perpSub U := by
  constructor
  · intro h x hx
    exact perp_mono (fun y hy => h hy) hx
  · intro h x hx
    have h2 : perp (perpSub U) ⊆ perp (perpSub V) := perp_mono h
    rw [perpSub_perpSub U, perpSub_perpSub V] at h2
    exact h2 hx

end Qatlib.Papers.NonabelianHSP98.MainResults.Corollary47
