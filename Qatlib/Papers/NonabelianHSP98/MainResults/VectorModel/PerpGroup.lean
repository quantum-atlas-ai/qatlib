/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.NonabelianHSP98.MainResults.VectorModel.Orthogonal
set_option warningAsError false

set_option autoImplicit false

namespace Qatlib.Papers.NonabelianHSP98.MainResults.VectorModel.PerpGroup

open Qatlib.Papers.NonabelianHSP98.MainResults.WreathGroup
open Qatlib.Papers.NonabelianHSP98.MainResults.WreathGroup.Wreath
open Qatlib.Papers.NonabelianHSP98.MainResults.Pairing
open Qatlib.Papers.NonabelianHSP98.MainResults.VectorModel
open Qatlib.Papers.NonabelianHSP98.MainResults.VectorModel.Orthogonal
open Finset

variable {n : ℕ}

theorem phi_mem_orthV {U : Subgroup (Wreath n)} {g : Wreath n} :
    phi g ∈ orthV (phiSet U) ↔ g ∈ perpSub U := by
  rw [mem_perpSub]
  constructor
  · intro H u hu
    have h := H (phi u) ⟨u, hu, rfl⟩
    rwa [← phi_mu] at h
  · intro H s hs
    obtain ⟨u, hu, rfl⟩ := hs
    rw [← phi_mu]
    exact H u hu

theorem perpSub_eq_preimage (U : Subgroup (Wreath n)) :
    perpSub U = phi ⁻¹' (orthV (phiSet U)) := by
  ext g
  rw [Set.mem_preimage]
  exact phi_mem_orthV.symm

theorem one_mem_perpSub (U : Subgroup (Wreath n)) : (1 : Wreath n) ∈ perpSub U := by
  rw [mem_perpSub]
  intro u _
  rw [phi_mu, phi_one]
  simp [dot]

theorem mul_mem_perpSub (U : Subgroup (Wreath n))
    (hbal : ∀ g ∈ U, swapFun g ∈ U) {g h : Wreath n}
    (hg : g ∈ perpSub U) (hh : h ∈ perpSub U) : g * h ∈ perpSub U := by
  rw [mem_perpSub] at hg hh ⊢
  have hgu : phi g ∈ orthV (phiSet U) := phi_mem_orthV.mpr hg
  have hhu : phi h ∈ orthV (phiSet U) := phi_mem_orthV.mpr hh
  have hS : ∀ s ∈ phiSet U, swapV s ∈ phiSet U := (phiSub_balanced_iff U).mp hbal
  have horth := orthV_balanced hS
  have hstep : phi (g * h) ∈ orthV (phiSet U) := by
    rw [phi_mul]
    split_ifs with h0
    · exact orthV_add hgu hhu
    · exact orthV_add hgu (horth (phi h) hhu)
  intro u hu
  have h := hstep (phi u) ⟨u, hu, rfl⟩
  rwa [← phi_mu] at h

theorem inv_mem_perpSub (U : Subgroup (Wreath n))
    (hbal : ∀ g ∈ U, swapFun g ∈ U) {g : Wreath n}
    (hg : g ∈ perpSub U) : g⁻¹ ∈ perpSub U := by
  rw [mem_perpSub] at hg ⊢
  have hgu : phi g ∈ orthV (phiSet U) := phi_mem_orthV.mpr hg
  have hS : ∀ s ∈ phiSet U, swapV s ∈ phiSet U := (phiSub_balanced_iff U).mp hbal
  have horth := orthV_balanced hS
  have hstep : phi (g⁻¹) ∈ orthV (phiSet U) := by
    rcases zmod2_eq_zero_or_one g.a with h0 | h1
    · rw [inv_eq_base g h0]; exact hgu
    · rw [inv_eq g h1, phi_swapFun]; exact horth (phi g) hgu
  intro u hu
  have h := hstep (phi u) ⟨u, hu, rfl⟩
  rwa [← phi_mu] at h

def perpGroup (U : Subgroup (Wreath n))
    (hbal : ∀ g ∈ U, swapFun g ∈ U) : Subgroup (Wreath n) where
  carrier := perpSub U
  mul_mem' := mul_mem_perpSub U hbal
  one_mem' := one_mem_perpSub U
  inv_mem' := inv_mem_perpSub U hbal

lemma coe_perpGroup (U : Subgroup (Wreath n)) (hbal : ∀ g ∈ U, swapFun g ∈ U) :
    (perpGroup U hbal : Set (Wreath n)) = perpSub U := rfl

theorem perp_balanced {S : Set (Wreath n)} (hS : ∀ s ∈ S, swapFun s ∈ S) :
    ∀ g ∈ perp S, swapFun g ∈ perp S := by
  intro g hg s hs
  have h := (mu_swapFun_swapFun (swapFun g) s).symm
  rw [h]
  exact hg (swapFun s) (hS s hs)

theorem conjSub_eq_of_balanced (U : Subgroup (Wreath n))
    (hbal : ∀ g ∈ U, swapFun g ∈ U) : conjSub U = U := by
  ext g
  constructor
  · intro hg
    obtain ⟨u, hu, rfl⟩ := mem_conjSub.mp hg
    exact hbal u hu
  · intro hg
    exact mem_conjSub.mpr ⟨swapFun g, hbal g hg, swapFun_swapFun g⟩

theorem balanced_of_conjSub_eq (U : Subgroup (Wreath n)) (h : conjSub U = U) :
    ∀ g ∈ U, swapFun g ∈ U := by
  intro g hg
  have hg' : g ∈ conjSub U := by rw [h]; exact hg
  obtain ⟨u, hu, heq⟩ := mem_conjSub.mp hg'
  rw [← heq, swapFun_swapFun]
  exact hu

end Qatlib.Papers.NonabelianHSP98.MainResults.VectorModel.PerpGroup
