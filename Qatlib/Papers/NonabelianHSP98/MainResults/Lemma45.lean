/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.NonabelianHSP98.MainResults.VectorModel.Counting
import Qatlib.Papers.NonabelianHSP98.MainResults.VectorModel.PerpGroup
set_option warningAsError false

set_option autoImplicit false

namespace Qatlib.Papers.NonabelianHSP98.MainResults.Lemma45

open Qatlib.Papers.NonabelianHSP98.MainResults.WreathGroup
open Qatlib.Papers.NonabelianHSP98.MainResults.WreathGroup.Wreath
open Qatlib.Papers.NonabelianHSP98.MainResults.Pairing
open Qatlib.Papers.NonabelianHSP98.MainResults.VectorModel
open Qatlib.Papers.NonabelianHSP98.MainResults.VectorModel.Orthogonal
open Qatlib.Papers.NonabelianHSP98.MainResults.VectorModel.PerpGroup
open Qatlib.Papers.NonabelianHSP98.MainResults.VectorModel.Counting
open Finset

attribute [local instance] Classical.propDecidable

variable {n : ℕ}

def lastVec (n : ℕ) : Vec n := ((0 : Fin n → ZMod 2), (0 : Fin n → ZMod 2), (1 : ZMod 2))

@[simp] lemma dot_lastVec (z : Vec n) : dot (lastVec n) z = z.2.2 := by
  simp [lastVec, dot]

theorem mem_orthW_iff {U : Subgroup (Wreath n)} {g : Wreath n} :
    phi g ∈ blin.orthogonal (phiSub U) ↔ g ∈ perpSub U := by
  change phi g ∈ (blin.orthogonal (phiSub U) : Set (Vec n)) ↔ g ∈ perpSub U
  rw [show (blin.orthogonal (phiSub U) : Set (Vec n)) = orthV (phiSet U) from
    (orthV_eq_orthogonal (phiSub U)).symm]
  exact phi_mem_orthV

theorem lemma_4_5 (U : Subgroup (Wreath n)) (t₀ : Wreath n)
    (ht₀ : t₀ ∈ perpSub U) (ht₀a : t₀.a = 1) :
    2 * (Finset.univ.filter (fun g : Wreath n => g ∈ perpSub U ∧ g.a = 0)).card
      = (Finset.univ.filter (fun g : Wreath n => g ∈ perpSub U)).card := by
  let W : Submodule (ZMod 2) (Vec n) := blin.orthogonal (phiSub U)
  let A : Finset (Wreath n) := univ.filter (fun g : Wreath n => g ∈ perpSub U ∧ g.a = 0)
  let B : Finset (Wreath n) := univ.filter (fun g : Wreath n => g ∈ perpSub U ∧ g.a = 1)
  let C : Finset (Wreath n) := univ.filter (fun g : Wreath n => g ∈ perpSub U)
  let A' : Finset W := univ.filter (fun z : W => (z : Vec n).2.2 = 0)
  let B' : Finset W := univ.filter (fun z : W => (z : Vec n).2.2 = 1)
  have hA : A.card = A'.card := by
    apply Finset.card_bij (fun (g : Wreath n) (hg : g ∈ A) =>
      (⟨phi g, mem_orthW_iff.mpr (by
        simp only [A, mem_filter, mem_univ, true_and] at hg
        exact hg.1)⟩ : W))
    · intro g hg
      simp only [A, mem_filter, mem_univ, true_and] at hg
      simp only [A', mem_filter, mem_univ, true_and]
      rw [phi_a]; exact hg.2
    · intro a _ b _ h
      apply phi_inj
      have := congrArg (fun z : W => (z : Vec n)) h
      simpa using this
    · intro z hz
      simp only [A', mem_filter, mem_univ, true_and] at hz
      refine ⟨phiInv (z : Vec n), ?_, ?_⟩
      · simp only [A, mem_filter, mem_univ, true_and]
        constructor
        · exact mem_orthW_iff.mp (by rw [phiInv_phi]; exact z.2)
        · rw [← phi_a, phiInv_phi]; exact hz
      · apply Subtype.ext
        simp only [Subtype.coe_mk]
        exact phiInv_phi (z : Vec n)
  have hB : B.card = B'.card := by
    apply Finset.card_bij (fun (g : Wreath n) (hg : g ∈ B) =>
      (⟨phi g, mem_orthW_iff.mpr (by
        simp only [B, mem_filter, mem_univ, true_and] at hg
        exact hg.1)⟩ : W))
    · intro g hg
      simp only [B, mem_filter, mem_univ, true_and] at hg
      simp only [B', mem_filter, mem_univ, true_and]
      rw [phi_a]; exact hg.2
    · intro a _ b _ h
      apply phi_inj
      have := congrArg (fun z : W => (z : Vec n)) h
      simpa using this
    · intro z hz
      simp only [B', mem_filter, mem_univ, true_and] at hz
      refine ⟨phiInv (z : Vec n), ?_, ?_⟩
      · simp only [B, mem_filter, mem_univ, true_and]
        constructor
        · exact mem_orthW_iff.mp (by rw [phiInv_phi]; exact z.2)
        · rw [← phi_a, phiInv_phi]; exact hz
      · apply Subtype.ext
        simp only [Subtype.coe_mk]
        exact phiInv_phi (z : Vec n)
  have hC : C.card = Fintype.card W := by
    rw [← Finset.card_univ]
    apply Finset.card_bij (fun (g : Wreath n) (hg : g ∈ C) =>
      (⟨phi g, mem_orthW_iff.mpr (by
        simp only [C, mem_filter, mem_univ, true_and] at hg
        exact hg)⟩ : W))
    · intro g _
      simp
    · intro a _ b _ h
      apply phi_inj
      have := congrArg (fun z : W => (z : Vec n)) h
      simpa using this
    · intro z _
      refine ⟨phiInv (z : Vec n), ?_, ?_⟩
      · simp only [C, mem_filter, mem_univ, true_and]
        exact mem_orthW_iff.mp (by rw [phiInv_phi]; exact z.2)
      · apply Subtype.ext
        simp only [Subtype.coe_mk]
        exact phiInv_phi (z : Vec n)

  have hz₀ : phi t₀ ∈ W := mem_orthW_iff.mpr ht₀
  have hlast₀ : (phi t₀).2.2 = 1 := by rw [phi_a]; exact ht₀a
  have hhalfW : A'.card = B'.card := by
    have hcount := card_dot_zero_eq_one W (lastVec n) (phi t₀) hz₀ (by
      rw [dot_lastVec]; exact hlast₀)
    simpa only [A', B', dot_lastVec] using hcount

  have hdisj : Disjoint A' B' := by
    rw [Finset.disjoint_left]
    intro z hzA hzB
    simp only [A', B', mem_filter, mem_univ, true_and] at hzA hzB
    rw [hzA] at hzB
    exact zero_ne_one hzB
  have hunion : A' ∪ B' = univ := by
    ext z
    simp only [A', B', mem_union, mem_filter, mem_univ, true_and, iff_true]
    rcases zmod2_eq_zero_or_one ((z : Vec n).2.2) with h | h
    · exact Or.inl h
    · exact Or.inr h
  have hcardW : A'.card + B'.card = Fintype.card W := by
    have hc := Finset.card_union_of_disjoint hdisj
    rw [hunion, Finset.card_univ] at hc
    omega

  have hAB : A.card = B.card := by rw [hA, hB, hhalfW]
  have hABC : A.card + B.card = C.card := by
    have hdisj' : Disjoint A B := by
      rw [Finset.disjoint_left]
      intro g hgA hgB
      simp only [A, B, mem_filter, mem_univ, true_and] at hgA hgB
      rw [hgA.2] at hgB
      exact zero_ne_one hgB.2
    have hunion' : A ∪ B = C := by
      ext g
      simp only [A, B, C, mem_union, mem_filter, mem_univ, true_and]
      constructor
      · rintro (h | h)
        · exact h.1
        · exact h.1
      · intro hg
        rcases zmod2_eq_zero_or_one g.a with h | h
        · exact Or.inl ⟨hg, h⟩
        · exact Or.inr ⟨hg, h⟩
    have hc := Finset.card_union_of_disjoint hdisj'
    rw [hunion'] at hc
    omega
  have hCW : C.card = Fintype.card W := hC
  have h2 : A.card + A.card = Fintype.card W := by
    rw [hAB] at hABC
    rw [hAB, hABC, hCW]
  rw [← hABC, hAB]
  omega

end Qatlib.Papers.NonabelianHSP98.MainResults.Lemma45
