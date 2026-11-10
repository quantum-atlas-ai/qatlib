/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors, Qatlib Contributors
-/

import Qatlib.Foundations.CbmdAnalysis.Residue.TauCeti.CBMDCompat

import Mathlib.Topology.Bornology.Basic
import Mathlib.Topology.Connected.Basic
import Mathlib.Topology.Connected.LocallyConnected
import Mathlib.Topology.Compactness.LocallyCompact
import Mathlib.Topology.Separation.Hausdorff
import Qatlib.Foundations.CbmdAnalysis.Residue.TauCeti.Topology.ConnectedComponents
import Qatlib.Foundations.CbmdAnalysis.Residue.TauCeti.Topology.Frontier
set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

namespace Qatlib.Foundations.CbmdAnalysis.Residue

section

namespace TauCeti

open Bornology _root_.Set

variable {E : Type*} [TopologicalSpace E] [Bornology E] {K L S : Set E} {x : E}

def filledHull (K : Set E) : Set E := {x | IsBounded (connectedComponentIn Kᶜ x)}

@[simp]
theorem mem_filledHull_iff
    : x ∈ filledHull K ↔ IsBounded (connectedComponentIn Kᶜ x) := Iff.rfl

theorem mem_filledHull_iff_of_mem_connectedComponentIn {y : E}
    (hy : y ∈ connectedComponentIn Kᶜ x) : y ∈ filledHull K ↔ x ∈ filledHull K := by
  rw [mem_filledHull_iff, mem_filledHull_iff, connectedComponentIn_eq hy]

theorem subset_filledHull : K ⊆ filledHull K := by
  intro x hx
  have hxc : x ∉ Kᶜ := by simpa using hx
  simp [mem_filledHull_iff, connectedComponentIn_eq_empty hxc]

@[gcongr]
theorem filledHull_mono (h : K ⊆ L) : filledHull K ⊆ filledHull L := fun _ hx =>
  mem_filledHull_iff.mpr <|
    (mem_filledHull_iff.mp hx).subset (connectedComponentIn_mono _ (compl_subset_compl.mpr h))

theorem _root_.Qatlib.Foundations.CbmdAnalysis.Residue.IsClosed.isOpen_filledHull_sdiff
    [LocallyConnectedSpace E] (hK : IsClosed K) :
    IsOpen (filledHull K \ K) := by
  rw [isOpen_iff_mem_nhds]
  intro x hx
  refine Filter.mem_of_superset
    ((hK.isOpen_compl.connectedComponentIn).mem_nhds (mem_connectedComponentIn hx.2)) ?_
  intro y hy
  exact ⟨(mem_filledHull_iff_of_mem_connectedComponentIn hy).mpr hx.1,
    connectedComponentIn_subset Kᶜ x hy⟩

theorem _root_.Qatlib.Foundations.CbmdAnalysis.Residue.IsClosed.isClosed_filledHull [LocallyConnectedSpace E] (hK : IsClosed K) :
    IsClosed (filledHull K) := by
  rw [← isOpen_compl_iff, isOpen_iff_mem_nhds]
  intro x hx
  have hxK : x ∈ Kᶜ := fun h => hx (subset_filledHull h)
  refine Filter.mem_of_superset
    ((hK.isOpen_compl.connectedComponentIn).mem_nhds (mem_connectedComponentIn hxK)) ?_
  exact fun y hy hyH => hx ((mem_filledHull_iff_of_mem_connectedComponentIn hy).mp hyH)

theorem _root_.Qatlib.Foundations.CbmdAnalysis.Residue.IsClosed.frontier_filledHull_sdiff_subset
    [LocallyConnectedSpace E] (hK : IsClosed K) :
    frontier (filledHull K \ K) ⊆ K := by
  intro x hx
  have hxH : x ∈ filledHull K :=
    (closure_minimal diff_subset (IsClosed.isClosed_filledHull hK)) hx.1
  by_contra hxK
  exact hx.2 ((IsClosed.isOpen_filledHull_sdiff hK).interior_eq.symm ▸ ⟨hxH, hxK⟩)

theorem filledHull_eq_self
    (h : IsPreconnected Kᶜ) (hu : ¬ IsBounded Kᶜ) : filledHull K = K := by
  refine Subset.antisymm (fun x hx => ?_) subset_filledHull
  by_contra hxK
  exact hu ((mem_filledHull_iff.mp hx).subset
    (h.subset_connectedComponentIn (mem_compl hxK) subset_rfl))

theorem filledHull_eq_self_of_isPreconnected_frontier [LocallyConnectedSpace E]
    [PreconnectedSpace E] (hK : IsOpen K) (hf : IsPreconnected (frontier K))
    (hu : ¬ IsBounded Kᶜ) : filledHull K = K :=
  filledHull_eq_self (isPreconnected_compl_of_isPreconnected_frontier hK hf) hu

theorem _root_.Qatlib.Foundations.CbmdAnalysis.Residue.IsPreconnected.subset_filledHull (hS : IsPreconnected S) (hSK : Disjoint S K)
    (hne : (S ∩ filledHull K).Nonempty) : S ⊆ filledHull K := by
  obtain ⟨x, hxS, hxH⟩ := hne
  have hScompl : S ⊆ Kᶜ := fun y hy => Set.disjoint_left.mp hSK hy
  have hScomp : S ⊆ connectedComponentIn Kᶜ x := hS.subset_connectedComponentIn hxS hScompl
  exact fun y hy => (mem_filledHull_iff_of_mem_connectedComponentIn (hScomp hy)).mpr hxH

theorem subset_filledHull_of_frontier_subset (hSb : IsBounded S) (hfr : frontier S ⊆ K) :
    S ⊆ filledHull K := by
  intro x hx
  by_cases hxK : x ∈ K
  · exact subset_filledHull hxK
  have hxKc : x ∈ Kᶜ := hxK
  have hxi : x ∈ interior S := (mem_interior_iff_notMem_frontier hx).2 fun h => hxK (hfr h)
  have hcomp : connectedComponentIn Kᶜ x ⊆ interior S := by
    by_contra h
    obtain ⟨y, hy, hyi⟩ := not_subset.mp h
    obtain ⟨z, hz, hzf⟩ := IsPreconnected.inter_frontier_nonempty isPreconnected_connectedComponentIn
      ⟨x, mem_connectedComponentIn hxKc, hxi⟩ ⟨y, hy, hyi⟩
    exact connectedComponentIn_subset _ _ hz (hfr (frontier_interior_subset hzf))
  exact mem_filledHull_iff.mpr (hSb.subset (hcomp.trans interior_subset))

end TauCeti

section Compact

open _root_.Set

variable {X : Type*} [TopologicalSpace X] [T2Space X] [WeaklyLocallyCompactSpace X]

theorem IsCompact.isCompact_setOf_isCompact_closure_connectedComponentIn_compl
    [LocallyConnectedSpace X] {K : Set X} (hK : IsCompact K)
    (hX : ∀ x : X, ¬IsCompact (connectedComponent x)) :
    IsCompact {x | IsCompact (closure (connectedComponentIn Kᶜ x))} := by
  set B := {x | IsCompact (closure (connectedComponentIn Kᶜ x))}
  have hB : IsClosed B := by
    let : Bornology X := .relativelyCompact X
    have hBK : B = TauCeti.filledHull K := by
      ext x
      simp [B, Bornology.relativelyCompact.isBounded_iff]
    exact hBK ▸ IsClosed.isClosed_filledHull hK.isClosed
  obtain ⟨L, hL, hKL⟩ := exists_compact_superset hK

  have hfrK : frontier L ⊆ Kᶜ := fun y hy hyK ↦ hy.2 (hKL hyK)
  obtain ⟨F, hFL, hcover⟩ := (hL.of_isClosed_subset isClosed_frontier
    hL.isClosed.frontier_subset).elim_nhds_subcover (connectedComponentIn Kᶜ)
      fun y hy ↦ hK.isClosed.isOpen_compl.connectedComponentIn.mem_nhds
        (mem_connectedComponentIn (hfrK hy))
  classical
  refine (hL.union ((F.filter (· ∈ B)).isCompact_biUnion fun z hz ↦
    (Finset.mem_filter.1 hz).2)).of_isClosed_subset hB fun y hy ↦ ?_
  by_cases hyL : y ∈ L
  · exact Or.inl hyL
  right
  set C := connectedComponentIn Kᶜ y
  have hyC : y ∈ C := mem_connectedComponentIn fun hyK ↦ hyL (interior_subset (hKL hyK))
  by_cases hCfr : (C ∩ frontier L).Nonempty
  · obtain ⟨w, hwC, hwL⟩ := hCfr
    obtain ⟨z, hzF, hwz⟩ := mem_iUnion₂.1 (hcover hwL)
    have hCz : connectedComponentIn Kᶜ z = C :=
      (connectedComponentIn_eq hwz).trans (connectedComponentIn_eq hwC).symm
    refine mem_iUnion₂.2 ⟨z, Finset.mem_filter.2 ⟨hzF, ?_⟩, ?_⟩
    · simpa [B, hCz] using hy
    · exact subset_closure (hCz ▸ hyC)
  · exfalso
    have hCL : C ⊆ Lᶜ := isPreconnected_connectedComponentIn.subset_of_closure_inter_subset
      hL.isClosed.isOpen_compl ⟨y, hyC, hyL⟩ fun w ⟨hw, hwC⟩ hwL ↦
        hCfr ⟨w, hwC, subset_closure hwL, by rwa [← mem_compl_iff, ← closure_compl]⟩
    have hfrC : frontier C = ∅ := by
      refine eq_empty_of_forall_notMem fun w hw ↦ ?_
      have hwK : w ∈ K := by
        simpa using TauCeti.frontier_connectedComponentIn_subset_compl hK.isClosed.isOpen_compl
          y hw
      have hw' : w ∈ closure Lᶜ := closure_mono hCL (frontier_subset_closure hw)
      rw [closure_compl] at hw'
      exact hw' (hKL hwK)
    have hcomp : connectedComponent y ⊆ closure C :=
      ((isClopen_iff_frontier_eq_empty.2 hfrC).connectedComponent_subset hyC).trans subset_closure
    exact hX y (hy.of_isClosed_subset isClosed_connectedComponent hcomp)

namespace TauCeti

theorem exists_mem_not_isCompact_closure_connectedComponentIn_compl [LocallyConnectedSpace X]
    (hX : ∀ x : X, ¬IsCompact (connectedComponent x)) {S L : Set X}
    (hS : ¬IsCompact (closure S)) (hL : IsCompact L) :
    ∃ y ∈ S, ¬IsCompact (closure (connectedComponentIn Lᶜ y)) := by
  by_contra! h
  have hB := IsCompact.isCompact_setOf_isCompact_closure_connectedComponentIn_compl hL hX
  exact hS (hB.of_isClosed_subset isClosed_closure (closure_minimal h hB.isClosed))

end TauCeti

end Compact

end
end Qatlib.Foundations.CbmdAnalysis.Residue
