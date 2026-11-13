/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors, Qatlib Contributors

Adapted from https://github.com/TauCetiProject/TauCeti@3780371c
-/

import Qatlib.Foundations.CbmdAnalysis.Residue.TauCeti.CBMDCompat

import Mathlib.Topology.Bornology.Basic
import Mathlib.Topology.Connected.Basic
import Mathlib.Topology.Connected.LocallyConnected
import Mathlib.Topology.Compactness.LocallyCompact
import Mathlib.Topology.Separation.Hausdorff
import Qatlib.Foundations.CbmdAnalysis.Residue.TauCeti.Topology.ConnectedComponents
import Qatlib.Foundations.CbmdAnalysis.Residue.TauCeti.Topology.Frontier

/-!
# Filled hulls and bounded complementary components

Defines `filledHull` by boundedness of connected components of the complement and proves
monotonicity, closedness, and frontier properties under the relevant topological hypotheses.
Additional results identify sets equal to their filled hull and provide compactness criteria
using complementary components.

The construction supports winding-number and contour-domain arguments associated with
[WangEtAl2026].

## Main statements

* `filledHull`: The filled hull of `K`, consisting of points whose connected component in the
  complement of `K` is bounded.
* `filledHull_eq_self`: A set with preconnected unbounded complement equals its filled hull.
* `subset_filledHull_of_frontier_subset`: A bounded set whose frontier lies in `K` is contained
  in the filled hull of `K`.

## References

* [Wang et al., 2026][WangEtAl2026]
-/

set_option backward.isDefEq.respectTransparency false

namespace Qatlib.Foundations.CbmdAnalysis.Residue

section

namespace TauCeti

open Bornology _root_.Set

variable {E : Type*} [TopologicalSpace E] [Bornology E] {K L S : Set E} {x : E}

/-- The filled hull of `K`, consisting of points whose connected component in the complement of
`K` is bounded. -/
def filledHull (K : Set E) : Set E := {x | IsBounded (connectedComponentIn Kᶜ x)}

/-- A point belongs to the filled hull exactly when its complementary connected component is
bounded. -/
@[simp]
theorem mem_filledHull_iff
    : x ∈ filledHull K ↔ IsBounded (connectedComponentIn Kᶜ x) := Iff.rfl

/-- Membership in the filled hull is constant along each connected component of the complement. -/
theorem mem_filledHull_iff_of_mem_connectedComponentIn {y : E}
    (hy : y ∈ connectedComponentIn Kᶜ x) : y ∈ filledHull K ↔ x ∈ filledHull K := by
  rw [mem_filledHull_iff, mem_filledHull_iff, connectedComponentIn_eq hy]

/-- Every set is contained in its filled hull. -/
theorem subset_filledHull : K ⊆ filledHull K := by
  intro x hx
  have hxc : x ∉ Kᶜ := by simpa using hx
  simp [mem_filledHull_iff, connectedComponentIn_eq_empty hxc]

/-- The filled hull is monotone under set inclusion. -/
@[gcongr]
theorem filledHull_mono (h : K ⊆ L) : filledHull K ⊆ filledHull L := fun _ hx =>
  mem_filledHull_iff.mpr <|
    (mem_filledHull_iff.mp hx).subset (connectedComponentIn_mono _ (compl_subset_compl.mpr h))

/-- In a locally connected space, the difference between the filled hull of a closed set and
that set is open. -/
theorem _root_.IsClosed.isOpen_filledHull_sdiff
    [LocallyConnectedSpace E] (hK : IsClosed K) :
    IsOpen (filledHull K \ K) := by
  rw [isOpen_iff_mem_nhds]
  intro x hx
  refine Filter.mem_of_superset
    ((hK.isOpen_compl.connectedComponentIn).mem_nhds (mem_connectedComponentIn hx.2)) ?_
  intro y hy
  exact ⟨(mem_filledHull_iff_of_mem_connectedComponentIn hy).mpr hx.1,
    connectedComponentIn_subset Kᶜ x hy⟩

/-- In a locally connected space, the filled hull of a closed set is closed. -/
theorem _root_.IsClosed.isClosed_filledHull [LocallyConnectedSpace E] (hK : IsClosed K) :
    IsClosed (filledHull K) := by
  rw [← isOpen_compl_iff, isOpen_iff_mem_nhds]
  intro x hx
  have hxK : x ∈ Kᶜ := fun h => hx (subset_filledHull h)
  refine Filter.mem_of_superset
    ((hK.isOpen_compl.connectedComponentIn).mem_nhds (mem_connectedComponentIn hxK)) ?_
  exact fun y hy hyH => hx ((mem_filledHull_iff_of_mem_connectedComponentIn hy).mp hyH)

/-- In a locally connected space, the frontier of the added portion of the filled hull of a
closed set lies in the original set. -/
theorem _root_.IsClosed.frontier_filledHull_sdiff_subset
    [LocallyConnectedSpace E] (hK : IsClosed K) :
    frontier (filledHull K \ K) ⊆ K := by
  intro x hx
  have hxH : x ∈ filledHull K :=
    (closure_minimal diff_subset (IsClosed.isClosed_filledHull hK)) hx.1
  by_contra hxK
  exact hx.2 ((IsClosed.isOpen_filledHull_sdiff hK).interior_eq.symm ▸ ⟨hxH, hxK⟩)

/-- A set with preconnected unbounded complement equals its filled hull. -/
theorem filledHull_eq_self
    (h : IsPreconnected Kᶜ) (hu : ¬ IsBounded Kᶜ) : filledHull K = K := by
  refine Subset.antisymm (fun x hx => ?_) subset_filledHull
  by_contra hxK
  exact hu ((mem_filledHull_iff.mp hx).subset
    (h.subset_connectedComponentIn (mem_compl hxK) subset_rfl))

/-- In a locally connected preconnected space, an open set with preconnected frontier and
unbounded complement equals its filled hull. -/
theorem filledHull_eq_self_of_isPreconnected_frontier [LocallyConnectedSpace E]
    [PreconnectedSpace E] (hK : IsOpen K) (hf : IsPreconnected (frontier K))
    (hu : ¬ IsBounded Kᶜ) : filledHull K = K :=
  filledHull_eq_self (isPreconnected_compl_of_isPreconnected_frontier hK hf) hu

/-- A preconnected set disjoint from `K` that meets the filled hull of `K` lies entirely in that
filled hull. -/
theorem _root_.IsPreconnected.subset_filledHull (hS : IsPreconnected S) (hSK : Disjoint S K)
    (hne : (S ∩ filledHull K).Nonempty) : S ⊆ filledHull K := by
  obtain ⟨x, hxS, hxH⟩ := hne
  have hScompl : S ⊆ Kᶜ := fun y hy => Set.disjoint_left.mp hSK hy
  have hScomp : S ⊆ connectedComponentIn Kᶜ x := hS.subset_connectedComponentIn hxS hScompl
  exact fun y hy => (mem_filledHull_iff_of_mem_connectedComponentIn (hScomp hy)).mpr hxH

/-- A bounded set whose frontier lies in `K` is contained in the filled hull of `K`. -/
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

/-- For compact `K` in the ambient locally connected space, the points whose complementary
component has compact closure form a compact set, provided every ambient connected component
is noncompact. -/
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

/-- A set with noncompact closure contains a point whose component outside a given compact set
has noncompact closure, provided every ambient connected component is noncompact. -/
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
