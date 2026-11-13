/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors, Qatlib Contributors

Adapted from https://github.com/TauCetiProject/TauCeti@3780371c
-/

import Qatlib.Foundations.CbmdAnalysis.Residue.TauCeti.CBMDCompat

import Mathlib.Topology.Connected.Basic

/-!
# Frontiers of preconnected sets and images

Proves that a preconnected set meeting both sides of a set meets its frontier. Further lemmas
bound image frontiers using open images, domain covers, and injective open maps.

These boundary estimates support the topological contour arguments associated with
[WangEtAl2026].

## Main statements

* `IsPreconnected.inter_frontier_nonempty`: A preconnected set meeting both a set and its
  complement also meets its frontier.
* `frontier_image_subset_of_closure_subset`: An injective open map carries the frontier of an
  image into the image of the original frontier together with an exceptional set, under the
  stated closure inclusion.

## References

* [Wang et al., 2026][WangEtAl2026]
-/

set_option backward.isDefEq.respectTransparency false

namespace Qatlib.Foundations.CbmdAnalysis.Residue

section

namespace TauCeti

open _root_.Set

section Straddle

variable {X : Type*} [TopologicalSpace X] {S V : Set X}

/-- A preconnected set meeting both a set and its complement also meets its frontier. -/
theorem _root_.IsPreconnected.inter_frontier_nonempty (hS : IsPreconnected S)
    (h₁ : (S ∩ V).Nonempty) (h₂ : (S \ V).Nonempty) : (S ∩ frontier V).Nonempty := by
  by_contra hcon
  have hsub : S ⊆ interior V ∪ interior Vᶜ := by
    rw [← compl_frontier_eq_union_interior]
    exact fun x hx hxf => hcon ⟨x, hx, hxf⟩
  have hdisj : Disjoint (interior V) (interior Vᶜ) :=
    disjoint_compl_right.mono interior_subset interior_subset
  rcases hS.subset_or_subset isOpen_interior isOpen_interior hdisj hsub with h | h
  · obtain ⟨x, hxS, hxV⟩ := h₂
    exact hxV (interior_subset (h hxS))
  · obtain ⟨x, hxS, hxV⟩ := h₁
    exact interior_subset (h hxS) hxV

end Straddle

section ImageSplit

variable {X Y : Type*} [TopologicalSpace Y] {f : X → Y} {U s t u : Set X}

/-- For two disjoint open images and a domain cover by three sets, the frontier of the first
image lies in the third image or the frontier of the full image. -/
theorem frontier_image_subset_image_union_frontier_image (hfs : IsOpen (f '' s))
    (hft : IsOpen (f '' t)) (hst : Disjoint (f '' s) (f '' t)) (hsU : s ⊆ U)
    (hcov : U ⊆ s ∪ t ∪ u) :
    frontier (f '' s) ⊆ f '' u ∪ frontier (f '' U) := by
  intro p hp
  have hpΩ : p ∈ closure (f '' U) := closure_mono (image_mono hsU) hp.1
  rw [closure_eq_self_union_frontier] at hpΩ
  rcases hpΩ with hpin | hpfr
  · obtain ⟨w, hw, rfl⟩ := hpin
    rcases hcov hw with (hws | hwt) | hwu
    · exact absurd ⟨mem_image_of_mem f hws, hp⟩
        (eq_empty_iff_forall_notMem.mp hfs.inter_frontier_eq (f w))
    · obtain ⟨q, hqt, hqs⟩ := mem_closure_iff.mp hp.1 _ hft (mem_image_of_mem f hwt)
      exact absurd hqs (disjoint_right.mp hst hqt)
    · exact Or.inl (mem_image_of_mem f hwu)
  · exact Or.inr hpfr

end ImageSplit

section Inside

variable {X : Type*} [TopologicalSpace X] {A V : Set X}

/-- If `A ⊆ V`, the intersection of the frontier of `V` with the closure of `A` equals its
intersection with the frontier of `A`. -/
theorem frontier_inter_closure_eq_frontier_inter_frontier (hAV : A ⊆ V) :
    frontier V ∩ closure A = frontier V ∩ frontier A := by
  rw [closure_eq_self_union_frontier, inter_union_distrib_left]
  refine union_eq_right.mpr fun x hx =>
    ⟨hx.1, (mem_frontier_iff_notMem_interior hx.2).mpr fun hint => ?_⟩
  exact (mem_frontier_iff_notMem_interior (hAV hx.2)).mp hx.1 (interior_mono hAV hint)

end Inside

section OpenInjectiveImage

variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] {f : X → Y} {s : Set X}
  {t : Set Y}

/-- An injective open map carries the frontier of an image into the image of the original
frontier together with an exceptional set, under the stated closure inclusion. -/
theorem frontier_image_subset_of_closure_subset (hf : IsOpenMap f) (hfi : Function.Injective f)
    (hcl : closure (f '' s) ⊆ f '' closure s ∪ t) :
    frontier (f '' s) ⊆ f '' frontier s ∪ t := by
  refine (Set.diff_subset_diff hcl (hf.image_interior_subset s)).trans ?_
  rw [Set.union_diff_distrib, ← Set.image_diff hfi]
  exact Set.union_subset_union_right _ Set.diff_subset

end OpenInjectiveImage

end TauCeti

end
end Qatlib.Foundations.CbmdAnalysis.Residue
