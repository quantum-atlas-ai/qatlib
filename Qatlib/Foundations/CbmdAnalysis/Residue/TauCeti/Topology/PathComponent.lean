/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors, Qatlib Contributors
-/

import Qatlib.Foundations.CbmdAnalysis.Residue.TauCeti.CBMDCompat

import Mathlib.Topology.Connected.LocPathConnected
import Qatlib.Foundations.CbmdAnalysis.Residue.TauCeti.Topology.Homotopy.Path

/-!
# Path components and representative basepoints

Transfers ambient homotopies to path-component subtypes and shows that path-component classes
distinguish points in totally disconnected spaces. `PathComponentBasepoints` packages a
representative in each path component, with a noncomputable choice construction.

These component tools support the topological contour framework associated with [WangEtAl2026].

## Main statements

* `homotopic_pathComponent_of_map_subtypeVal_homotopic`: Paths in a path-component subtype are
  homotopic there whenever their images under subtype inclusion are homotopic in the ambient
  space.
* `PathComponentBasepoints`: A choice of one representative point for each path-component class.
* `PathComponentBasepoints.choose`: Chooses a representative point for every path-component
  class.

## References

* [Wang et al., 2026][WangEtAl2026]
-/

set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

namespace Qatlib.Foundations.CbmdAnalysis.Residue

section

open scoped _root_.unitInterval
open Topology

namespace TauCeti

variable {X : Type*} [TopologicalSpace X] (x₀ : X)

/-- Paths in a path-component subtype are homotopic there whenever their images under subtype
inclusion are homotopic in the ambient space. -/
theorem homotopic_pathComponent_of_map_subtypeVal_homotopic
    {a b : pathComponent x₀} {γ δ : Path a b}
    (h : (γ.map continuous_subtype_val).Homotopic
      (δ.map continuous_subtype_val)) :
    γ.Homotopic δ := by
  obtain ⟨H⟩ := h
  have hγmem : ∀ t, (γ.map continuous_subtype_val) t ∈ pathComponent x₀ := fun t =>
    (γ t).2
  have hmem : ∀ p : I × I, H p ∈ pathComponent x₀ := fun p =>
    Joined.mem_pathComponent
      (Path.mem_pathComponent (H.evalAt p.2) p.1)
      (H.map_zero_left p.2 ▸ hγmem p.2)
  exact Path.homotopic_of_continuous_square (fun p => ⟨H p, hmem p⟩)
    (H.continuous.subtype_mk hmem) (fun t => Subtype.ext (H.map_zero_left t))
    (fun t => Subtype.ext (H.map_one_left t)) (fun t => Subtype.ext (H.source t))
    (fun t => Subtype.ext (H.target t))

instance instPathConnectedSpaceSubtypePathComponent :
    PathConnectedSpace (pathComponent x₀) :=
  isPathConnected_iff_pathConnectedSpace.mp isPathConnected_pathComponent

instance instLocPathConnectedSpaceSubtypePathComponent [LocallyPathConnectedSpace X] :
    LocallyPathConnectedSpace (pathComponent x₀) :=
  (IsOpen.pathComponent x₀).locallyPathConnectedSpace

/-- The basepoint `x₀` regarded as a point of its own path-component subtype. -/
abbrev pathComponentSelf : (pathComponent x₀ : Set X) :=
  ⟨x₀, mem_pathComponent_self x₀⟩

/-- Points joined by a path in a totally disconnected space are equal. -/
theorem _root_.Qatlib.Foundations.CbmdAnalysis.Residue.Joined.eq_of_totallyDisconnectedSpace [TotallyDisconnectedSpace X] {x y : X}
    (h : Joined x y) : x = y := by
  obtain ⟨γ⟩ := h
  simpa using (isPreconnected_range γ.continuous).subsingleton
    (Set.mem_range_self 0) (Set.mem_range_self 1)

/-- The map from points to their path-component classes is injective in a totally disconnected
space. -/
theorem _root_.Qatlib.Foundations.CbmdAnalysis.Residue.ZerothHomotopy.mk_injective_of_totallyDisconnectedSpace
    [TotallyDisconnectedSpace X] : Function.Injective (ZerothHomotopy.mk (X := X)) :=
  fun _ _ h ↦ Joined.eq_of_totallyDisconnectedSpace (Quotient.exact h)

/-- A choice of one representative point for each path-component class. -/
@[ext]
structure PathComponentBasepoints (X : Type*) [TopologicalSpace X] where

  point : ZerothHomotopy X → X

  mk_point : ∀ c, ZerothHomotopy.mk (point c) = c

attribute [simp] PathComponentBasepoints.mk_point

/-- Chooses a representative point for every path-component class. -/
noncomputable def PathComponentBasepoints.choose (X : Type*) [TopologicalSpace X] :
    PathComponentBasepoints X :=
  ⟨Function.surjInv ZerothHomotopy.mk_surjective, Function.surjInv_eq _⟩

instance (X : Type*) [TopologicalSpace X] : Nonempty (PathComponentBasepoints X) :=
  ⟨PathComponentBasepoints.choose X⟩

end TauCeti

end
end Qatlib.Foundations.CbmdAnalysis.Residue
