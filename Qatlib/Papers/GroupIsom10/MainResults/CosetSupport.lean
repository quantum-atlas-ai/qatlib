/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Papers.GroupIsom10.MainResults.CosetSpecs

@[expose] public section


/-! # Pure mathematical existence of a finite coset answer

This constructs an actual representative and a generating list when the
intersection is nonempty. The list enumerates a subgroup: no uniform short
list, black-box quantum implementation, cost, or success probability follows.
-/

set_option autoImplicit false
noncomputable section
open scoped Classical
open Qatlib.Foundations.FiniteGroups.HiddenCosets.Intersection
open Qatlib.Foundations.FiniteGroups.HiddenCosets.Generators
open Qatlib.Papers.GroupIsom10.MainResults.CosetSpecs

namespace Qatlib.Papers.GroupIsom10.MainResults.CosetSupport

/-- A finite group admits a genuine mathematical answer to each coset intersection. -/
theorem answerExists {G : Type*} [Group G] [Fintype G] (inp : CosetInput G) :
    ∃ o : Option (G × List G), CosetValid inp o := by
  let H := listClosure inp.gens1
  let K := listClosure inp.gens2
  by_cases h : (coset inp.x H ∩ coset inp.y K).Nonempty
  · obtain ⟨z, hz⟩ := h
    obtain ⟨gs, hgs⟩ := hasGenerators (H ⊓ K)
    refine ⟨some (z, gs), ?_⟩
    change coset inp.x H ∩ coset inp.y K = coset z (listClosure gs)
    rw [hgs]
    exact interAt H K inp.x inp.y z hz
  · refine ⟨none, ?_⟩
    exact Set.not_nonempty_iff_eq_empty.mp h

end Qatlib.Papers.GroupIsom10.MainResults.CosetSupport
