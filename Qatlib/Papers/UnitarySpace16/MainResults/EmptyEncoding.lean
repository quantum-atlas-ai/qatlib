/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Papers.UnitarySpace16.MainResults.Model.UnitarySpaceModel

@[expose] public section


set_option autoImplicit false

namespace Qatlib.Papers.UnitarySpace16.MainResults

open Qatlib.Papers.UnitarySpace16.MainResults.Model

/-- An encoding interface may reject every bit string under the legacy structure. -/
def emptyLocal (k : ℕ) : LocalHamiltonianEncoding k where
  decode := fun _ => none
  efficient := fun _ => True
  isLocal := fun _ => True
  frustrationFree := fun _ => True

/-- A promise problem with every input positive and no negative instances. -/
def allYes : PromiseProblem where
  yes := Set.univ
  no := ∅
  disjoint := by
    intro x _ hx
    exact hx

/-- The legacy polynomial-space interface contains the constant-accepting problem. -/
theorem allYes_pspace : allYes ∈ PSPACE := by
  refine ⟨{
    Config := Bool
    run := fun _ => true
    accept := id
    spaceUsed := fun _ => 0
    poly_space := ⟨1, by intro x; exact Nat.zero_le _⟩
  }, ?_, ?_⟩
  · intro x _
    rfl
  · intro x hx
    exact False.elim hx

/-- The arbitrary-encoding completeness claim fails for the encoding that decodes nothing. -/
theorem emptyFF_notComp :
    ¬ CompleteFor PolyTimeReduction
      (FrustrationFreeLocalHamiltonian 3 (emptyLocal 3)) PSPACE := by
  intro h
  obtain ⟨r, _hr, hyes, _hno⟩ := h.2 allYes allYes_pspace
  have hx := hyes [] (Set.mem_univ [])
  obtain ⟨_hff, I, hdecode, _⟩ := hx
  change (none : Option HamiltonianInstance) = some I at hdecode
  cases hdecode

end Qatlib.Papers.UnitarySpace16.MainResults
