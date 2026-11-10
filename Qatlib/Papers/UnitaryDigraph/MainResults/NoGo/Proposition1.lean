/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.UnitaryDigraph.MainResults.Defs
import Qatlib.Papers.UnitaryDigraph.MainResults.Quadrangular
import Qatlib.Papers.UnitaryDigraph.MainResults.Permutation
set_option backward.isDefEq.respectTransparency false
set_option warningAsError false

set_option autoImplicit false
set_option linter.unusedSectionVars false
noncomputable section

namespace Qatlib.Papers.UnitaryDigraph.MainResults.NoGo

open Qatlib.Papers.UnitaryDigraph.MainResults.Defs
open Qatlib.Papers.UnitaryDigraph.MainResults.Quadrangular
open Qatlib.Papers.UnitaryDigraph.MainResults.Permutation
open Qatlib.Papers.UnitaryDigraph.MainResults.Defs.Digraph

theorem nPath_inter {n : ℕ} (hn : 3 ≤ n) :
    ((nPath n).outNbrs ⟨0, by omega⟩ ∩ (nPath n).outNbrs ⟨2, by omega⟩)
      = ({⟨1, by omega⟩} : Set (Fin n)) := by
  ext j
  rw [Set.mem_inter_iff, mem_outNbrs, mem_outNbrs]
  simp only [nPath, Set.mem_singleton_iff]
  constructor
  · rintro ⟨h0, _h2⟩
    rcases h0 with h0 | h0
    · exact Fin.ext (by simpa using h0.symm)
    · omega
  · rintro rfl
    constructor
    · left; simp
    · right; simp

theorem nPath_not_outQuadrangular {n : ℕ} (hn : 3 ≤ n) :
    ¬ OutQuadrangular (nPath n) := by
  intro h
  have hcard : ((nPath n).outNbrs ⟨0, by omega⟩ ∩ (nPath n).outNbrs ⟨2, by omega⟩).ncard = 1 := by
    rw [nPath_inter hn, Set.ncard_singleton]
  have hne : (⟨0, by omega⟩ : Fin n) ≠ ⟨2, by omega⟩ := by
    intro he
    have := congrArg Fin.val he
    simp at this
  exact h ⟨0, by omega⟩ ⟨2, by omega⟩ hne hcard

theorem nPath_not_unitary {n : ℕ} (hn : 3 ≤ n) : ¬ IsUnitaryDigraph (nPath n) :=
  fun hU => nPath_not_outQuadrangular hn (outQuadrangular_of_isUnitaryDigraph _ hU)

theorem proposition1 {V : Type} [Fintype V] [DecidableEq V] (D : Defs.Digraph V) (n : ℕ)
    (hn : 3 ≤ n) (h : PermEquivalentTo D (nPath n)) : ¬ IsUnitaryDigraph D := by
  intro hUD
  exact nPath_not_unitary hn ((lemma2 h).mp hUD)

end Qatlib.Papers.UnitaryDigraph.MainResults.NoGo
