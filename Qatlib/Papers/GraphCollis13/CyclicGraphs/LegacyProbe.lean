/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Papers.GraphCollis13.CyclicGraphs.ChunkCollision.SourceChunkCollision
public import Mathlib.Tactic.FinCases
public import Mathlib.Tactic.NormNum

@[expose] public section


/-! A finite counterexample to the legacy cyclic-window contract, not to the
source algorithm. The window contains its marked centre even when the graph
has no marked edge. -/

set_option autoImplicit false

namespace Qatlib.Papers.GraphCollis13.CyclicGraphs

open Qatlib.Papers.GraphCollis13.CyclicGraphs.ChunkCollision

/-- A single marked vertex lies in the legacy window and has no collision. -/
theorem single_mark_gap :
    (∃ s ∈ cIcc (6 : Fin 8) (2 : Fin 8), (s == 0) = true) ∧
      ¬ ∃ s t : Fin 8, s ∈ chunk (0 : Fin 8) 0 ∧
        (s == 0) = true ∧ (t == 0) = true ∧ (CI 8 2 2).Adj s t := by
  constructor
  · refine ⟨0, ?_, by decide⟩
    norm_num [cIcc, cwDist]
  · rintro ⟨s, t, _, hs, ht, hadj⟩
    have hs0 : s = 0 := by simpa using hs
    have ht0 : t = 0 := by simpa using ht
    subst s
    subst t
    exact (CI 8 2 2).loopless.irrefl 0 hadj

/-- The extremal-position and distance premises hold for the singleton chunk. -/
theorem singleton_premises :
    (0 : Fin 8) ∈ chunk (0 : Fin 8) 0 ∧
      (∀ s ∈ chunk (0 : Fin 8) 0, (s == 0) = true →
        cwDist (0 : Fin 8) s = 0) ∧
      cwDist (6 : Fin 8) 0 = 2 ∧ cwDist (0 : Fin 8) 2 = 2 := by
  refine ⟨self_mem_chunk _ _, ?_, by decide, by decide⟩
  intro s _ hs
  have hs0 : s = 0 := by simpa using hs
  subst s
  exact cwDist_self 0

end Qatlib.Papers.GraphCollis13.CyclicGraphs
