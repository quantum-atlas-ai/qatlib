/-
Copyright (c) 2026 Quantum Atlas Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quantum Atlas Contributors
-/

module

public import Qatlib.Concepts.GraphQuery.CosetReduction.SimpleGraphCosetReductionStat
public import Qatlib.Concepts.GraphQuery.CosetReduction.GraphCosetReductionGrap

@[expose] public section

set_option autoImplicit false

namespace Qatlib.Concepts.GraphQuery.CosetReduction

/-- Establishes the simple graph coset reduction specified by `SimpleGraphCosetReduction`. -/
theorem simpleGraphCosetReduction : SimpleGraphCosetReduction := by
  intro V G H _ _
  rw [← graphCosetReduction V
    (fun i j => decide (G.Adj i j)) (fun i j => decide (H.Adj i j))]
  constructor
  · rintro ⟨e⟩
    refine ⟨e.toEquiv, ?_⟩
    intro i j
    exact decide_eq_decide.mpr e.map_adj_iff
  · rintro ⟨p, hp⟩
    refine ⟨{ toEquiv := p, map_rel_iff' := ?_ }⟩
    intro i j
    exact decide_eq_decide.mp (hp i j)

end Qatlib.Concepts.GraphQuery.CosetReduction
