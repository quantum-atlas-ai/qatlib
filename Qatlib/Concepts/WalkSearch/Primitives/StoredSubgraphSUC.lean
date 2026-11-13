/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.WalkSearch.QuantumAccess.ResidualDiagnosticContracts

/-!
# Obstructions to the stored-subgraph contract

This module refutes `StoredSubgraphSUC` in two ways: its positive cost requirements fail on the
empty stored set, and its looplessness requirement conflicts with unrestricted adjacency inputs.
The results identify boundary conditions needed when specifying stored graph data for
quantum-walk search [MagniezNayakRolandSantha2011].

## Main statements

* `storedSubgraphSUC_empty_obstruction`: the empty-set contradiction.
* `storedSubgraphSUC_loop_obstruction`: the looped-input contradiction.

## References

* [Magniez et al., 2011][MagniezNayakRolandSantha2011]
-/

open Qatlib.Concepts.WalkSearch.QuantumAccess.Walk

set_option autoImplicit false

namespace Qatlib.Concepts.WalkSearch.Primitives

/-- The proposition `StoredSubgraphSUC` is false because the empty stored set conflicts with its
strictly positive update-cost requirement. -/
theorem storedSubgraphSUC_empty_obstruction : ¬ StoredSubgraphSUC := by
  intro h
  obtain ⟨_D, _edges, _symm, _loops, s, u, c, _hs, hu, _hc, _hsp, hup⟩ :=
    h 1 (fun _ _ => false) ∅
  simp only [Finset.card_empty] at hu
  omega

/-- The proposition `StoredSubgraphSUC` is false because unrestricted adjacency may force a
stored loop. -/
theorem storedSubgraphSUC_loop_obstruction : ¬ StoredSubgraphSUC := by
  intro h
  obtain ⟨D, hedges, _symm, hloops, _costs⟩ := h 1 (fun _ _ => true) Finset.univ
  exact hloops 0 ((hedges 0 0).mpr (by simp))

end Qatlib.Concepts.WalkSearch.Primitives
