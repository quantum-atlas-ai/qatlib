/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.WalkSearch.QuantumAccess.ResidualDiagnosticContracts
set_option warningAsError false

open Qatlib.Concepts.WalkSearch.QuantumAccess.Walk

set_option autoImplicit false

namespace Qatlib.Concepts.WalkSearch.Primitives

theorem storedSubgraphSUC_empty_obstruction : ¬ StoredSubgraphSUC := by
  intro h
  obtain ⟨_D, _edges, _symm, _loops, s, u, c, _hs, hu, _hc, _hsp, hup⟩ :=
    h 1 (fun _ _ => false) ∅
  simp only [Finset.card_empty] at hu
  omega

theorem storedSubgraphSUC_loop_obstruction : ¬ StoredSubgraphSUC := by
  intro h
  obtain ⟨D, hedges, _symm, hloops, _costs⟩ := h 1 (fun _ _ => true) Finset.univ
  exact hloops 0 ((hedges 0 0).mpr (by simp))

end Qatlib.Concepts.WalkSearch.Primitives
