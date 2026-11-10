/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.UnitaryDigraph.MainResults.Eulerian.Theorem3
import Qatlib.Papers.UnitaryDigraph.MainResults.LineDigraph.Theorem2
set_option backward.isDefEq.respectTransparency false
set_option warningAsError false

set_option autoImplicit false
set_option linter.unusedSectionVars false
noncomputable section

namespace Qatlib.Papers.UnitaryDigraph.MainResults.Eulerian

open Qatlib.Papers.UnitaryDigraph.MainResults.Defs
open Qatlib.Papers.UnitaryDigraph.MainResults.LineDigraph

theorem corollary2 {V : Type} [Fintype V] [DecidableEq V] (D : Defs.Digraph V)
    [Fintype (Arc D)] [DecidableEq (Arc D)]
    (hT3 : IsUnitaryDigraph (lineDigraph D) → Eulerian D)
    (hT2iii : StronglyConnected D → Eulerian D → Hamiltonian (lineDigraph D))
    (hsc : StronglyConnected D) (hU : IsUnitaryDigraph (lineDigraph D)) :
    Hamiltonian (lineDigraph D) :=
  hT2iii hsc (hT3 hU)

end Qatlib.Papers.UnitaryDigraph.MainResults.Eulerian
