/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Foundations.GraphMoves.IndepInsert
set_option backward.isDefEq.respectTransparency false
set_option warningAsError false

set_option autoImplicit false

namespace Qatlib.Papers.AltQAOAHad19.IndepMoves

universe u
variable {V : Type u}

open Qatlib.Foundations.GraphMoves.IndepInsert

theorem insertion_feasibility (G : SimpleGraph V) (S : Set V) (w : V) :
    G.IsIndepSet (insert w S) ↔ G.IsIndepSet S ∧ NoSelectedNeighbor G w S :=
  independent_insert_iff G S w

theorem removal_feasibility (G : SimpleGraph V) (S : Set V) (w : V)
    (hS : G.IsIndepSet S) : G.IsIndepSet (S \ {w}) :=
  independent_remove G S w hS

end Qatlib.Papers.AltQAOAHad19.IndepMoves
