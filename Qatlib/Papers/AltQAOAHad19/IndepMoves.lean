/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Foundations.GraphMoves.IndepInsert

/-!
# Feasible moves for independent sets

Records the insertion and removal rules for independent sets used in constrained
alternating-operator constructions. Insertion is feasible exactly when the original set is
independent and the inserted vertex has no selected neighbor, while removal preserves
independence. See [HadfieldEtAl2019].

## Main statements

* `insertion_feasibility`: the exact condition for inserting a vertex.
* `removal_feasibility`: removing a vertex preserves independence.

## References

* [Hadfield et al., 2019][HadfieldEtAl2019]
-/

set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false

namespace Qatlib.Papers.AltQAOAHad19.IndepMoves

universe u
variable {V : Type u}

open Qatlib.Foundations.GraphMoves.IndepInsert

/-- Inserting `w` preserves independence exactly when `S` is independent and `w` has no neighbor
in `S` [Hadfield et al., Section 4.2.1][HadfieldEtAl2019]. -/
theorem insertion_feasibility (G : SimpleGraph V) (S : Set V) (w : V) :
    G.IsIndepSet (insert w S) ↔ G.IsIndepSet S ∧ NoSelectedNeighbor G w S :=
  independent_insert_iff G S w

/-- Removing `w` from an independent set leaves an independent set [Hadfield et al., Section
4.2.1][HadfieldEtAl2019]. -/
theorem removal_feasibility (G : SimpleGraph V) (S : Set V) (w : V)
    (hS : G.IsIndepSet S) : G.IsIndepSet (S \ {w}) :=
  independent_remove G S w hS

end Qatlib.Papers.AltQAOAHad19.IndepMoves
