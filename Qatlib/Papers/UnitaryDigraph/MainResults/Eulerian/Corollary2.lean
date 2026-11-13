/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.UnitaryDigraph.MainResults.Eulerian.Theorem3
import Qatlib.Papers.UnitaryDigraph.MainResults.LineDigraph.Theorem2

/-!
# Hamiltonicity from supplied Eulerian implications

This module assembles the implication in Corollary 2 from the supplied
unitary-line-digraph-to-Eulerian implication and the supplied Hamiltonicity result for strongly
connected Eulerian digraphs. Applying them to a strongly connected digraph whose line digraph is
unitary yields Hamiltonicity of that line digraph. See [Severini2003].

## Main statements

* `corollary2`: Hamiltonicity of the line digraph under the two supplied implications.

## References

* [Severini, 2003][Severini2003]
-/

set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.UnitaryDigraph.MainResults.Eulerian

open Qatlib.Papers.UnitaryDigraph.MainResults.Defs
open Qatlib.Papers.UnitaryDigraph.MainResults.LineDigraph

/-- Given the supplied Eulerian and Hamiltonicity implications, a strongly connected digraph
with unitary line digraph has a Hamiltonian line digraph. See [Severini, Corollary
2][Severini2003]. -/
theorem corollary2 {V : Type} [Fintype V] [DecidableEq V] (D : Defs.Digraph V)
    [Fintype (Arc D)] [DecidableEq (Arc D)]
    (hT3 : IsUnitaryDigraph (lineDigraph D) → Eulerian D)
    (hT2iii : StronglyConnected D → Eulerian D → Hamiltonian (lineDigraph D))
    (hsc : StronglyConnected D) (hU : IsUnitaryDigraph (lineDigraph D)) :
    Hamiltonian (lineDigraph D) :=
  hT2iii hsc (hT3 hU)

end Qatlib.Papers.UnitaryDigraph.MainResults.Eulerian
