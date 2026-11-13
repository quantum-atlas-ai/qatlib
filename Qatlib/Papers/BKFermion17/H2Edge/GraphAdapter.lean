/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.BKFermion17.GraphWords
import Qatlib.Papers.BKFermion17.H2Edge.Relations

/-!
# The hydrogen graph as an indexed graph

This module instantiates `GraphWords.IndexedGraph` with the four hydrogen vertices and four
edges. It identifies the generic graph vertex and edge words with the explicit hydrogen Pauli
words and verifies that each vertex has degree two. See [SetiaWhitfield2018].

## Main statements

* `hydrogen_vertex_words`: generic vertex words agree with `h2B`.
* `hydrogen_edge_words`: generic edge words agree with the words of `h2A`.
* `hydrogen_degree`: every vertex has degree two.

## References

* [Setia and Whitfield, 2018][SetiaWhitfield2018]
-/

set_option backward.isDefEq.respectTransparency false

namespace Qatlib.Papers.BKFermion17.H2Edge
set_option autoImplicit false
open Qatlib.Concepts.PauliClifford.PauliAlgebra

/-- The indexed four-vertex, four-edge graph used in the hydrogen example. -/
def hydrogenGraph : GraphWords.IndexedGraph 4 4 where
  left := ![0,0,1,2]
  right := ![1,3,2,3]
  ordered := by decide
  simple := by decide

/-- The generic vertex Pauli word for the hydrogen graph equals the word of the explicit vertex
generator `h2B i`. -/
theorem hydrogen_vertex_words (i : Fin 4) : GraphWords.vertexWord hydrogenGraph i=(h2B i).word := by
  decide +revert

/-- The generic edge Pauli word for the hydrogen graph equals the word of its explicit oriented
edge element. See [Setia and Whitfield, Eqs. (24)–(25)][SetiaWhitfield2018]. -/
theorem hydrogen_edge_words (e : Fin 4) :
    GraphWords.edgeWord hydrogenGraph e=(h2A (hydrogenGraph.left e) (hydrogenGraph.right e)).word := by
  decide +revert

/-- Every vertex of the indexed hydrogen graph has degree two. -/
theorem hydrogen_degree (i : Fin 4) : GraphWords.degree hydrogenGraph i=2 := by
  decide +revert

end Qatlib.Papers.BKFermion17.H2Edge
