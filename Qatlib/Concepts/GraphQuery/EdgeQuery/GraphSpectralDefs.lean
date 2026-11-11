/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Combinatorics.SimpleGraph.AdjMatrix
import Mathlib.Combinatorics.SimpleGraph.Clique
import Qatlib.Concepts.QueryWordCore.QueryMachinery.Oracle
import Qatlib.Concepts.GraphQuery.EdgeQuery.GraphCollision

/-!
# Boolean edge predicates and query circuits

This module encodes simple-graph adjacency and triangle existence as Boolean predicates. It
defines `edgeQuery`, a single oracle-query circuit, and `preservesEdges`, the compatibility
condition for relabeling vertices. These definitions model graph-query inputs as in
[DurrEtAl2006].

## Main statements

* `edgeBit` and `triangleBit`: Boolean adjacency and triangle tests.
* `edgeQuery`: the single-query circuit.
* `preservesEdges`: preservation of edge bits under a vertex equivalence.

## References

* [Dürr et al., 2006][DurrEtAl2006]
-/

open Qatlib.Foundations.QueryWordCore.Circuit

set_option autoImplicit false

namespace Qatlib.Concepts.GraphQuery.EdgeQuery

open Qatlib

/-- The Boolean adjacency indicator of a pair of vertices. -/
def edgeBit {V : Type*} (G : SimpleGraph V) [DecidableRel G.Adj] (e : V × V) : Bool :=
  decide (G.Adj e.1 e.2)

/-- The Boolean predicate asserting the existence of three cyclically adjacent vertices. -/
def triangleBit {V : Type*} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj] : Bool :=
  decide (∃ x y z : V, G.Adj x y ∧ G.Adj y z ∧ G.Adj z x)

/-- The circuit consisting of a single query step on a vertex-pair register and target bit. -/
def edgeQuery {V : Type*} : Circuit ((V × V) × Bool) := [Step.query]

/-- The condition that a vertex equivalence preserves all Boolean adjacency values. -/
def preservesEdges {V W : Type*} (G : SimpleGraph V) (H : SimpleGraph W)
    [DecidableRel G.Adj] [DecidableRel H.Adj] (e : V ≃ W) : Prop :=
  ∀ u v, edgeBit G (u,v) = edgeBit H (e u,e v)

end Qatlib.Concepts.GraphQuery.EdgeQuery
