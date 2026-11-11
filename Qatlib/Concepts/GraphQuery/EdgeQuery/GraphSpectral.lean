/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.GraphQuery.EdgeQuery.GraphSpectralDefs
import Qatlib.Concepts.QueryWordCore.QueryMachinery.Oracle

/-!
# Semantics of Boolean graph queries

This module connects Boolean edge and triangle predicates with simple-graph adjacency, adjacency
matrices, and three-vertex cliques. It verifies the one-query edge circuit, characterizes graph
collision, and converts edge-preserving vertex equivalences into graph isomorphisms. The
graph-query context is described in [DurrEtAl2006].

## Main statements

* `edge_query_semantics`: the action and resource counts of an edge query.
* `triangleBit_clique` and `collision_iff`: graph interpretations of Boolean predicates.
* `isoOfPreservesEdges`: construction of a graph isomorphism.

## References

* [Dürr et al., 2006][DurrEtAl2006]
-/

set_option backward.isDefEq.respectTransparency false
set_option warningAsError false
open Qatlib.Concepts.QueryWordCore.QueryMachinery
open Qatlib.Foundations.QueryWordCore.Circuit
open Qatlib.Foundations.PureStateMath

set_option autoImplicit false

namespace Qatlib.Concepts.GraphQuery.EdgeQuery

open Matrix

/-- The edge bit of a vertex pair is true exactly when the vertices are adjacent. -/
theorem edgeBit_true_iff {V : Type*} (G : SimpleGraph V) [DecidableRel G.Adj] (u v : V) :
    edgeBit G (u,v) = true ↔ G.Adj u v := by simp [edgeBit]

/-- The edge bit is true exactly when the corresponding natural-number adjacency-matrix entry is
one. -/
theorem edgeBit_matrix {V : Type*} (G : SimpleGraph V) [DecidableRel G.Adj] (u v : V) :
    edgeBit G (u,v) = true ↔ G.adjMatrix ℕ u v = 1 := by
  by_cases h : G.Adj u v <;> simp [edgeBit, h]

/-- Swapping the endpoints leaves the edge bit unchanged. -/
theorem edgeBit_symmetric {V : Type*} (G : SimpleGraph V) [DecidableRel G.Adj] (u v : V) :
    edgeBit G (u,v) = edgeBit G (v,u) := by simp [edgeBit, G.adj_comm]

/-- The edge bit at a repeated vertex is false. -/
theorem edgeBit_no_loop {V : Type*} (G : SimpleGraph V) [DecidableRel G.Adj] (u : V) :
    edgeBit G (u,u) = false := by simp [edgeBit]

/-- The edge-query circuit flips the target bit according to adjacency, uses one query, and
contains no fixed gates. -/
theorem edge_query_semantics {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (u v : V) (b : Bool) :
    Run (BitOracleOn (edgeBit G)) edgeQuery (Qatlib.Foundations.PureStateMath.Ket ((u,v),b)) =
        Qatlib.Foundations.PureStateMath.Ket ((u,v),b ^^ decide (G.Adj u v)) ∧
      QueryCount (edgeQuery (V := V)) = 1 ∧ GateCount (edgeQuery (V := V)) = 0 := by
  refine ⟨?_, rfl, rfl⟩
  exact run_query_bitOracleOn_ket (edgeBit G) (u,v) b

/-- The triangle predicate is true exactly when the graph has a clique with three vertices. -/
theorem triangleBit_clique {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] :
    triangleBit G = true ↔ ∃ s : Finset V, G.IsNClique 3 s := by
  simp only [triangleBit, decide_eq_true_eq]
  constructor
  · rintro ⟨x,y,z,hxy,hyz,hzx⟩
    exact ⟨{x,y,z}, G.is3Clique_triple_iff.mpr ⟨hxy, G.adj_symm hzx, hyz⟩⟩
  · rintro ⟨s, hs⟩
    obtain ⟨x,y,z,hxy,hxz,hyz,_⟩ := G.is3Clique_iff.mp hs
    exact ⟨x,y,z,hxy,hyz,G.adj_symm hxz⟩

/-- Preservation of Boolean edge bits is equivalent to preservation and reflection of adjacency. -/
theorem preservesEdges_iff {V W : Type*} (G : SimpleGraph V) (H : SimpleGraph W)
    [DecidableRel G.Adj] [DecidableRel H.Adj] (e : V ≃ W) :
    preservesEdges G H e ↔ ∀ u v, G.Adj u v ↔ H.Adj (e u) (e v) := by
  simp only [preservesEdges, edgeBit, decide_eq_decide]

/-- The graph isomorphism induced by a vertex equivalence preserving Boolean edge bits. -/
def isoOfPreservesEdges {V W : Type*} (G : SimpleGraph V) (H : SimpleGraph W)
    [DecidableRel G.Adj] [DecidableRel H.Adj] (e : V ≃ W) (h : preservesEdges G H e) :
    G ≃g H where
  toEquiv := e
  map_rel_iff' := fun {u v} => ((preservesEdges_iff G H e).mp h u v).symm

/-- Every graph isomorphism preserves Boolean edge bits. -/
theorem preservesEdges_of_iso {V W : Type*} (G : SimpleGraph V) (H : SimpleGraph W)
    [DecidableRel G.Adj] [DecidableRel H.Adj] (e : G ≃g H) :
    preservesEdges G H e.toEquiv := by
  apply (preservesEdges_iff G H e.toEquiv).mpr
  intro u v
  exact e.map_rel_iff.symm

/-- The graph-collision predicate is true exactly when an edge joins two vertices marked true. -/
theorem collision_iff {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (x : Fin n → Bool) :
    graphCollision (fun u v => edgeBit G (u,v)) x = true ↔
      ∃ u v, G.Adj u v ∧ x u = true ∧ x v = true := by
  simp [graphCollision, edgeBit]

end Qatlib.Concepts.GraphQuery.EdgeQuery
