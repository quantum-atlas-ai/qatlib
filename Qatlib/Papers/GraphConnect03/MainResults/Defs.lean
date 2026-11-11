/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Tactic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Data.Real.Sqrt
import Mathlib.Data.Finset.Card
import Mathlib.Data.Fintype.Card
import Mathlib.Order.Filter.Basic

/-!
# Graph query models and cost functions

This module defines Boolean adjacency-matrix and fixed-outdegree neighbor-list models, together
with directed reachability and associated graph predicates. It also introduces the Grover-search
charges, DFS cost expressions, abstract query-complexity quantities, and explicit-threshold
comparison predicates `IsBigOFrom` and `IsOmegaFrom`. See [DurrMhallaLei2003].

## Main statements

* `Reach.mono`: Directed reachability is preserved when every edge of the original graph is also
  an edge of the target graph.
* `dfsMatrixCost`: The DFS search count multiplied by the matrix-model Grover charge.
* `IsBigOFrom`: There is a positive real constant such that `q n ≤ c * f n` for every natural
  input at least `N`.

## References

* [Durr et al., 2003][DurrMhallaLei2003]
-/

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.GraphConnect03.MainResults.Defs

open Filter

/-- The type `Fin n` of vertex labels for an `n`-vertex graph. -/
abbrev Vertex (n : ℕ) := Fin n

/-- A directed graph on `Fin n` specified by a Boolean adjacency function [DurrMhallaLei2003]. -/
structure Digraph (n : ℕ) where

  adj : Vertex n → Vertex n → Bool

namespace Digraph

variable {n : ℕ}

/-- Directed reachability defined as the reflexive transitive closure of the graph's true
adjacency entries. -/
def Reach (G : Digraph n) (s t : Vertex n) : Prop :=
  Relation.ReflTransGen (fun u v => G.adj u v = true) s t

/-- Every vertex is reachable from itself in a directed graph. -/
theorem Reach.refl (G : Digraph n) (s : Vertex n) : G.Reach s s :=
  Relation.ReflTransGen.refl

/-- Directed reachability is transitive. -/
theorem Reach.trans {G : Digraph n} {a b c : Vertex n}
    (hab : G.Reach a b) (hbc : G.Reach b c) : G.Reach a c :=
  Relation.ReflTransGen.trans hab hbc

/-- A true adjacency entry gives directed reachability between its endpoints. -/
theorem Reach.edge {G : Digraph n} {u v : Vertex n} (h : G.adj u v = true) :
    G.Reach u v :=
  Relation.ReflTransGen.single h

/-- Directed reachability is preserved when every edge of the original graph is also an edge of
the target graph. -/
theorem Reach.mono {G H : Digraph n} (hGH : ∀ u v, G.adj u v = true → H.adj u v = true)
    {s t : Vertex n} (h : G.Reach s t) : H.Reach s t := by
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | tail _ hbc ih => exact ih.tail (hGH _ _ hbc)

/-- Every ordered pair of vertices is connected by directed reachability. -/
def Connected (G : Digraph n) : Prop := ∀ s t : Vertex n, G.Reach s t

/-- The directed graph's `Connected` predicate is equivalent to reachability between every
ordered pair of vertices. -/
theorem connected_iff (G : Digraph n) :
    G.Connected ↔ ∀ s t : Vertex n, G.Reach s t := Iff.rfl

end Digraph

/-- A symmetric, loopless Boolean adjacency matrix on `Fin n` [DurrMhallaLei2003]. -/
structure UndirectedMatrix (n : ℕ) where

  adj : Vertex n → Vertex n → Bool

  symm : ∀ u v, adj u v = adj v u

  loopless : ∀ u, adj u u = false

namespace UndirectedMatrix

variable {n : ℕ}

/-- The directed graph with the same adjacency function as the undirected matrix. -/
def toDigraph (M : UndirectedMatrix n) : Digraph n := ⟨M.adj⟩

/-- Connectivity of an undirected matrix is all-pairs reachability in its associated directed
graph. -/
def Connected (M : UndirectedMatrix n) : Prop := M.toDigraph.Connected

/-- An undirected matrix is connected exactly when all vertex pairs are reachable in its
associated directed graph. -/
theorem connected_iff (M : UndirectedMatrix n) :
    M.Connected ↔ ∀ s t : Vertex n, M.toDigraph.Reach s t := Iff.rfl

/-- Reachability in the directed graph associated to an undirected matrix is symmetric. -/
theorem reach_symm (M : UndirectedMatrix n) {s t : Vertex n}
    (h : M.toDigraph.Reach s t) : M.toDigraph.Reach t s := by
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | tail _ hbc ih =>
      refine Relation.ReflTransGen.head ?_ ih
      simpa [toDigraph] using (M.symm _ _).trans hbc

end UndirectedMatrix

/-- A neighbor-list instance with `k` ordered outgoing neighbors per vertex and no repeated
neighbor within a row [DurrMhallaLei2003]. -/
structure ListInstance (n k : ℕ) where

  nbr : Vertex n → Fin k → Vertex n

  simple : ∀ u, Function.Injective (nbr u)

namespace ListInstance

variable {n k : ℕ}

/-- There is an outgoing neighbor-list index at `u` whose value is `v`. -/
def HasEdge (L : ListInstance n k) (u v : Vertex n) : Prop :=
  ∃ i : Fin k, L.nbr u i = v

/-- Reachability in a neighbor-list instance is the reflexive transitive closure of `HasEdge`. -/
def Reach (L : ListInstance n k) (s t : Vertex n) : Prop :=
  Relation.ReflTransGen (fun u v => L.HasEdge u v) s t

/-- Every vertex is reachable from itself in a neighbor-list instance. -/
theorem Reach.refl (L : ListInstance n k) (s : Vertex n) : L.Reach s s :=
  Relation.ReflTransGen.refl

/-- Reachability in a neighbor-list instance is transitive. -/
theorem Reach.trans {L : ListInstance n k} {a b c : Vertex n}
    (hab : L.Reach a b) (hbc : L.Reach b c) : L.Reach a c :=
  Relation.ReflTransGen.trans hab hbc

/-- A listed edge gives reachability between its endpoints. -/
theorem Reach.edge {L : ListInstance n k} {u v : Vertex n} (h : L.HasEdge u v) :
    L.Reach u v :=
  Relation.ReflTransGen.single h

/-- Every vertex can reach every other vertex through listed outgoing edges. -/
def StrongConnected (L : ListInstance n k) : Prop := ∀ s t : Vertex n, L.Reach s t

/-- Every listed edge also occurs in the reverse direction [DurrMhallaLei2003]. -/
def UndirectedPromise (L : ListInstance n k) : Prop :=
  ∀ u v : Vertex n, L.HasEdge u v → L.HasEdge v u

/-- Every ordered pair of vertices is related by the symmetric closure of `HasEdge`. -/
def Connected (L : ListInstance n k) : Prop :=
  ∀ s t : Vertex n, Relation.SymmGen (fun u v => L.HasEdge u v) s t

end ListInstance

/-- The real search charge `√n * log n` for an adjacency-matrix row. -/
def matrixGroverCharge (n : ℕ) : ℝ := Real.sqrt (n : ℝ) * Real.log (n : ℝ)

/-- The real search charge `√k * log n` for a neighbor list of length `k`. -/
def listGroverCharge (n k : ℕ) : ℝ := Real.sqrt (k : ℝ) * Real.log (n : ℝ)

/-- Twice the cardinality of the visited vertex set. -/
def dfsSearchCount {n : ℕ} (visited : Finset (Vertex n)) : ℕ := 2 * visited.card

/-- The DFS search count multiplied by the matrix-model Grover charge. -/
def dfsMatrixCost {n : ℕ} (visited : Finset (Vertex n)) : ℝ :=
  (dfsSearchCount visited : ℝ) * matrixGroverCharge n

/-- The DFS search count multiplied by the neighbor-list Grover charge. -/
def dfsListCost (n k : ℕ) (visited : Finset (Vertex n)) : ℝ :=
  (dfsSearchCount visited : ℝ) * listGroverCharge n k

/-- The cost expression `n` times the neighbor-list Grover charge. -/
def backwardEdgeCost (n k : ℕ) : ℝ := (n : ℝ) * listGroverCharge n k

/-- The sum of the DFS list cost and the backward-edge cost. -/
def strongConnectivityListCost (n k : ℕ) (visited : Finset (Vertex n)) : ℝ :=
  dfsListCost n k visited + backwardEdgeCost n k

/-- An abstract real-valued quantity indexed by graph size for matrix-model connectivity query
complexity. -/
opaque matrixConnectivityQueryComplexity : ℕ → ℝ

/-- An abstract real-valued quantity indexed by graph size and outdegree for list-model
strong-connectivity query complexity. -/
opaque listStrongConnectivityQueryComplexity : ℕ → ℕ → ℝ

/-- There is a positive real constant such that `c * f n ≤ q n` for every natural input at least
`N`. -/
def IsOmegaFrom (f q : ℕ → ℝ) (N : ℕ) : Prop :=
  ∃ c : ℝ, 0 < c ∧ ∀ n : ℕ, N ≤ n → c * f n ≤ q n

/-- There is a positive real constant such that `q n ≤ c * f n` for every natural input at least
`N` [DurrMhallaLei2003]. -/
def IsBigOFrom (q f : ℕ → ℝ) (N : ℕ) : Prop :=
  ∃ c : ℝ, 0 < c ∧ ∀ n : ℕ, N ≤ n → q n ≤ c * f n

end Qatlib.Papers.GraphConnect03.MainResults.Defs
