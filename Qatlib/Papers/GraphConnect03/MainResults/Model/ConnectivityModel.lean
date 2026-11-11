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

set_option backward.isDefEq.respectTransparency false

/-!
# ConnectivityModel — shared vocabulary for GraphConnect03

Dürr--Mhalla--Lei, *Quantum query complexity of graph connectivity*,
fixed arXiv:quant-ph/0303169v3 (5 Apr 2003), Section 1.

This file fixes the objects the paper works with:

* finite graphs on `Fin n`, both as a Boolean adjacency matrix (matrix model,
  `UndirectedMatrix`) and as a `k`-out-degree neighbour function (list model,
  `ListInstance`, with the simple-graph promise of the source, equation (1));
* connectivity and strong connectivity as reachability predicates;
* the per-search Grover charges `√n·log n` (matrix model) and `√k·log n`
  (list model) that Algorithm 1 spends on each stack operation (source p.4);
* the two quantum query-complexity interfaces against which the source's
  asymptotic theorems are stated.

The operational quantum-circuit semantics is *not* re-derived in this block.
The library's concrete bounded-error circuit model is
`QuantumAlgorithm.Concepts.QueryComplexity.AdversarySearch`
(`Circuit`, `Run`, `workspaceBitOracle`, `QueryCount`); the paper's `Q(·)` is
the minimum over correct bounded-error circuits in that model, and the
interfaces below name that quantity so that the asymptotic statements of the
paper have a fixed referent.
-/

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.GraphConnect03.MainResults.Model

open Filter

/-- Vertex type of the paper: `V = {v_0, …, v_{n-1}}`. -/
abbrev Vertex (n : ℕ) := Fin n

/-! ## Directed graphs and reachability -/

/-- A directed graph on `Fin n`, given by a decidable Boolean adjacency
function (the paper's adjacency matrix `M ∈ {0,1}^{n×n}`). -/
structure Digraph (n : ℕ) where
  /-- Boolean adjacency. -/
  adj : Vertex n → Vertex n → Bool

namespace Digraph

variable {n : ℕ}

/-- `G.Reach s t`: there is a directed path from `s` to `t` (including the
length-zero path at `s = t`). -/
def Reach (G : Digraph n) (s t : Vertex n) : Prop :=
  Relation.ReflTransGen (fun u v => G.adj u v = true) s t

/-- The length-zero path joins a vertex to itself. -/
theorem Reach.refl (G : Digraph n) (s : Vertex n) : G.Reach s s :=
  Relation.ReflTransGen.refl

/-- Reachability is transitive: concatenate two directed paths. -/
theorem Reach.trans {G : Digraph n} {a b c : Vertex n}
    (hab : G.Reach a b) (hbc : G.Reach b c) : G.Reach a c :=
  Relation.ReflTransGen.trans hab hbc

/-- A single edge is a path. -/
theorem Reach.edge {G : Digraph n} {u v : Vertex n} (h : G.adj u v = true) :
    G.Reach u v :=
  Relation.ReflTransGen.single h

/-- Reachability is monotone in the underlying adjacency relation. -/
theorem Reach.mono {G H : Digraph n} (hGH : ∀ u v, G.adj u v = true → H.adj u v = true)
    {s t : Vertex n} (h : G.Reach s t) : H.Reach s t := by
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | tail _ hbc ih => exact ih.tail (hGH _ _ hbc)

/-- `G.Connected`: every ordered pair of vertices is joined by a directed path.
For a directed graph this is strong connectivity (source Section 3). -/
def Connected (G : Digraph n) : Prop := ∀ s t : Vertex n, G.Reach s t

/-- Connectivity as a predicate is definitionally pairwise reachability. -/
theorem connected_iff (G : Digraph n) :
    G.Connected ↔ ∀ s t : Vertex n, G.Reach s t := Iff.rfl

end Digraph

/-! ## The matrix model (undirected) -/

/-- An undirected graph in the matrix model: a symmetric Boolean adjacency
matrix with zero diagonal, exactly the input promise of the source (p.2). -/
structure UndirectedMatrix (n : ℕ) where
  /-- Boolean adjacency matrix. -/
  adj : Vertex n → Vertex n → Bool
  /-- Symmetry promise. -/
  symm : ∀ u v, adj u v = adj v u
  /-- No loops. -/
  loopless : ∀ u, adj u u = false

namespace UndirectedMatrix

variable {n : ℕ}

/-- Forget the undirected promise. -/
def toDigraph (M : UndirectedMatrix n) : Digraph n := ⟨M.adj⟩

/-- Connectivity in the matrix model: every pair is joined by a path in the
symmetric adjacency relation. -/
def Connected (M : UndirectedMatrix n) : Prop := M.toDigraph.Connected

/-- Connectivity of the matrix model is definitionally pairwise reachability
in the underlying digraph. -/
theorem connected_iff (M : UndirectedMatrix n) :
    M.Connected ↔ ∀ s t : Vertex n, M.toDigraph.Reach s t := Iff.rfl

/-- The matrix model is undirected: reachability is symmetric. -/
theorem reach_symm (M : UndirectedMatrix n) {s t : Vertex n}
    (h : M.toDigraph.Reach s t) : M.toDigraph.Reach t s := by
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | tail _ hbc ih =>
      refine Relation.ReflTransGen.head ?_ ih
      simpa [toDigraph] using (M.symm _ _).trans hbc

end UndirectedMatrix

/-! ## The list model (directed, fixed out-degree) -/

/-- A `k`-out-degree directed graph in the adjacency-list model, encoded by
`f : [n] × [k] → [n]` with the simple-graph promise of source equation (1):
the outgoing neighbour list of every vertex is injective. -/
structure ListInstance (n k : ℕ) where
  /-- The neighbour function `f(u, i)`. -/
  nbr : Vertex n → Fin k → Vertex n
  /-- Source equation (1): no repeated neighbours. -/
  simple : ∀ u, Function.Injective (nbr u)

namespace ListInstance

variable {n k : ℕ}

/-- The underlying edge relation of a list instance. -/
def HasEdge (L : ListInstance n k) (u v : Vertex n) : Prop :=
  ∃ i : Fin k, L.nbr u i = v

/-- Reachability in the directed graph encoded by the list. -/
def Reach (L : ListInstance n k) (s t : Vertex n) : Prop :=
  Relation.ReflTransGen (fun u v => L.HasEdge u v) s t

/-- The length-zero list-model path joins a vertex to itself. -/
theorem Reach.refl (L : ListInstance n k) (s : Vertex n) : L.Reach s s :=
  Relation.ReflTransGen.refl

/-- List-model reachability is transitive. -/
theorem Reach.trans {L : ListInstance n k} {a b c : Vertex n}
    (hab : L.Reach a b) (hbc : L.Reach b c) : L.Reach a c :=
  Relation.ReflTransGen.trans hab hbc

/-- A single listed edge is a list-model path. -/
theorem Reach.edge {L : ListInstance n k} {u v : Vertex n} (h : L.HasEdge u v) :
    L.Reach u v :=
  Relation.ReflTransGen.single h

/-- `L.StrongConnected`: the directed graph is strongly connected. -/
def StrongConnected (L : ListInstance n k) : Prop := ∀ s t : Vertex n, L.Reach s t

/-- The undirected promise of the source for list-model connectivity
(source p.2): every listed edge is listed in both directions. -/
def UndirectedPromise (L : ListInstance n k) : Prop :=
  ∀ u v : Vertex n, L.HasEdge u v → L.HasEdge v u

/-- Connectivity of an undirected list instance. -/
def Connected (L : ListInstance n k) : Prop :=
  ∀ s t : Vertex n, Relation.SymmGen (fun u v => L.HasEdge u v) s t

end ListInstance

/-! ## Costs of Algorithm 1 -/

/-- Per-stack-operation Grover charge in the matrix model (source p.4):
`O(√n log n)` queries to the adjacency matrix. -/
def matrixGroverCharge (n : ℕ) : ℝ := Real.sqrt (n : ℝ) * Real.log (n : ℝ)

/-- Per-stack-operation Grover charge in the list model (source p.4):
`O(√k log n)` queries to the adjacency-list oracle. -/
def listGroverCharge (n k : ℕ) : ℝ := Real.sqrt (k : ℝ) * Real.log (n : ℝ)

/-- Number of Grover searches performed by Algorithm 1 when it marks a set
`visited` of vertices: one search per push and one per pop, hence at most
`2 · |visited|` (source p.4: "at most 2n Grover's searches"). -/
def dfsSearchCount {n : ℕ} (visited : Finset (Vertex n)) : ℕ := 2 * visited.card

/-- Total matrix-model query ledger of Algorithm 1. -/
def dfsMatrixCost {n : ℕ} (visited : Finset (Vertex n)) : ℝ :=
  (dfsSearchCount visited : ℝ) * matrixGroverCharge n

/-- Total list-model query ledger of Algorithm 1. -/
def dfsListCost (n k : ℕ) (visited : Finset (Vertex n)) : ℝ :=
  (dfsSearchCount visited : ℝ) * listGroverCharge n k

/-- Second stage of the source's Theorem 2 (p.5): for each of the `n` vertices
one minimum-finding search over `k` neighbours, each charged `√k log n`. -/
def backwardEdgeCost (n k : ℕ) : ℝ := (n : ℝ) * listGroverCharge n k

/-- Total query ledger of the two-stage Strong-Connectivity algorithm of the
source's Theorem 2. -/
def strongConnectivityListCost (n k : ℕ) (visited : Finset (Vertex n)) : ℝ :=
  dfsListCost n k visited + backwardEdgeCost n k

/-! ## Query-complexity interfaces -/

/-- The quantum query complexity `Q(Connectivity)` in the adjacency-matrix
model on `n` vertices: the minimum number of adjacency-matrix queries of a
bounded-error quantum algorithm deciding connectivity.  This is the quantity
of source Theorem 1 and Theorem 5; the operational semantics is the library's
concrete bounded-error bit-oracle circuit model
(`QuantumAlgorithm.Concepts.QueryComplexity.AdversarySearch`). -/
opaque matrixConnectivityQueryComplexity : ℕ → ℝ

/-- The quantum query complexity `Q(Strong Connectivity_k)` in the
adjacency-list model on `n` vertices with out-degree `k`: the minimum number of
list-oracle queries of a bounded-error quantum algorithm deciding strong
connectivity.  This is the quantity of source Theorem 2 and Theorem 4. -/
opaque listStrongConnectivityQueryComplexity : ℕ → ℕ → ℝ

/-- `Ω`-form used by the source's lower bounds, with an explicit threshold:
`f` is a lower bound for `q` from size `N` on. -/
def IsOmegaFrom (f q : ℕ → ℝ) (N : ℕ) : Prop :=
  ∃ c : ℝ, 0 < c ∧ ∀ n : ℕ, N ≤ n → c * f n ≤ q n

/-- `O`-form used by the source's upper bounds: `q` is bounded by `c · f` from
size `N` on. -/
def IsBigOFrom (q f : ℕ → ℝ) (N : ℕ) : Prop :=
  ∃ c : ℝ, 0 < c ∧ ∀ n : ℕ, N ≤ n → q n ≤ c * f n

end Qatlib.Papers.GraphConnect03.MainResults.Model
