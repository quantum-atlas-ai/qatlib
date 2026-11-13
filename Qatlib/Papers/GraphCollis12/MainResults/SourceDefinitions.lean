/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Combinatorics.SimpleGraph.DegreeSum
import Mathlib.Combinatorics.SimpleGraph.Clique
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Real.Sqrt
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Exp
import Qatlib.Concepts.GraphQuery.EdgeQuery.GraphCollision

set_option backward.isDefEq.respectTransparency false

/-!
# GraphCollis12 — shared vocabulary of Gavinsky–Ito (arXiv:1204.1527v1)

Fixed source: *A quantum query algorithm for the graph collision problem*,
Dmitry Gavinsky and Tsuyoshi Ito, arXiv:1204.1527v1 (6 Apr 2012).

This file fixes, on finite vertex set `Fin n`, the paper's §2 vocabulary:

* `markedSet x` — the set `S = {v | x_v = 1}` of marked vertices (p.3);
* `deg G v` and `degSum G S` — the degree of a vertex and `deg(S) = Σ_{v∈S} deg(v)` (p.3);
* `IsIndep G S` and `alphaStar G = max{deg(S) : S independent}` (p.3);
* the promise `deg(S) ≤ k` of Lemma 7 (p.5);
* the random-graph model `μ_{n,p}` of §5 (p.6): every unordered edge present
  independently with probability `p`.

The graph itself is given explicitly and is *not* queried; only `x ∈ {0,1}^V` is
oracle input (Definition 1, p.3).  The decision predicate is the shared
definition `Qatlib.Concepts.GraphQuery.EdgeQuery.graphCollision`,
which we bridge to `SimpleGraph` through `adjOf` below.

Boundary: this file declares the vocabulary and elementary bridge lemmas only.
The span-program witness construction (Lemma 7) and the probability bounds
(Lemma 8 / Theorem 9) live with their own consumers.
-/

set_option autoImplicit false
noncomputable section

open scoped Classical BigOperators
open Qatlib.Concepts.GraphQuery.EdgeQuery

namespace Qatlib.Papers.GraphCollis12.MainResults

/-- The adjacency matrix (as a `Bool`-valued function on `Fin n`) of a `SimpleGraph`,
fed to the shared `graphCollision` decision predicate. -/
def adjOf {n : ℕ} (G : SimpleGraph (Fin n)) : Fin n → Fin n → Bool :=
  fun u v => decide (G.Adj u v)

/-- The set of marked vertices `S = {v | x_v = 1}` (paper p.3).  Lists each marked
vertex once. -/
def markedSet {n : ℕ} (x : Fin n → Bool) : Finset (Fin n) :=
  Finset.univ.filter fun v => x v = true

/-- `v` is marked, `x_v = 1`. -/
def IsMarked {n : ℕ} (x : Fin n → Bool) (v : Fin n) : Prop := x v = true

/-- Membership in `markedSet` is exactly `x v = true`. -/
@[simp] theorem mem_markedSet {n : ℕ} (x : Fin n → Bool) (v : Fin n) :
    v ∈ markedSet x ↔ x v = true := by
  simp [markedSet]

/-- Degree of a vertex, as the cardinality of the neighbour filter.  For a simple
graph this is the paper's `deg(v)` on p.3. -/
def deg {n : ℕ} (G : SimpleGraph (Fin n)) (v : Fin n) : ℕ :=
  (Finset.univ.filter fun w => G.Adj v w).card

/-- Total degree `deg(S) = Σ_{v∈S} deg(v)` of a vertex set (paper p.3). -/
def degSum {n : ℕ} (G : SimpleGraph (Fin n)) (S : Finset (Fin n)) : ℕ :=
  ∑ v ∈ S, deg G v

/-- `S` is an independent set of `G`: no two of its vertices are adjacent. -/
def IsIndep {n : ℕ} (G : SimpleGraph (Fin n)) (S : Finset (Fin n)) : Prop :=
  ∀ u ∈ S, ∀ v ∈ S, ¬ G.Adj u v

/-- `α*(G) = max{deg(S) : S independent in G}` (paper p.3).  Defined as the maximum
of `degSum` over all independent vertex sets; the empty set is independent, so the
value is attained and nonnegative. -/
def alphaStar {n : ℕ} (G : SimpleGraph (Fin n)) : ℕ :=
  (Finset.univ.filter fun S : Finset (Fin n) => IsIndep G S).sup (degSum G)

/-- The promise domain of Lemma 7 (p.5): the marked set `S` satisfies `deg(S) ≤ k`. -/
def PromiseDegLe {n : ℕ} (G : SimpleGraph (Fin n)) (k : ℕ) (x : Fin n → Bool) : Prop :=
  degSum G (markedSet x) ≤ k

/-! ### Random-graph model `μ_{n,p}` (§5, p.6)

The paper models a random graph on `[n]` where each (unordered) edge is present with
probability `p`, independently.  We realise the distribution by the product weight
`p^{#edges} · (1-p)^{N - #edges}` where `N = C(n,2)` is the number of possible edges,
summed over all simple graphs on `Fin n`. -/

/-- Number `C(n,2)` of possible edges on `n` vertices. -/
def numPairs (n : ℕ) : ℕ := n.choose 2

/-- Product weight of a simple graph under `μ_{n,p}`. -/
def muWeight {n : ℕ} (p : ℝ) (G : SimpleGraph (Fin n)) : ℝ :=
  p ^ G.edgeFinset.card * (1 - p) ^ (numPairs n - G.edgeFinset.card)

/-- Probability of an event `E` under `μ_{n,p}`: the weighted sum over all graphs. -/
def muPr {n : ℕ} (p : ℝ) (E : SimpleGraph (Fin n) → Prop) : ℝ :=
  ∑ G : SimpleGraph (Fin n), if E G then muWeight p G else 0

/-- `#G.edgeFinset ≤ C(n,2)`; used to keep the exponent `N - #edges` meaningful. -/
theorem card_edgeFinset_le_numPairs {n : ℕ} (G : SimpleGraph (Fin n)) :
    G.edgeFinset.card ≤ numPairs n := by
  simpa [numPairs] using G.card_edgeFinset_le_card_choose_two

end Qatlib.Papers.GraphCollis12.MainResults
