/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.DQIAdvantage25.MainResults.Model.CutGirthModel
import Mathlib.Combinatorics.SimpleGraph.Acyclic

set_option backward.isDefEq.respectTransparency false

/-!
# Lemma 5: tree partition of a connected high-girth graph (paper p.9–10)

Source: Ojas Parekh, *No Quantum Advantage in Decoded Quantum Interferometry for MaxCut*,
arXiv:2509.19966v2 (2025-09-30), Lemma 5, Section 3, p.9.

> **Lemma 5.** Suppose `G ∈ 𝒢` is a connected graph with girth `g = Ω(m)`. Then the vertices of
> `G` can be partitioned into vertex-disjoint trees `T₁, …, T_t` where (i) `t = O(1)`, and (ii)
> there is at most one edge in `G` between any two `T_i` and `T_j`.

**Paper proof** (p.9–10). Set `d = ⌊(g-3)/4⌋` and take a spanning tree `T`. Repeatedly cut off,
from the deepest leaf upwards, the subtree `S_i` of depth `d`; the induced subgraphs `T_i = G[S_i]`
are trees, `t = O(1)` because each truncated tree has at least `d` edges and `d = Ω(m)`, and a
second edge between `T_i`, `T_j` would create a cycle of length `≤ 4d + 2 < g`.

The statement below quantifies the `O(1)` of (i) as a bound `C` depending only on the implicit
constant `c` of `g = Ω(m)`, and (ii) as `Set.Subsingleton` of the set of edges with one endpoint
in `part i` and one in `part j`.
-/

open scoped BigOperators
open Qatlib.Papers.DQIAdvantage25.MainResults.Model

namespace Qatlib.Papers.DQIAdvantage25.MainResults

namespace Lemma5

variable {V : Type*}

/-- The set of edges of `G` with one endpoint in `A` and the other in `B`. This is the paper's
"edge in `G` between `T_i` and `T_j`" (Lemma 5(ii), p.10). -/
def EdgesBetween (G : SimpleGraph V) (A B : Set V) : Set (Sym2 V) :=
  {e | e ∈ G.edgeSet ∧ ∃ a ∈ A, ∃ b ∈ B, e = s(a, b)}

/-- A partition of the vertex set of `G` into vertex-disjoint induced trees `T_1, …, T_t`
(Lemma 5, p.9). -/
structure TreePartition (G : SimpleGraph V) where
  /-- The number `t` of parts. -/
  t : ℕ
  /-- The vertex set of the part `T_i`. -/
  part : Fin t → Finset V
  /-- The parts are pairwise disjoint. -/
  disjoint : ∀ i j : Fin t, i ≠ j → Disjoint (↑(part i) : Set V) (↑(part j) : Set V)
  /-- The parts cover all vertices. -/
  cover : ∀ v : V, ∃ i : Fin t, v ∈ part i
  /-- Each part induces a tree of `G`. -/
  isTree : ∀ i : Fin t, (G.induce (↑(part i) : Set V)).IsTree

variable [Fintype V] [DecidableEq V]

/-- **Lemma 5** (Parekh, arXiv:2509.19966v2, Lemma 5, p.9). For every constant `c > 0` there is a
bound `C` such that: if `G` is connected with girth `g ≥ c·m` (`m` the number of edges), then the
vertices of `G` have a partition into vertex-disjoint induced trees `T_1, …, T_t` with
`t ≤ C` and at most one `G`-edge between any two distinct parts.

**Lean gap (substantive).** The statement is faithful; the proof is not formalised. Required
ingredients:
* existence of a spanning tree (`SimpleGraph.exists_spanningTree` / `SimpleGraph.Connected`),
  its depth, and the cut-off construction of the paper (an iterative subtree-removal argument);
* `IsTree.card_edgeFinset` to count `≥ d` edges in each truncated tree and derive `t ≤ m/d + 1`;
* the cycle-length contradiction `4d + 2 < g`, built from two inter-part edges plus tree paths,
  using `SimpleGraph.Walk` concatenation and `SimpleGraph.girth_le_length`.
These are combinatorial but substantial; no external paper result is missing.

Recorded as a `def : Prop` (no proof, no placeholder) so that Theorem 3 can cite it as an explicit
hypothesis in a restricted statement.

**Candidate reusable dependencies.** `SimpleGraph.Connected.exists_spanningTree` (or
`SimpleGraph.exists_isTree_le`), `SimpleGraph.IsTree.card_edgeFinset`, `SimpleGraph.Walk.append`
/ `SimpleGraph.Walk.length_append`, `SimpleGraph.girth_le_length`,
`SimpleGraph.mem_edgeSet`, `Nat.dist_le_dist`, plus `Finset`/`Set` partition bookkeeping
(`Set.Subsingleton`, `Disjoint`).

**Suggested takeover tactics.** Build `T` with `exists_spanningTree`, root it at a vertex, and
induct on the height of `T` with `Nat.strong_induction_on`, cutting subtrees of depth
`d = (g - 3) / 4` (use `Nat.div_mul_le_self` and `omega` for `4d + 2 < g`); instantiate
`C = ⌈m / d⌉ + 1` from the edge count `d ≤ |E(T_i)|`, then contradict `g ≥ c·m` with
`Nat.div_mul_le_self`/`le_of_mul_le_mul_left`; for (ii) read off a cycle from two inter-part
edges by concatenating the two tree paths and apply `girth_le_length`. -/
def lemma5_tree_partition (c : ℝ) (_hc : 0 < c) : Prop :=
  ∃ C : ℕ, ∀ (V : Type) [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj],
    G.Connected → c * (numEdges G : ℝ) ≤ (G.girth : ℝ) →
    ∃ P : TreePartition G,
      P.t ≤ C ∧ ∀ i j : Fin P.t, i ≠ j →
        (EdgesBetween G (↑(P.part i) : Set V) (↑(P.part j) : Set V)).Subsingleton

end Lemma5

end Qatlib.Papers.DQIAdvantage25.MainResults
