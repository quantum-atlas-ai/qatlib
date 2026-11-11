/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.GramQueryCore.LowerBoundTools.ResidualModels
import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Combinatorics.SimpleGraph.DeleteEdges
import Mathlib.Combinatorics.SimpleGraph.Acyclic
import Mathlib.Combinatorics.SimpleGraph.VertexCover
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
import Mathlib.Combinatorics.SimpleGraph.Walk.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Order.Filter.Basic
import Mathlib.Data.Sym.Sym2

set_option backward.isDefEq.respectTransparency false

/-!
# Graph, property and query-complexity model for arXiv:1011.1443v2

Childs–Kothari, *Quantum query complexity of minor-closed graph properties*,
arXiv:1011.1443v2 (19 May 2011), fixed for this paper block.

This module fixes the paper's conventions (Section 2, pp. 4–5):

* a **graph property** is an isomorphism-invariant predicate on labelled graphs,
  represented here as a family over labelled vertex types;
* **subgraph**, **minor** and **topological-minor** containment, following the
  Section 2 definitions (edge/isolated-vertex deletion, edge contraction, and
  elementary subdivision respectively);
* the closure hypotheses *subgraph closed*, *minor closed*, *topologically minor
  closed*;
* **sparsity** (Section 2, p. 5), the **forbidden subgraph property** (FSP), and
  **nontriviality**;
* the graph invariant `β` of Section 3.3 (internal edges, p. 10);
* the edge-splitting operation of Lemma 3.1 (p. 6);
* the bounded-error quantum query complexity `Qc` via the repository's actual
  source query model (`sourceFunctionQ`), together with the deterministic and
  randomized decision-tree complexities `Dc`, `Rc` used in Theorem 3.3.

Everything here is definitional: the paper-layer results live in the sibling
`Source*` modules.
-/

set_option autoImplicit false
noncomputable section
open Qatlib.Concepts.GramQueryCore.LowerBoundTools
open Filter

namespace Qatlib.Papers.MinorClosed10.MainResults

/-! ## Graph properties -/

/-- A **graph property** in the sense of the paper (Section 2, p. 4): a family
assigning to each labelled vertex type a predicate on graphs.  Graph properties in
the paper are independent of labelling; we take labelled predicates here, which is
the standard labelled representative of an isomorphism-invariant property. -/
abbrev GraphProperty : Type 1 :=
  (V : Type) → [Fintype V] → [DecidableEq V] → SimpleGraph V → Prop

/-! ## Containment relations (Section 2, pp. 4–5) -/

/-- `H ≤S G` (subgraph, Section 2, p. 4): `H` is obtained from `G` by deleting
edges and isolated vertices.  Equivalently, an injective edge-preserving map
`V(H) → V(G)` (isolated vertices of `H` may be dropped, so we only require the
edge-preserving injection). -/
def ContainsSubgraph {V W : Type} (H : SimpleGraph V) (G : SimpleGraph W) : Prop :=
  ∃ e : V ↪ W, ∀ ⦃a b⦄, H.Adj a b → G.Adj (e a) (e b)

/-- A **minor model** of `H` in `G` (Section 2, p. 4): a partition of `V(G)` into
nonempty connected branch sets `B_i` indexed by `i : Fin m`, such that every edge
`ij` of `H` is witnessed by an edge of `G` between `B_i` and `B_j`. -/
def ContainsMinor {V W : Type} (H : SimpleGraph V) (G : SimpleGraph W) : Prop :=
  ∃ f : W → V,
    (∀ i, ∃ v, f v = i) ∧
    (∀ i, ∀ v w, f v = i → f w = i → G.Reachable v w) ∧
    (∀ ⦃i j⦄, H.Adj i j → ∃ v w, f v = i ∧ f w = j ∧ G.Adj v w)

/-- The **interior** of a walk: the vertices on its support other than its two
endpoints. -/
def WalkInterior {V : Type} {G : SimpleGraph V} {u v : V}
    (p : G.Walk u v) : Set V :=
  {x | x ∈ p.support ∧ x ≠ u ∧ x ≠ v}

/-- `H ≤T G` (topological minor, Section 2, p. 5): `G` is obtained from `H` by
adding edges, adding isolated vertices and performing elementary subdivisions.
Formalized by the standard equivalent path model: an injection of `V(H)` into
`V(G)` together with, for every edge `ab` of `H`, a walk in `G` between the two
images, such that the walk interiors avoid all images and are pairwise disjoint. -/
def ContainsTopologicalMinor {V W : Type}
    (H : SimpleGraph V) (G : SimpleGraph W) : Prop :=
  ∃ (φ : V ↪ W) (P : ∀ a b, H.Adj a b → G.Walk (φ a) (φ b)),
    (∀ a b (h : H.Adj a b) x, x ∈ WalkInterior (P a b h) → x ∉ Set.range φ) ∧
    (∀ a b (hab : H.Adj a b) c d (hcd : H.Adj c d) x,
      ¬ ((a = c ∧ b = d) ∨ (a = d ∧ b = c)) →
      x ∈ WalkInterior (P a b hab) → x ∈ WalkInterior (P c d hcd) → False)

/-! ## Closure hypotheses (Section 2, p. 5) -/

/-- **Subgraph closed**: every subgraph of a graph with the property also has it. -/
def SubgraphClosed (P : GraphProperty) : Prop :=
  ∀ (n : ℕ) (G H : SimpleGraph (Fin n)), P (Fin n) G → H ≤ G → P (Fin n) H

/-- **Minor closed**: every minor of a graph with the property also has it. -/
def MinorClosed (P : GraphProperty) : Prop :=
  ∀ (m n : ℕ) (H : SimpleGraph (Fin m)) (G : SimpleGraph (Fin n)),
    P (Fin n) G → ContainsMinor H G → P (Fin m) H

/-- **Closed under topological minors** (used in Lemma 3.1, p. 6). -/
def TopologicalMinorClosed (P : GraphProperty) : Prop :=
  ∀ (m n : ℕ) (H : SimpleGraph (Fin m)) (G : SimpleGraph (Fin n)),
    P (Fin n) G → ContainsTopologicalMinor H G → P (Fin m) H

/-! ## Nontrivial, sparse, FSP (Section 2, p. 5) -/

/-- **Nontrivial** (Section 2): for all sufficiently large `n` there are both an
`n`-vertex graph with the property and one without it. -/
def IsNontrivial (P : GraphProperty) : Prop :=
  ∀ᶠ n in atTop, (∃ G : SimpleGraph (Fin n), P (Fin n) G) ∧
    (∃ G : SimpleGraph (Fin n), ¬ P (Fin n) G)

/-- **Sparse** (Section 2, p. 5): there is a constant `c` with `|E(G)| ≤ c·|V(G)|`
for every graph `G` with the property. -/
def IsSparse (P : GraphProperty) : Prop := by
  classical
  exact ∃ c : ℝ, 0 < c ∧ ∀ (V : Type) [Fintype V] [DecidableEq V]
    (G : SimpleGraph V), P V G → ((G.edgeFinset.card : ℝ) ≤ c * (Fintype.card V : ℝ))

/-- A **forbidden subgraph property** (FSP, Section 2, p. 5): the property is
described by a finite set of forbidden subgraphs. -/
def IsFSP (P : GraphProperty) : Prop := by
  classical
  exact ∃ F : Finset (Sigma fun k : ℕ => SimpleGraph (Fin k)),
    ∀ (V : Type) [Fintype V] [DecidableEq V] (G : SimpleGraph V),
      P V G ↔ ∀ f ∈ F, ¬ ContainsSubgraph f.2 G

/-- The property of being a **forest** (Section 3.2): the graph is acyclic. -/
def IsForestProperty (n : ℕ) (G : SimpleGraph (Fin n)) : Prop := G.IsAcyclic

/-! ## The invariant `β`: internal edges (Section 3.3, p. 10) -/

/-- An edge `(u,v)` is **internal** (Section 3.3, p. 10) if it lies on a cycle or on
a path joining two vertices of degree `≥ 3`.  We read this off the edge-deleted
graph: the edge is on a cycle when its endpoints remain connected after deleting it,
and it is on a high-degree path when each of the two sides left by the deletion
still meets a vertex of degree `≥ 3`. -/
def IsInternalEdge {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (u v : V) : Prop := by
  classical
  exact
    G.Adj u v ∧
      ((G.deleteEdges {Sym2.mk u v}).Reachable u v ∨
        ((∃ a, (G.deleteEdges {Sym2.mk u v}).Reachable u a ∧ 3 ≤ G.degree a) ∧
         (∃ b, (G.deleteEdges {Sym2.mk u v}).Reachable v b ∧ 3 ≤ G.degree b)))

/-- `β(G)`: the number of internal edges (Section 3.3, p. 10). -/
def beta {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) : ℕ := by
  classical
  exact (G.edgeFinset.filter
    (fun e : Sym2 V => ∃ u : V, ∃ v : V, e = Sym2.mk u v ∧ IsInternalEdge G u v)).card

/-! ## The edge-splitting operation of Lemma 3.1 (p. 6) -/

/-- `twoPathSplitSum G u v n₁ n₂`: delete the edge `(u,v)` of `G` and attach two
disjoint dangling paths, one of `n₁` edges at `u` and one of `n₂` edges at `v`
(Lemma 3.1, p. 6).  Vertices: the old ones in the left `Fin k` summand, the new
path vertices in `Fin n₁` and `Fin n₂`. -/
def twoPathSplitSum {k : ℕ} (G : SimpleGraph (Fin k)) (u v : Fin k) (n₁ n₂ : ℕ) :
    SimpleGraph ((Fin k ⊕ Fin n₁) ⊕ Fin n₂) :=
  SimpleGraph.fromRel (fun a b =>
    match a, b with
    | .inl (.inl x), .inl (.inl y) =>
        G.Adj x y ∧ ¬ ((x = u ∧ y = v) ∨ (x = v ∧ y = u))
    | .inl (.inl x), .inl (.inr j) => x = u ∧ j.val = 0
    | .inl (.inr i), .inl (.inr j) => i.val + 1 = j.val
    | .inl (.inl x), .inr j => x = v ∧ j.val = 0
    | .inl (.inr _), .inr _ => False
    | .inr i, .inr j => i.val + 1 = j.val
    | _, _ => False)

/-- The hypothesis of Lemma 3.1 (p. 6): replacing the edge `(u,v)` of `G` by two
disjoint paths of any length, one connected at `u` and one at `v`, always results in
a graph possessing `P`. -/
def SplitsInto (P : GraphProperty) {k : ℕ} (G : SimpleGraph (Fin k)) (u v : Fin k) : Prop :=
  ∀ n₁ n₂ : ℕ, P ((Fin k ⊕ Fin n₁) ⊕ Fin n₂) (twoPathSplitSum G u v n₁ n₂)

/-! ## Decision-tree and query complexities (Section 2, p. 4) -/

/-- A **deterministic adjacency decision tree** on `n`-vertex graphs.  Each internal
node queries whether an ordered pair of vertices is an edge; each leaf outputs a
bit. -/
inductive DetTree (n : ℕ) where
  | leaf : Bool → DetTree n
  | query : Fin n × Fin n → DetTree n → DetTree n → DetTree n

namespace DetTree

/-- Evaluate a deterministic decision tree on a graph. -/
def eval {n : ℕ} (t : DetTree n) (G : SimpleGraph (Fin n)) : Bool := by
  classical
  exact
    match t with
    | .leaf b => b
    | .query e l r => if G.Adj e.1 e.2 then eval l G else eval r G
termination_by t

/-- The number of adjacency queries of a tree (its depth). -/
def depth {n : ℕ} : DetTree n → ℕ
  | .leaf _ => 0
  | .query _ l r => 1 + max (depth l) (depth r)

end DetTree

/-- `D(P)`: the **deterministic** query complexity of the `n`-vertex property `P`
(Section 2, p. 4), as the minimal depth of a deterministic adjacency decision tree
deciding `P`. -/
noncomputable def Dc (P : GraphProperty) (n : ℕ) : ℝ := by
  classical
  exact sInf {d : ℝ |
    ∃ t : DetTree n,
      (∀ G : SimpleGraph (Fin n), t.eval G = decide (P (Fin n) G)) ∧
      (t.depth : ℝ) ≤ d}

/-- `R(P)`: the **randomized** (two-sided bounded-error) query complexity of `P`
(Section 2, p. 4), as the minimal depth of a randomized decision tree that decides
`P` with success probability at least `2/3`, uniformly over inputs. -/
noncomputable def Rc (P : GraphProperty) (n : ℕ) : ℝ := by
  classical
  exact sInf {d : ℝ |
    ∃ (k : ℕ) (t : (Fin k → Bool) → DetTree n),
      (∀ G : SimpleGraph (Fin n),
        (((Finset.univ.filter (fun r : Fin k → Bool =>
            (t r).eval G = decide (P (Fin n) G))).card : ℝ) /
          (Fintype.card (Fin k → Bool) : ℝ)) ≥ (2 : ℝ) / 3) ∧
      (∀ r : Fin k → Bool, ((t r).depth : ℝ) ≤ d)}

/-- The adjacency-bit encoding of an `n`-vertex graph over the `n * n` ordered
vertex pairs; redundant on the two orientations but with the same query count. -/
def graphInput (n : ℕ) : SimpleGraph (Fin n) → Fin (n * n) → Fin 2 := by
  classical
  exact fun G i =>
    if G.Adj (finProdFinEquiv.symm i).1 (finProdFinEquiv.symm i).2 then (1 : Fin 2) else 0

/-- The property decision function `SimpleGraph (Fin n) → Bool`. -/
def propDecision (P : GraphProperty) (n : ℕ) : SimpleGraph (Fin n) → Bool := by
  classical
  exact fun G => decide (P (Fin n) G)

/-- `Q(P)`: the bounded-error **quantum** query complexity of the `n`-vertex
property `P` (Section 2, p. 4), realized through the repository's source query
model `sourceFunctionQ` on the adjacency-bit encoding of the graph. -/
def Qc (P : GraphProperty) (n : ℕ) : ℝ := by
  classical
  exact (sourceFunctionQ (graphInput n) (propDecision P n)).toReal

/-! ## Asymptotic helpers -/

/-- `f = O(g)`: `f` is eventually bounded by a constant multiple of `g`. -/
def IsBigO (f g : ℕ → ℝ) : Prop :=
  ∃ c : ℝ, 0 ≤ c ∧ ∀ᶠ n in atTop, f n ≤ c * g n

/-- `f = Ω(g)`: `f` is eventually at least a positive constant multiple of `g`. -/
def IsBigOmega (f g : ℕ → ℝ) : Prop :=
  ∃ c : ℝ, 0 < c ∧ ∀ᶠ n in atTop, c * g n ≤ f n

/-- `f = Θ(g)`. -/
def IsBigTheta (f g : ℕ → ℝ) : Prop := IsBigO f g ∧ IsBigOmega f g

/-- The power function `n ↦ n^a` on natural inputs, for real exponent `a`. -/
def npow (a : ℝ) : ℕ → ℝ := fun n => Real.rpow (n : ℝ) a

end Qatlib.Papers.MinorClosed10.MainResults
