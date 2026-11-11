/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.MinorClosed10.MainResults.Model.GraphAndQueryModel
import Mathlib.Combinatorics.SimpleGraph.Maps

set_option backward.isDefEq.respectTransparency false

/-!
# Paper-specific graph objects for arXiv:1011.1443v2

Concrete graphs and properties used by the statements of Childs–Kothari,
*Quantum query complexity of minor-closed graph properties* (arXiv:1011.1443v2):

* the `k`-path and the `{d₁,d₂,d₃}`-claw (Section 2, p. 5; Proposition 4.1, p. 18);
* the "many edges or contains `H`" properties of Theorems 4.4/4.5/4.7/4.9;
* the deletion of degree-one vertices of Theorem 4.5;
* the vertex cover number `vc(H)` (Section 4.3, p. 15).
-/

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.MinorClosed10.MainResults

/-- The **`k`-path** `P_{k+1}`: vertices `0, …, k` with edges between consecutive
vertices (Section 2, p. 5: "a `k`-path is a path with `k` edges"). -/
def PathGraph (k : ℕ) : SimpleGraph (Fin (k + 1)) :=
  SimpleGraph.fromRel (fun i j : Fin (k + 1) => i.val + 1 = j.val)

/-- `H` is a **`k`-path** (Section 2, p. 5) when it is isomorphic to `PathGraph k`. -/
def IsKPath {m : ℕ} (H : SimpleGraph (Fin m)) (k : ℕ) : Prop :=
  Nonempty (H ≃g PathGraph k)

/-- The property "the graph contains a copy of the `k`-path" (Section 4.3). -/
def ContainsKPathProperty (k : ℕ) : GraphProperty :=
  fun _ _ _ G => ContainsSubgraph (PathGraph k) G

/-- The **`{d₁,d₂,d₃}`-claw** (Section 2, p. 5): a subdivision of the claw `K_{1,3}`
whose three branches have `d₁`, `d₂`, `d₃` edges.  Vertex set: a centre `Unit`, and
for each branch `i : Fin 3` the `dᵢ` internal vertices `Fin (d i)`; branch `i` is the
path centre–`(i,0)`–`(i,1)`–…–`(i,dᵢ-1)`. -/
def ClawGraph (d1 d2 d3 : ℕ) :
    SimpleGraph (Unit ⊕ (Sigma fun i : Fin 3 => Fin (![d1, d2, d3] i))) :=
  SimpleGraph.fromRel (fun a b =>
    match a, b with
    | .inl _, .inr ⟨_, j⟩ => j.val = 0
    | .inr ⟨i, j⟩, .inr ⟨i', j'⟩ => i = i' ∧ j.val + 1 = j'.val
    | _, _ => False)

/-- `H` is a **`{d₁,d₂,d₃}`-claw** (Section 2, p. 5) when it is isomorphic to
`ClawGraph d₁ d₂ d₃`. -/
def IsDClaw {m : ℕ} (H : SimpleGraph (Fin m)) (d1 d2 d3 : ℕ) : Prop :=
  Nonempty (H ≃g ClawGraph d1 d2 d3)

/-- The property "the graph contains a copy of the `{d₁,d₂,d₃}`-claw"
(Corollary 4.4, p. 18). -/
def ContainsDClawProperty (d1 d2 d3 : ℕ) : GraphProperty :=
  fun _ _ _ G => ∃ (m : ℕ) (H : SimpleGraph (Fin m)),
    IsDClaw H d1 d2 d3 ∧ ContainsSubgraph H G

/-- The **vertex cover number** `vc(H)` (Section 4.3, p. 15): the size of a smallest
vertex cover of `H` (`SimpleGraph.vertexCoverNum`, valued in `ℕ∞`). -/
def vc {V : Type} [Fintype V] (H : SimpleGraph V) : ℕ∞ := by
  classical
  exact H.vertexCoverNum

/-- The property of Theorem 4.4/4.5: "the graph has more than `c·n` edges, or
contains the given subgraph `H`" (p. 16). -/
def DenseOrContains {m : ℕ} (c : ℝ) (H : SimpleGraph (Fin m)) : GraphProperty := by
  classical
  exact fun V _ _ G => c * (Fintype.card V : ℝ) < (G.edgeFinset.card : ℝ) ∨
    ContainsSubgraph H G

/-- The property of Theorem 4.7/4.9: "the `n`-vertex graph has more than `mbar n`
edges, or contains the given subgraph `H`" (p. 20). -/
def ManyOrContains {m : ℕ} (mbar : ℕ → ℝ) (H : SimpleGraph (Fin m)) : GraphProperty := by
  classical
  exact fun V _ _ G => mbar (Fintype.card V) < (G.edgeFinset.card : ℝ) ∨
    ContainsSubgraph H G

/-- `H'` is obtained from `H` by **deleting all degree-one vertices that are not part
of an isolated edge** (Theorem 4.5, p. 18): `H'` is the induced subgraph of `H` on a
vertex subset containing every vertex of degree `≠ 1` and omitting exactly the
degree-one vertices whose neighbour does not also have degree one. -/
def IsLeafDeletion {m m' : ℕ} (H : SimpleGraph (Fin m)) (H' : SimpleGraph (Fin m')) :
    Prop := by
  classical
  exact
    ∃ emb : Fin m' ↪ Fin m,
      (∀ a b, H'.Adj a b ↔ H.Adj (emb a) (emb b)) ∧
      (∀ x, x ∉ Set.range emb → H.degree x = 1) ∧
      (∀ x, H.degree x = 1 →
        (∀ y, H.Adj x y → H.degree y ≠ 1) → x ∉ Set.range emb)


/-- `P` is **described by a finite set of forbidden topological minors** (Corollary 2.1,
p. 5): there is a finite list `F` of graphs such that `G` has `P` iff it contains none
of them as a topological minor. -/
def DescribedByForbiddenTopologicalMinors (P : GraphProperty) : Prop := by
  classical
  exact ∃ F : Finset (Sigma fun k : ℕ => SimpleGraph (Fin k)),
    ∀ (V : Type) [Fintype V] [DecidableEq V] (G : SimpleGraph V),
      P V G ↔ ∀ f ∈ F, ¬ ContainsTopologicalMinor f.2 G

/-- `P` is **described by a finite set of forbidden minors** (Theorem 2.1). -/
def DescribedByForbiddenMinors (P : GraphProperty) : Prop := by
  classical
  exact ∃ F : Finset (Sigma fun k : ℕ => SimpleGraph (Fin k)),
    ∀ (V : Type) [Fintype V] [DecidableEq V] (G : SimpleGraph V),
      P V G ↔ ∀ f ∈ F, ¬ ContainsMinor f.2 G

/-- The **`N`-cycle** `C_N`: vertices `0, …, N-1` in a ring (Section 2, p. 5). -/
def CycleGraph (N : ℕ) : SimpleGraph (Fin N) :=
  SimpleGraph.fromRel (fun i j : Fin N => i.val + 1 = j.val ∨ (i.val = 0 ∧ j.val + 1 = N))

/-- `halfUp d = ⌈d/2⌉` for a natural number `d`. -/
def halfUp (d : ℕ) : ℕ := (d + 1) / 2

/-- `f = Õ(g)`: `f` is bounded by `g` up to polylogarithmic factors (Section 2, p. 5). -/
def IsSoftBigO (f bound : ℕ → ℝ) : Prop :=
  ∃ k : ℕ, IsBigO f (fun n => bound n * (Real.log ((n : ℝ) + 2)) ^ k)

/-- The hypothesis bundle of Lemma 3.1 (p. 6): `P` is closed under topological
minors, and there are `G ∉ P` and an edge `(u,v)` of `G` whose replacement by two
disjoint paths (at `u` and at `v`) always lands in `P`. -/
def Lemma31Hypothesis (P : GraphProperty) : Prop :=
  TopologicalMinorClosed P ∧
    ∃ (k : ℕ) (G : SimpleGraph (Fin k)) (u v : Fin k),
      ¬ P (Fin k) G ∧ G.Adj u v ∧ SplitsInto P G u v

end Qatlib.Papers.MinorClosed10.MainResults
