/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Data.Finset.Powerset
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic

set_option backward.isDefEq.respectTransparency false

/-!
# Source model for TriangleFind14

François Le Gall, *Improved Quantum Algorithm for Triangle Finding via
Combinatorial Arguments*, fixed version arXiv:1407.0085v2 (8 Sep 2014).

This module fixes the combinatorial vocabulary of Section 4 of the paper:

* `edgeSetIn G Y` is `E(Y)`, the edge set of `Y`;
* `coveredByX G X e` says that the unordered pair `e` lies in `E(N_G(x))` for
  some `x ∈ X`, i.e. that both endpoints of `e` are neighbours of `x`;
* `deltaSet G X Y` is `Δ_G(X,Y) = E(Y) \ ⋃_{x∈X} E(N_G(x))`;
* `deltaSetW G X Y w` is `Δ_G(X,Y,w) = {e ∈ Δ_G(X,Y) | e ⊆ N_G(w)}`;
* `KGood G X k` is Definition 4.1: `∑_{w∈V} |Δ_G(X,Y,w)| ≤ |Y|² n^{1-k}` for
  every `Y ⊆ V`.

Edges are represented by two-element `Finset V`, which keeps the cardinality
arguments of Lemma 4.3 purely finitary.  The probabilistic notation of the
paper is represented by uniform finite probability (`uniformProb`, `subsetProb`).

The module is the shared source model; it introduces no axioms and no `sorry`.
-/

set_option autoImplicit false
noncomputable section

open scoped Classical BigOperators

namespace Qatlib.Papers.TriangleFind14.MainResults

variable {V : Type*}

/-- A three-element vertex set spans a triangle when its three vertices are
pairwise adjacent.  (arXiv:1407.0085v2, Section 4: "G is undirected and
unweighted" and a triangle is a set of three pairwise adjacent vertices.) -/
def IsTriangle (G : SimpleGraph V) (t : Finset V) : Prop :=
  t.card = 3 ∧ ∀ u ∈ t, ∀ v ∈ t, u ≠ v → G.Adj u v

/-- The graph contains at least one triangle. -/
def HasTriangle (G : SimpleGraph V) : Prop :=
  ∃ t : Finset V, IsTriangle G t

/-- `E(Y)`: the set of edges of `G` whose two endpoints lie in `Y`.
Edges are unordered pairs represented as two-element finsets. -/
def edgeSetIn (G : SimpleGraph V) (Y : Finset V) : Finset (Finset V) :=
  letI := Classical.decRel G.Adj
  (Y.powersetCard 2).filter (fun e => ∃ u ∈ e, ∃ v ∈ e, u ≠ v ∧ G.Adj u v)

/-- The unordered pair `e` is contained in `E(N_G(x))` for some `x ∈ X`:
both endpoints of `e` are neighbours of `x`.  This is the set
`⋃_{x∈X} E(N_G(x))` removed in the definition of `Δ_G(X,Y)`. -/
def coveredByX (G : SimpleGraph V) (X : Finset V) (e : Finset V) : Prop :=
  letI := Classical.decRel G.Adj
  ∃ x ∈ X, ∃ u ∈ e, ∃ v ∈ e, u ≠ v ∧ G.Adj x u ∧ G.Adj x v

/-- `Δ_G(X,Y) = E(Y) \ ⋃_{x∈X} E(N_G(x))` (arXiv:1407.0085v2, Section 4,
displayed formula before Definition 4.1). -/
def deltaSet (G : SimpleGraph V) (X Y : Finset V) : Finset (Finset V) :=
  letI := Classical.decRel G.Adj
  (edgeSetIn G Y).filter (fun e => ¬ coveredByX G X e)

/-- `Δ_G(X,Y,w) = {e ∈ Δ_G(X,Y) | e ⊆ N_G(w)}`, the version restricted to
edges whose two endpoints are both adjacent to `w`
(arXiv:1407.0085v2, Section 4, displayed formula before Definition 4.1). -/
def deltaSetW (G : SimpleGraph V) (X Y : Finset V) (w : V) : Finset (Finset V) :=
  letI := Classical.decRel G.Adj
  (edgeSetIn G (Y.filter (fun v => G.Adj v w))).filter (fun e => ¬ coveredByX G X e)

/-- An edge `e` of `G` is an edge of a triangle: there is a vertex `w` adjacent
to both endpoints. -/
def EdgeInTriangle (G : SimpleGraph V) (e : Finset V) : Prop :=
  letI := Classical.decRel G.Adj
  e.card = 2 ∧ ∃ w : V, ∃ u ∈ e, ∃ v ∈ e, u ≠ v ∧ G.Adj u v ∧ G.Adj u w ∧ G.Adj v w

/-- `Δ_G(X,A)` contains an edge of a triangle of `G`
(arXiv:1407.0085v2, Proposition 4.1, printed p. 9). -/
def ContainsTriangleEdge (G : SimpleGraph V) (X A : Finset V) : Prop :=
  letI := Classical.decRel G.Adj
  ∃ e ∈ deltaSet G X A, EdgeInTriangle G e

/-- Definition 4.1 (arXiv:1407.0085v2, printed p. 8): a set `X ⊆ V` is
`k`-good for `G` when `∑_{w∈V} |Δ_G(X,Y,w)| ≤ |Y|² n^{1-k}` for every
`Y ⊆ V`, where `n = |V|`. -/
def KGood [Fintype V] (G : SimpleGraph V) (X : Finset V) (k : ℝ) : Prop :=
  ∀ Y : Finset V,
    (∑ w : V, ((deltaSetW G X Y w).card : ℝ)) ≤
      (Y.card : ℝ) ^ 2 * Real.rpow (Fintype.card V : ℝ) (1 - k)

/-- Uniform probability of a predicate on a finite type. -/
def uniformProb {α : Type*} [Fintype α] (p : α → Prop) : ℝ :=
  letI := Classical.decPred p
  ((Finset.univ.filter p).card : ℝ) / (Fintype.card α : ℝ)

/-- Uniform probability over the `r`-element subsets of `A`
(the space `S(A,r)` of the paper). -/
def subsetProb {V : Type*} [DecidableEq V] (A : Finset V) (r : ℕ)
    (p : Finset V → Prop) : ℝ :=
  letI := Classical.decPred p
  (((A.powersetCard r).filter p).card : ℝ) / ((A.powersetCard r).card : ℝ)

/-- Membership in `E(Y)` unfolds to a two-element subset of `Y` whose two
vertices are adjacent. -/
lemma mem_edgeSetIn {G : SimpleGraph V} {Y : Finset V} {e : Finset V}
    (he : e ∈ edgeSetIn G Y) :
    e ⊆ Y ∧ e.card = 2 ∧ ∃ u ∈ e, ∃ v ∈ e, u ≠ v ∧ G.Adj u v := by
  unfold edgeSetIn at he
  rw [Finset.mem_filter, Finset.mem_powersetCard] at he
  exact ⟨he.1.1, he.1.2, he.2⟩

/-- `Δ_G(X,Y,w) ⊆ Δ_G(X,Y)`: restricting to `Y ∩ N_G(w)` gives a subset. -/
lemma deltaSetW_subset_deltaSet (G : SimpleGraph V) (X Y : Finset V) (w : V) :
    deltaSetW G X Y w ⊆ deltaSet G X Y := by
  intro e he
  unfold deltaSetW at he
  unfold deltaSet
  rw [Finset.mem_filter] at he ⊢
  refine ⟨?_, he.2⟩
  unfold edgeSetIn at he ⊢
  rw [Finset.mem_filter, Finset.mem_powersetCard] at he ⊢
  exact ⟨⟨he.1.1.1.trans (Finset.filter_subset _ _), he.1.1.2⟩, he.1.2⟩

/-- The set `Δ_G(X,Y,w)` is a subset of `Δ_G(X,Y)`; consequently its cardinality
is bounded by the cardinality of `Δ_G(X,Y)`. -/
lemma deltaSetW_card_le_deltaSet_card (G : SimpleGraph V) (X Y : Finset V) (w : V) :
    (deltaSetW G X Y w).card ≤ (deltaSet G X Y).card :=
  Finset.card_le_card (deltaSetW_subset_deltaSet G X Y w)

/-- Membership in `Δ_G(X,Y,w)` exhibits `e` as a two-element subset of `Y`
(both endpoints adjacent to `w`, not covered by `X`). -/
lemma mem_deltaSetW_subset {G : SimpleGraph V} {X Y : Finset V} {w : V} {e : Finset V}
    (he : e ∈ deltaSetW G X Y w) : e ⊆ Y := by
  unfold deltaSetW at he
  rw [Finset.mem_filter] at he
  exact ((mem_edgeSetIn he.1).1).trans (Finset.filter_subset _ _)

/-- Monotonicity in the vertex-set argument: `B ⊆ A` implies
`Δ_G(X,B,w) ⊆ Δ_G(X,A,w)`. -/
lemma deltaSetW_mono (G : SimpleGraph V) (X B A : Finset V) (w : V) (h : B ⊆ A) :
    deltaSetW G X B w ⊆ deltaSetW G X A w := by
  have hBF : B.filter (fun v => G.Adj v w) ⊆ A.filter (fun v => G.Adj v w) := by
    intro x hx
    exact Finset.mem_filter.2 ⟨h (Finset.mem_filter.1 hx).1, (Finset.mem_filter.1 hx).2⟩
  intro e he
  unfold deltaSetW at he ⊢
  rw [Finset.mem_filter] at he ⊢
  refine ⟨?_, he.2⟩
  unfold edgeSetIn at he ⊢
  rw [Finset.mem_filter] at he ⊢
  exact ⟨Finset.powersetCard_mono hBF he.1.1, he.1.2⟩

/-- Finite union bound for `uniformProb`: if every sample satisfying `bad`
satisfies `∃ i ∈ t, viol i s`, then the `bad`-probability is at most the sum of
the `viol i`-probabilities. -/
lemma uniformProb_union_bound {α : Type*} [Fintype α] [Nonempty α]
    {ι : Type*} [Fintype ι] (t : Finset ι)
    (bad : α → Prop) (viol : ι → α → Prop)
    (hcover : ∀ s : α, bad s → ∃ i ∈ t, viol i s) :
    uniformProb bad ≤ ∑ i ∈ t, uniformProb (viol i) := by
  classical
  have hpos : (0 : ℝ) < (Fintype.card α : ℝ) := by
    exact_mod_cast Fintype.card_pos_iff.mpr ‹Nonempty α›
  unfold uniformProb
  have hsub : (Finset.univ.filter bad) ⊆
      t.biUnion (fun i => Finset.univ.filter (viol i)) := by
    intro s hs
    rw [Finset.mem_filter] at hs
    obtain ⟨i, hi, hvi⟩ := hcover s hs.2
    exact Finset.mem_biUnion.mpr ⟨i, hi,
      Finset.mem_filter.mpr ⟨Finset.mem_univ s, hvi⟩⟩
  have h12 : (Finset.univ.filter bad).card
      ≤ ∑ i ∈ t, (Finset.univ.filter (viol i)).card :=
    Nat.le_trans (Finset.card_le_card hsub) Finset.card_biUnion_le
  rw [← Finset.sum_div, div_le_div_iff₀ hpos hpos]
  exact mul_le_mul_of_nonneg_right (by exact_mod_cast h12) hpos.le

/-- Complement law for `uniformProb` on a nonempty space. -/
lemma uniformProb_compl {α : Type*} [Fintype α] [Nonempty α] (p : α → Prop) :
    uniformProb p + uniformProb (fun s => ¬ p s) = 1 := by
  letI := Classical.decPred p
  letI := Classical.decPred (fun s => ¬ p s)
  have hpos : (0 : ℝ) < (Fintype.card α : ℝ) := by
    exact_mod_cast Fintype.card_pos_iff.mpr ‹Nonempty α›
  have h1 : (Finset.univ.filter p).card
      + (Finset.univ.filter (fun s => ¬ p s)).card = Fintype.card α := by
    have h := Finset.card_filter_add_card_filter_not p (s := Finset.univ)
    rw [Finset.card_univ] at h
    exact h
  unfold uniformProb
  rw [← add_div, div_eq_iff hpos.ne', one_mul]
  exact_mod_cast h1

end Qatlib.Papers.TriangleFind14.MainResults
