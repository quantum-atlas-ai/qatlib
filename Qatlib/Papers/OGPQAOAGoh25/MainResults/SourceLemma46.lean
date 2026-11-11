/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.OGPQAOAGoh25.MainResults.Model.SourceModel

set_option backward.isDefEq.respectTransparency false

/-!
# Lemma 4.6 — adding edges preserves tree-likeness of most neighbourhoods

Fixed source: arXiv:2404.06087v6, Lemma 4.6 (p. 14, lines 765–768).

> Fix any `λ`. There exists some `ε > 0` such that for `l ≤ ε log n`, with high
> probability as `n → ∞`, adding edges preserves trees in a `1 - o(1)` fraction
> of the `l`-local neighbourhoods.

In the model of `Model.SourceModel`, an edge-addition step is an arbitrary map
`addEdges n : Instance n q → Instance n q` (the paper's operation of adding a
matching of edges to reach the target degree). A vertex is *broken* when its
radius-`l` ball was treelike before the addition but is not afterwards. The
paper's estimate (which uses `ε < 1/log λ'`) says that, with probability tending
to one, at most a `δ`-fraction of vertices is broken; the counting lemma below
turns this into the `1 - o(1)` statement.
-/

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.OGPQAOAGoh25.MainResults

open Filter Topology
open Qatlib.Papers.OGPQAOAGoh25.MainResults.Model
open Qatlib.Concepts.MonteCarloMean.FinDistBounds

variable {n q : ℕ}

namespace Model

/-- Vertices whose radius-`l` neighbourhood was treelike before an edge addition
but is no longer treelike after it. -/
def Instance.breaksTreeCount (I I' : Instance n q) (l : ℕ) : ℕ :=
  (Finset.univ.filter (fun v => I.IsTreelike v l ∧ ¬ I'.IsTreelike v l)).card

/-- Vertices for which the edge addition does not break tree-likeness. -/
def Instance.preservedCount (I I' : Instance n q) (l : ℕ) : ℕ :=
  (Finset.univ.filter (fun v => ¬ (I.IsTreelike v l ∧ ¬ I'.IsTreelike v l))).card

/-- The fraction of vertices whose tree-likeness is preserved by an edge
addition. -/
def Instance.preservedFraction (I I' : Instance n q) (l : ℕ) : ℝ :=
  (I.preservedCount I' l : ℝ) / (n : ℝ)

/-- Counting reduction: if at most a `δ`-fraction of vertices is broken by the
edge addition, at least a `1 - δ` fraction is preserved. -/
theorem Instance.preservedFraction_ge (I I' : Instance n q) (l : ℕ) (hn : 0 < n) {δ : ℝ}
    (h : (I.breaksTreeCount I' l : ℝ) ≤ δ * (n : ℝ)) :
    1 - δ ≤ I.preservedFraction I' l := by
  unfold preservedFraction
  refine fraction_ge_of_bad_le _ _ hn ?_ h
  unfold breaksTreeCount preservedCount
  have hsum := Finset.card_filter_add_card_filter_not
    (s := (Finset.univ : Finset (Fin n)))
    (p := fun v => I.IsTreelike v l ∧ ¬ I'.IsTreelike v l)
  have hsum' : (Finset.univ.filter
        (fun v => I.IsTreelike v l ∧ ¬ I'.IsTreelike v l)).card +
      (Finset.univ.filter
        (fun v => ¬ (I.IsTreelike v l ∧ ¬ I'.IsTreelike v l))).card = n := by
    simpa using hsum
  omega

end Model

/-- **Lemma 4.6** (arXiv:2404.06087v6, p. 14, lines 765–768).

There is `ε > 0` (the paper's `ε < 1/log λ'`) such that for every schedule
`l n ≤ ε log n`, if the paper's estimate holds — with probability tending to
one at most a `δ`-fraction of vertices is broken by the edge addition — then
with probability tending to one at least a `1 - δ` fraction of the `l n`-local
neighbourhoods remains treelike after adding edges. -/
theorem lemma46
    {q : ℕ} (hq : 2 ≤ q)
    (μ : ∀ n : ℕ, FinDist (Instance n q))
    (addEdges : ∀ n : ℕ, Instance n q → Instance n q)
    (l : ℕ → ℕ) (ε : ℝ) (hε : 0 < ε)
    (hl : ∀ᶠ n : ℕ in atTop, (l n : ℝ) ≤ ε * Real.log n)
    (hbreaks : ∀ δ : ℝ, 0 < δ → ∀ᶠ n : ℕ in atTop,
      1 - δ ≤ mass (μ n) (fun I =>
        (I.breaksTreeCount (addEdges n I) (l n) : ℝ) ≤ δ * (n : ℝ))) :
    ∃ ε' : ℝ, 0 < ε' ∧ ∀ δ : ℝ, 0 < δ → ∀ᶠ n : ℕ in atTop,
      1 - δ ≤ mass (μ n) (fun I =>
        1 - δ ≤ I.preservedFraction (addEdges n I) (l n)) := by
  refine ⟨ε, hε, ?_⟩
  intro δ hδ
  filter_upwards [hbreaks δ hδ, eventually_ge_atTop 1] with n hb hn
  have hn0 : 0 < n := lt_of_lt_of_le zero_lt_one hn
  refine le_trans hb (mass_mono (μ n) ?_)
  intro I hI
  exact I.preservedFraction_ge (addEdges n I) (l n) hn0 hI

end Qatlib.Papers.OGPQAOAGoh25.MainResults
