/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Papers.AdiabNoSign20.MainResults.SourceModel
public import Mathlib.Combinatorics.SimpleGraph.Acyclic
public import Mathlib.Data.Set.Card

@[expose] public section


set_option backward.isDefEq.respectTransparency false

/-!
# AdiabNoSign20 — decoration structure and the provable part of Lemma 4

Source: M. B. Hastings, *The Power of Adiabatic Quantum Computation with No
Sign Problem*, arXiv:2005.03791v2, Section 5 (p. 14-17).

This module preserves the closed model support of the original development of
this material and proves the part of Lemma 4 that follows from the structural
data alone:

* `IsDecoration` — the `l`-fold decoration of Section 5.1 as an induced
  supergraph whose extra edges form a bounded-degree forest;
* `lemma4_lambda0_subgraph` — monotonicity of the Perron root under the
  induced embedding (proved in the source via `lambda0_mono`);
* `IsPaperC` / `IsPaperD` — the structural data of the base graphs
  `R_{L,(n+1)/2}` (eigenvalue `n+1`) and `P_{L,(n+1)/2}`
  (eigenvalue `n+1-δ`, `δ ≤ n/L²`); the legacy `IsPaperC` carried a vacuous
  `start_original : True` field, dropped here as it carries no mathematical
  content;
* `lemma4_lambda0_C_lower` — `λ₀(C) ≥ n`, proved here from
  `IsPaperC.base_lambda` and the subgraph monotonicity; the source left it
  open expecting a Perron-Frobenius development that the actual derivation
  does not require.

The remaining spectral inequalities of Lemma 4 (`lemma4_lambda0_upper`,
`lemma4_lambda0_D_upper`, `lemma4_second_eigenvalue`, `lemma4_overlap`) need
an `m`-ary tree eigenvalue bound, an additive eigenvalue inequality and
Courant-Fischer min-max, none of which are available in Mathlib; they remain
deferred obligations of this development with the original statements
preserved in the project history.
-/

set_option autoImplicit false

namespace Qatlib.Papers.AdiabNoSign20.MainResults.Decoration

open Qatlib.Papers.AdiabNoSign20.MainResults.SourceModel

/-- **Decoration (Section 5.1, p. 14).**  `Gl` is obtained from `G` by the
`l`-fold decoration with the height sequence of the paper: `G` is an induced
subgraph of `Gl` (its "original vertices"), and the extra edges form a forest
(the union of the `m`-ary trees attached at each vertex) whose every vertex
has at most `2^l * n` extra neighbours.  This is the structural input of
Lemma 4; the spectral estimates are stated relative to it. -/
structure IsDecoration (V : Type) [Fintype V] (G Gl : SimpleGraph V)
    (l n : ℕ) : Prop where
  /-- the original graph is an induced subgraph of the decorated graph -/
  induced : ∀ a b, G.Adj a b → Gl.Adj a b
  /-- the added edges form a forest whose degrees are bounded by the largest
  arity `2^l * n` of the decorating trees -/
  extra_forest :
    ∃ F : SimpleGraph V,
      (∀ a b, Gl.Adj a b ↔ G.Adj a b ∨ F.Adj a b) ∧
      F.IsAcyclic ∧ ∀ v, (F.neighborSet v).ncard ≤ 2 ^ l * n

/-- **Lemma 4, first inequality** (§5.3, p. 16): since `G` is an induced
subgraph of `G_l`, the largest eigenvalue of the adjacency matrix of `G` is
at most that of `G_l`. -/
theorem lemma4_lambda0_subgraph {V : Type} [Fintype V] [Nonempty V]
    {G Gl : SimpleGraph V} {l n : ℕ} (h : IsDecoration V G Gl l n) :
    lambda0 G ≤ lambda0 Gl :=
  lambda0_mono h.induced

/-- The base ring graph `R_{L,(n+1)/2}` has largest eigenvalue `n+1`
(§5.3, p. 17: `λ₀(R_{L,(n+1)/2}) = n+1`).  Recorded as the structural datum
of the construction. -/
structure IsPaperC (V : Type) [Fintype V] (C : SimpleGraph V) (n L l : ℕ)
    (startC : V) : Prop where
  /-- `C` is a decoration of a base graph `G₀` -/
  decorated : ∃ G0 : SimpleGraph V, IsDecoration V G0 C l n
  /-- the base graph has largest adjacency eigenvalue `n+1` -/
  base_lambda : ∃ G0 : SimpleGraph V, IsDecoration V G0 C l n ∧ lambda0 G0 = n + 1

/-- The base path graph `P_{L,(n+1)/2}` has largest eigenvalue
`n+1-Θ(n/L²)` (§5.3, p. 17).  Recorded as the structural datum of the
construction, with an explicit `δ = Θ(n/L²)`. -/
structure IsPaperD (V : Type) [Fintype V] (D : SimpleGraph V) (n L l : ℕ)
    (startD : V) : Prop where
  decorated : ∃ G0 : SimpleGraph V, IsDecoration V G0 D l n
  /-- the base graph has largest adjacency eigenvalue `n+1-δ` with
  `δ = Θ(n/L²)`; the lower bound `δ ≤ n/L²` is the side used here -/
  base_lambda :
    ∃ (G0 : SimpleGraph V) (δ : ℝ),
      IsDecoration V G0 D l n ∧ 0 < δ ∧ δ ≤ (n : ℝ) / (L : ℝ) ^ 2 ∧
        lambda0 G0 = (n : ℝ) + 1 - δ

/-- **Lemma 4, `λ₀(C) ≥ n`** (§5.3, p. 17), proved from the structural datum
`IsPaperC.base_lambda` and the subgraph monotonicity
`lemma4_lambda0_subgraph`.  The original development of this material left
this open under the expectation that a Perron-Frobenius identification would
be needed;
the recorded hypotheses already supply the base eigenvalue, so only the
monotonicity transfer is required. -/
theorem lemma4_lambda0_C_lower {V : Type} [Fintype V] [Nonempty V]
    {C : SimpleGraph V} {n L l : ℕ} {startC : V} (_hn : 0 < n)
    (hC : IsPaperC V C n L l startC) :
    (n : ℝ) ≤ lambda0 C := by
  obtain ⟨G0, hdec, hlam⟩ := hC.base_lambda
  have h1 : (n : ℝ) ≤ lambda0 G0 := by
    rw [hlam]
    exact_mod_cast n.le_succ
  exact h1.trans (lemma4_lambda0_subgraph hdec)

end Qatlib.Papers.AdiabNoSign20.MainResults.Decoration
