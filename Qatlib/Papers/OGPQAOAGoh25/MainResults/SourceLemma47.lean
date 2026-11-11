/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.OGPQAOAGoh25.MainResults.Model.SourceModel

set_option backward.isDefEq.respectTransparency false

/-!
# Lemma 4.7 — tree-likeness of most local neighbourhoods in the regular graph

Fixed source: arXiv:2404.06087v6, Lemma 4.7 and eqs. (32)–(34)
(p. 14, lines 782–784).

> Fix any `λ > 1` and `p ≤ ε log n` for some `ε > 0`. With high probability as
> `n → ∞`, a `1 - o_λ(1)` fraction of vertices in the `p`-local neighbourhood
> are treelike.

The proof is the regular-graph analogue of Lemma 4.5: the cycle count and the
degree tail are controlled with `ε < 1/log((q-1)λ)` (eqs. (32)–(34)). In the
finite model, `IsRegularLaw` records the `R^q(n, d)` ensemble and
`treelikeFraction` the fraction of vertices with a tree-like radius-`p` ball;
this file reduces the statement to the paper's cycle-count estimate `hbad`.
-/

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.OGPQAOAGoh25.MainResults

open Filter Topology
open Qatlib.Papers.OGPQAOAGoh25.MainResults.Model
open Qatlib.Concepts.MonteCarloMean.FinDistBounds

/-- **Lemma 4.7** (arXiv:2404.06087v6, p. 14, lines 782–784).

For `λ > 1`, a law `μ n` supported on `D`-regular hypergraphs, and a depth
schedule `p n ≤ ε log n`: if with probability tending to one at most a
`δ`-fraction of vertices have a non-treelike radius-`p n` neighbourhood (the
cycle-count estimate of eqs. (32)–(34)), then with probability tending to one at
least a `1 - δ` fraction of the `p n`-local neighbourhoods are treelike. -/
theorem lemma47
    {q : ℕ} (hq : 2 ≤ q)
    (lam : ℝ) (hlam : 1 < lam) (D : ℕ)
    (μ : ∀ n : ℕ, FinDist (Instance n q))
    (hRegLaw : ∀ n : ℕ, IsRegularLaw (μ n) D)
    (p : ℕ → ℕ) (ε : ℝ) (hε : 0 < ε)
    (hp : ∀ᶠ n : ℕ in atTop, (p n : ℝ) ≤ ε * Real.log n)
    (hbad : ∀ δ : ℝ, 0 < δ → ∀ᶠ n : ℕ in atTop,
      1 - δ ≤ mass (μ n) (fun I => (I.badCount (p n) : ℝ) ≤ δ * (n : ℝ))) :
    ∀ δ : ℝ, 0 < δ → ∀ᶠ n : ℕ in atTop,
      1 - δ ≤ mass (μ n) (fun I => 1 - δ ≤ I.treelikeFraction (p n)) := by
  intro δ hδ
  filter_upwards [hbad δ hδ, eventually_ge_atTop 1] with n hb hn
  have hn0 : 0 < n := lt_of_lt_of_le zero_lt_one hn
  refine le_trans hb (mass_mono (μ n) ?_)
  intro I hI
  exact I.treelikeFraction_ge (p n) hn0 hI

end Qatlib.Papers.OGPQAOAGoh25.MainResults
