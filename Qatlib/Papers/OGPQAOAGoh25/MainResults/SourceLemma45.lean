/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.OGPQAOAGoh25.MainResults.Model.SourceModel

set_option backward.isDefEq.respectTransparency false

/-!
# Lemma 4.5 — most local neighbourhoods of the Erdős–Rényi graph are treelike

Fixed source: arXiv:2404.06087v6, Lemma 4.5 and eqs. (28)–(31)
(p. 14, lines 717–719).

> Fix any constant `λ` and `l ≤ ε log n`. With high probability as `n → ∞`,
> a `1 - o(1)` fraction of the `l`-local neighbourhoods are treelike.

The paper's proof counts `k`-cycles, applies a Markov bound to the number of
cycles in the `l`-neighbourhood and a Poisson tail bound for the degrees; both
are concentration statements about the cycle/path count. In the finite model of
`Model.SourceModel`, `treelikeFraction` measures the fraction of vertices whose
radius-`l` ball satisfies the tree Euler characteristic. This file reduces the
`1 - o(1)` treelike statement to the paper's cycle-count estimate `hbad`
(at most a `δ`-fraction of vertices are non-treelike, with probability tending
to one), using the counting lemma `fraction_ge_of_bad_le`.
-/

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.OGPQAOAGoh25.MainResults

open Filter Topology
open Qatlib.Papers.OGPQAOAGoh25.MainResults.Model
open Qatlib.Concepts.MonteCarloMean.FinDistBounds

/-- **Lemma 4.5** (arXiv:2404.06087v6, p. 14, lines 717–719).

For `l n ≤ ε log n`, if with probability tending to one at most a `δ`-fraction
of vertices have a non-treelike radius-`l n` neighbourhood (the cycle-count
Markov bound of eqs. (28)–(31)), then with probability tending to one at least a
`1 - δ` fraction of the `l n`-local neighbourhoods are treelike. -/
theorem lemma45
    {q : ℕ} (hq : 2 ≤ q)
    (μ : ∀ n : ℕ, FinDist (Instance n q))
    (l : ℕ → ℕ) (ε : ℝ) (hε : 0 < ε)
    (hl : ∀ᶠ n : ℕ in atTop, (l n : ℝ) ≤ ε * Real.log n)
    (hbad : ∀ δ : ℝ, 0 < δ → ∀ᶠ n : ℕ in atTop,
      1 - δ ≤ mass (μ n) (fun I => (I.badCount (l n) : ℝ) ≤ δ * (n : ℝ))) :
    ∀ δ : ℝ, 0 < δ → ∀ᶠ n : ℕ in atTop,
      1 - δ ≤ mass (μ n) (fun I => 1 - δ ≤ I.treelikeFraction (l n)) := by
  intro δ hδ
  filter_upwards [hbad δ hδ, eventually_ge_atTop 1] with n hb hn
  have hn0 : 0 < n := lt_of_lt_of_le zero_lt_one hn
  refine le_trans hb (mass_mono (μ n) ?_)
  intro I hI
  exact I.treelikeFraction_ge (l n) hn0 hI

end Qatlib.Papers.OGPQAOAGoh25.MainResults
