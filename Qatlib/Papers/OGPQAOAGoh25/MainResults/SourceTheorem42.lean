/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.OGPQAOAGoh25.MainResults.Model.SourceModel

set_option backward.isDefEq.respectTransparency false

/-!
# Theorem 4.2 — OGP bound for the QAOA on random regular hypergraphs

Fixed source: arXiv:2404.06087v6, Theorem 4.2 and eq. (19) (pp. 11–12,
lines 508–519).

> For Max-`q`-XORSAT on a `D`-regular `q`-uniform hypergraph, for every even
> `q ≥ 4`, there exists a value `ηOGP` smaller than the optimal value `ηOPT`
> such that for every `ε > 0` there is `d₀` with: for every `d > d₀`, every
> depth `p ≤ d log n`, and arbitrary parameters `γ, β`, with probability
> converging to one as `n → ∞` the QAOA performance satisfies eq. (19), in
> particular `⟨γ,β|C_XOR/n|γ,β⟩ / |E| < ηOGP + ε`.

The paper derives this by combining Theorem 3.5 (the explicit evaluation of
eq. (19) at the tree/Parisi value, the hypothesis `hBound` below) with the
transfer of Theorem 4.1. This file states the resulting theorem and proves the
elementary assembly of the `ε`, `d`, `p`, `γ, β` and probability quantifiers.
-/

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.OGPQAOAGoh25.MainResults

open scoped BigOperators
open Filter Topology
open Qatlib.Papers.OGPQAOAGoh25.MainResults.Model
open Qatlib.Concepts.MonteCarloMean.FinDistBounds

/-- **Theorem 4.2** (arXiv:2404.06087v6, p. 11, lines 508–519).

For even `q ≥ 4` and a law `reg` supported on `D`-regular `q`-uniform
hypergraphs, assume the quantitative bound of eq. (19) in the form supplied by
Theorem 3.5: there is `ηOGP < ηOPT` such that for every depth schedule
`p ≤ D log n` and every `γ, β` the performance is, with probability tending to
one, at most some level `L ≤ ηOGP` up to an arbitrarily small slack. Then for
every `ε > 0` the same holds with the deterministic threshold `ηOGP + ε`. -/
theorem theorem42
    {q : ℕ} (hq4 : 4 ≤ q) (hqeven : Even q)
    (D : ℕ) (hD : 0 < D)
    (reg : ∀ n : ℕ, FinDist (Instance n q))
    (hRegLaw : ∀ n : ℕ, IsRegularLaw (reg n) D)
    (ηOPT : ℝ)
    (hBound : ∃ ηOGP : ℝ, ηOGP < ηOPT ∧
      ∀ (p : ℕ → ℕ),
        (∀ᶠ n : ℕ in atTop, (p n : ℝ) ≤ (D : ℝ) * Real.log n) →
        ∀ (γ β : ∀ n : ℕ, Fin (p n) → ℝ),
          ∃ L : ℝ, L ≤ ηOGP ∧
            ∀ δ : ℝ, 0 < δ → ∀ᶠ n : ℕ in atTop,
              1 - δ ≤ mass (reg n) (fun I =>
                qaoaPerformance I (p n) (γ n) (β n) < L + δ)) :
    ∃ ηOGP : ℝ, ηOGP < ηOPT ∧
      ∀ ε : ℝ, 0 < ε →
      ∀ (p : ℕ → ℕ),
        (∀ᶠ n : ℕ in atTop, (p n : ℝ) ≤ (D : ℝ) * Real.log n) →
        ∀ (γ β : ∀ n : ℕ, Fin (p n) → ℝ),
          ∀ δ : ℝ, 0 < δ → ∀ᶠ n : ℕ in atTop,
            1 - δ ≤ mass (reg n) (fun I =>
              qaoaPerformance I (p n) (γ n) (β n) < ηOGP + ε) := by
  obtain ⟨ηOGP, hsep, hcore⟩ := hBound
  refine ⟨ηOGP, hsep, ?_⟩
  intro ε hε p hp γ β δ hδ
  obtain ⟨L, hL, hmass⟩ := hcore p hp γ β
  have hδε : 0 < min δ ε := lt_min hδ hε
  have hm := hmass (min δ ε) hδε
  filter_upwards [hm] with n hn
  have hstep : (1 : ℝ) - δ ≤ 1 - min δ ε := by
    have h1 : min δ ε ≤ δ := min_le_left δ ε
    linarith
  refine le_trans hstep ?_
  refine le_trans hn ?_
  refine mass_mono (reg n) ?_
  intro I hI
  have hle : L + min δ ε ≤ ηOGP + ε := by
    have h1 : min δ ε ≤ ε := min_le_right δ ε
    linarith
  exact lt_of_lt_of_le hI hle

end Qatlib.Papers.OGPQAOAGoh25.MainResults
