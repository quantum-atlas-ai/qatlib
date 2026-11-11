/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.OGPQAOAGoh25.MainResults.Model.SourceModel

set_option backward.isDefEq.respectTransparency false

/-!
# Theorem 4.1 — OGP limitation transfers from Erdős–Rényi to random regular

Fixed source: arXiv:2404.06087v6, Theorem 4.1 (p. 11, lines 489–503).

> Given a local algorithm `A` that is limited in performance up to depth
> `p = ε log n` on an Erdős–Rényi hypergraph with sufficiently large average
> degree `λ`, `A` is also limited in performance up to depth `p` on a random
> `D`-regular hypergraph for sufficiently large `D`.

The paper proves this by contradiction (§4.1, pp. 13–17): after trimming and
re-adding edges the two ensembles are `p`-locally the same on a `1 - o(1)`
fraction of vertices (Lemmas 4.5–4.7), so an algorithm that found near-optimal
solutions on the regular graph would also find them on the Erdős–Rényi graph,
contradicting the assumed limitation.

This file states the asymptotic transfer faithfully and proves its logical
core (`limited_transfer` in `Model.SourceModel`). The hypothesis
`hLocalSame` is exactly the `p`-local coupling step supplied by Lemmas 4.5–4.7
plus the bounded-degree cost comparison of §4.1.
-/

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.OGPQAOAGoh25.MainResults

open scoped BigOperators
open Filter Topology
open Qatlib.Papers.OGPQAOAGoh25.MainResults.Model
open Qatlib.Concepts.MonteCarloMean.FinDistBounds

/-- **Theorem 4.1** (arXiv:2404.06087v6, p. 11, lines 489–503).

Let `A` be a family of `p n`-local algorithms with `p n ≤ ε log n`. If, with
probability tending to one, the output of `A n` on an Erdős–Rényi law `er n`
has energy density below `η n`, and if the Erdős–Rényi and `D`-regular laws
`er n`, `reg n` come with a `p n`-local coupling whose output densities agree up
to `γ n → 0` with probability tending to one (the content of Lemmas 4.5–4.7),
then with probability tending to one the output of `A n` on the random regular
law `reg n` has density below `η n + γ n`. Choosing `η n` below the OGP
threshold and `γ n → 0` yields the statement of the paper. -/
theorem theorem41
    {q : ℕ} (hq : 2 ≤ q)
    (p : ℕ → ℕ) (ε : ℝ) (hε : 0 < ε)
    (hp : ∀ᶠ n : ℕ in atTop, (p n : ℝ) ≤ ε * Real.log n)
    (A : ∀ n : ℕ, LocalAlgorithm n q (p n))
    (er reg : ∀ n : ℕ, FinDist (Instance n q))
    (η γ : ℕ → ℝ) (hγ : Tendsto γ atTop (𝓝 0))
    (hLimER : ∀ δ : ℝ, 0 < δ → ∀ᶠ n : ℕ in atTop,
      1 - δ ≤ mass (er n) (fun I => (A n).density I < η n))
    (hLocalSame : ∀ δ : ℝ, 0 < δ → ∀ᶠ n : ℕ in atTop,
      ∃ ν : FinDist (Instance n q × Instance n q),
        marginalFst ν = er n ∧ marginalSnd ν = reg n ∧
          1 - δ ≤ mass ν (fun ω =>
            |ω.1.density ((A n).output ω.1) - ω.2.density ((A n).output ω.2)| ≤ γ n)) :
    ∀ δ : ℝ, 0 < δ → ∀ᶠ n : ℕ in atTop,
      1 - δ ≤ mass (reg n) (fun I => (A n).density I < η n + γ n) := by
  intro δ hδ
  have hhalf : 0 < δ / 2 := by linarith
  filter_upwards [hLimER (δ / 2) hhalf, hLocalSame (δ / 2) hhalf] with n hER hLS
  obtain ⟨ν, hfst, hsnd, hclose⟩ := hLS
  have h := limited_transfer ν (A n) (η n) (γ n) (δ / 2) (δ / 2) hclose (by
    rw [hfst]
    exact hER)
  rw [← hsnd]
  simpa only [LocalAlgorithm.density, show δ / 2 + δ / 2 = δ by ring] using h

end Qatlib.Papers.OGPQAOAGoh25.MainResults
