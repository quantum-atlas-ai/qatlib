/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.Recommender18.MainResults.SourceDefinitions

set_option backward.isDefEq.respectTransparency false

/-!
# Complexity envelopes and randomized-output success masses

Fixed arXiv:1807.04271.  The paper states its query/time complexities as
`O(poly(‖A‖_F/σ, 1/ε, 1/η, log(1/δ), ‖A_i‖/‖D_i‖))` (Theorem 1, p. 11;
Theorem 4.4, p. 14; Theorem 2, p. 22).  A big-`O` assertion is the existence of
an absolute constant times a polynomial in those parameters.  We fix an
explicit high-degree polynomial envelope `polyBound` (degree 16 in each of
`‖A‖_F/σ`, `1/ε`, `1/η`) that dominates every polynomial appearing in the
paper's analysis (the largest is `K⁴/ε̄²` with `K = ‖A‖_F²/σ²`, `ε̄ = ηε²/4`,
i.e. degree 8 in `‖A‖_F/σ` and 4 in `1/ε`).  The big-`O` statements are then
faithfully rendered as `∃ C > 0, cost ≤ C · polyBound …`.

`successMass law good` is the probability of a decidable event under a finite
law, the form in which the paper's "with probability at least `1 − δ`"
guarantees are stated.
-/

open scoped Classical BigOperators
open Qatlib.Concepts.MonteCarloMean.FinDistBounds

namespace Qatlib.Papers.Recommender18.MainResults

noncomputable section

/-- A dominating polynomial envelope for the paper's complexities. -/
def polyBound (F σ ε η δ : ℝ) : ℝ :=
  ((F / σ) ^ 2 + 1) ^ 16 * ((1 / ε) + 1) ^ 16 * ((1 / η) + 1) ^ 16 *
    (Real.log (1 / δ) + 1)

/-- The same envelope with the extra recommendation ratio `‖A_i‖/‖D_i‖`
(Theorem 1, p. 11). -/
def polyBoundRatio (F σ ε η δ ratio : ℝ) : ℝ :=
  polyBound F σ ε η δ * (ratio + 1) ^ 16

/-- Probability of a decidable event under a finite law. -/
def successMass {Ω : Type} [Fintype Ω] (law : FinDist Ω) (good : Ω → Prop)
    [DecidablePred good] : ℝ :=
  ∑ ω ∈ Finset.univ.filter good, law.prob ω

end

end Qatlib.Papers.Recommender18.MainResults
