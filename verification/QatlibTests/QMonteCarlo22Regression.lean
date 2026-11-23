module

import Qatlib.Papers.QMonteCarlo22.MainResults.MeanEstimation

set_option autoImplicit false

namespace QatlibTests.QMonteCarlo22Regression

open scoped BigOperators
open Qatlib.Concepts.MonteCarloMean.FinDistBounds

/-- Ordinary-module consumer for the QMonteCarlo22 median-of-means theorem. -/
example {X : Type*} [Fintype X] [DecidableEq X]
    {L : ℕ} (p : FinDist X) (f : X → ℝ)
    (hL : 0 < L) (ε : ℝ) (hε : 0 < ε)
    (hvar : 4 * p.variance f ≤ (L : ℝ) * ε ^ 2) :
    (∑ ω ∈ Finset.univ.filter
        (fun ω : Fin 8 → Fin L → X => ε <
          |p.medianOfMeans f ω - p.expect f|),
      ∏ m, p.probOf (ω m)) ≤ (1 : ℝ) / 3 :=
  Qatlib.Papers.QMonteCarlo22.MainResults.theorem_1_1_median_of_means
    p f hL ε hε hvar

end QatlibTests.QMonteCarlo22Regression
