module

public import Qatlib.Papers.DysonSeries22.MainResults.FactorialEndpoint

@[expose] public section
set_option autoImplicit false
noncomputable section

namespace QatlibTests.DysonSeries22FactorialRegression

open Matrix
open scoped Matrix.Norms.L2Operator
open Qatlib.Foundations.PureStateMath
open Qatlib.Foundations.PureStateMath.BornBridge
open Qatlib.Papers.DysonSeries22.ExactSource
open Qatlib.Papers.DysonSeries22.Truncation
open Qatlib.Papers.DysonSeries22.PureDistance

/-- An ordinary module consumer can apply the explicit factorial endpoint estimate. -/
example {I : Type} [Fintype I] [DecidableEq I]
    (A : ℝ → Matrix I I ℂ) (b x : ℝ → QState I)
    (hA : Continuous A) (hb : Continuous b)
    (s t M C : ℝ) (hM : 0 ≤ M) (hC : 0 ≤ C)
    (hboundA : ∀ u ∈ Set.uIcc s t, ‖A u‖ ≤ M)
    (hboundb : ∀ u ∈ Set.uIcc s t,
      ‖toEuclidean_fromVec (b u)‖ ≤ C)
    (hx : ∀ u, HasDerivAt x (A u *ᵥ x u + b u) u) (K : ℕ) :
    rankOneDistance (truncatedSolution A b (x s) s t K)
        (toEuclidean_fromVec (x t)) ≤
      (M * |t - s|) ^ (K + 1) / ((K + 1).factorial : ℝ) *
          Real.exp (M * |t - s|) * ‖toEuclidean_fromVec (x s)‖ +
        C * |t - s| *
          ((M * |t - s|) ^ K / ((K + 1).factorial : ℝ) *
            Real.exp (M * |t - s|)) :=
  Qatlib.Papers.DysonSeries22.MainResults.finite_endpoint_rankone_factorial_error
    A b x hA hb s t M C hM hC hboundA hboundb hx K

end QatlibTests.DysonSeries22FactorialRegression
