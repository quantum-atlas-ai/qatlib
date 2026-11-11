/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.RiskEstimation.VaRQuantile.RiskDefs
import Qatlib.Concepts.AEMeanReadout.LayeredMeanLaw.RationalWeightPreparation
import Qatlib.Concepts.MonteCarloMean.PayoffRotation.RationalPayoffRotation

/-!
# Rational market distribution loading specification

`MarketPayoffLoading` specifies how rational weight preparation and rational payoff rotations
approximate a weighted loss distribution. It combines unitarity and operator-norm control of
`rationalWeightPrepare` with comparison counts and error bounds for the cumulative probability
and truncated loss numerator used in [WoernerEgger2019].

## Main statements

* `MarketPayoffLoading`: preparation accuracy, comparison cost, and propagated risk-payoff
  errors.

## References

* [Woerner and Egger, 2019][WoernerEgger2019]
-/

set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

open Qatlib.Concepts.AmplitudeCore.PayoffMedian.SignedMean
open Qatlib.Concepts.LinearLearning.ConcisePipeline

open Qatlib.Concepts.AEMeanReadout.LayeredMeanLaw
open Qatlib.Concepts.PhaseGeometry.RationalCayleyPhase Qatlib.Concepts.MonteCarloMean.PayoffRotation
open Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw
open Qatlib.Concepts.RiskEstimation.VaRQuantile.Papers.QuantumRiskAnalysis2018

open Qatlib.Foundations.PureStateMath

set_option autoImplicit false
noncomputable section
namespace Qatlib.Concepts.RiskEstimation.VaRQuantile
open Matrix
open scoped Classical BigOperators Matrix.Norms.L2Operator

/-- The specification of unitary rational weight preparation, its operator-norm error and
comparison count, and the resulting cumulative-probability and truncated-payoff errors. -/
def MarketPayoffLoading : Prop :=
  ∀ (n bits payoffBits : ℕ) (w : Option (Fin n) → ℚ) (loss : Option (Fin n) → ℚ),
    (∀ a, 0 ≤ w a) → 0 < rationalWeightMass w →
    (∀ a, 0 ≤ loss a ∧ loss a ≤ 1) →
    rationalWeightPrepare w bits ∈ Matrix.unitaryGroup (Option (Fin n)) ℂ ∧
    ‖rationalWeightPrepare w bits - idealWeightPrepare w‖ ≤ 32 * (n : ℝ) / 2 ^ bits ∧
    rationalWeightComparisons w bits = 2 * n * bits ∧
    (∀ t : ℚ,
      |riskCDF (rationalWeightPrepare w bits) none loss t -
        (∑ a, ((w a / rationalWeightMass w : ℚ) : ℝ) * riskCDFPayoff loss t a)| ≤
        64 * (n : ℝ) / 2 ^ bits) ∧
    (∀ t : ℚ,
      |(∑ i, BornProb (rationalWeightPrepare w bits *ᵥ Ket none) i *
            (rationalPayoffValue (riskTailPayoff loss t i) payoffBits : ℝ)) -
        (∑ a, ((w a / rationalWeightMass w : ℚ) : ℝ) * (riskTailPayoff loss t a : ℝ))| ≤
        64 * (n : ℝ) / 2 ^ bits + 64 / 2 ^ payoffBits)

end Qatlib.Concepts.RiskEstimation.VaRQuantile
