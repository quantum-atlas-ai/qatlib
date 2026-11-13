/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.RiskEstimation.VaRQuantile.CVaRCumulativeRotationFees
import Qatlib.Concepts.RiskEstimation.CVaREstimation.NativeCVaRFiniteRestrictedQuan

/-!
# Conditional risk readout with rotation construction bounds

This module combines the native CVaR readout guarantee and sampling-call bound with rational
square-root construction and payoff-approximation bounds. The combined result is exposed as
`riskCVaRCumulativeRotationFees`.

The quantum risk-analysis setting is described in [WoernerEgger2019].

## Main statements

* `riskCVaRCumulativeRotationFees`: The cumulative CVaR specification combines the native
  readout error and supportwise call-count guarantees with rational square-root construction and
  payoff-approximation bounds; see [WoernerEgger2019].

## References

* [Woerner and Egger, 2019][WoernerEgger2019]
-/

set_option backward.isDefEq.respectTransparency false

open Qatlib.Concepts.PhaseGeometry.RationalCayleyPhase Qatlib.Concepts.MonteCarloMean.PayoffRotation
open Qatlib.Concepts.RiskEstimation.CVaREstimation
open Qatlib.Concepts.RiskEstimation.VaRQuantile
open Qatlib.Concepts.RiskEstimation.VaRQuantile.Papers.QuantumRiskAnalysis2018

set_option autoImplicit false
noncomputable section
namespace Qatlib.Concepts.RiskEstimation.PopulationGap
open Matrix

/-- The cumulative CVaR specification combines the native readout error and supportwise
call-count guarantees with rational square-root construction and payoff-approximation
bounds; see [WoernerEgger2019]. -/
theorem riskCVaRCumulativeRotationFees : CVaRCumulativeRotationFees := by
  intro I _ _ A j loss xs q ε rotationBits bits M r v hA hM hloss hxs hs hsupport hq0 hq1 heps hv hwindow habove hbelow hp
  have hmain := riskNativeCVaRFinite I A j loss xs q ε rotationBits bits M r v
    hA hM hloss hxs hs hsupport hq0 hq1 heps hv hwindow habove hbelow hp
  have htail := riskTailPayoff_bounds loss (xs.getD v 0) hloss
  refine ⟨hmain.1, hmain.2, ?_, ?_, ?_⟩
  · intro i
    exact (rational_sqrt_bracket_actual_interval_and_comparisons
      (riskTailPayoff loss (xs.getD v 0) i) rotationBits (htail i).1 (htail i).2).2.2.2.2.2.2.1
  · intro i
    exact (rational_sqrt_bracket_actual_interval_and_comparisons
      (1 - riskTailPayoff loss (xs.getD v 0) i) rotationBits
      (by linarith [(htail i).2]) (by linarith [(htail i).1])).2.2.2.2.2.2.1
  · intro i
    exact rationalPayoffValue_error (riskTailPayoff loss (xs.getD v 0) i) rotationBits
      (htail i).1 (htail i).2

end Qatlib.Concepts.RiskEstimation.PopulationGap
