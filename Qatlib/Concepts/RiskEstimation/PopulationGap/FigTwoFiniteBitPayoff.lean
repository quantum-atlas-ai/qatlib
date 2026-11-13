/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.RiskEstimation.VaRQuantile.FigTwoFiniteBitPayoff
import Qatlib.Concepts.RiskEstimation.PolyReadout.PolyFigTwoExpandedReadoutQuan
import Qatlib.Concepts.RiskEstimation.PolyReadout.PolyFigTwoExpandedWordLedgerQuan

/-!
# Polynomial payoff readout with finite-bit error allowance

This module proves `polyFigTwoFiniteBitPayoff` by combining expanded polynomial payoff readout
with the rotation-word bound. Its readout guarantee includes the additional nonnegative
angle-precision allowance specified by `FigTwoFiniteBitPayoff`.

The quantum risk-analysis setting is described in [WoernerEgger2019].

## Main statements

* `polyFigTwoFiniteBitPayoff`: The expanded Figure 2 payoff satisfies the specified readout
  bound with an added angle-precision allowance and the polynomial rotation-word length bound;
  see [WoernerEgger2019].

## References

* [Woerner and Egger, 2019][WoernerEgger2019]
-/

set_option backward.isDefEq.respectTransparency false

open Qatlib.Concepts.RiskEstimation.PolyReadout
open Qatlib.Concepts.RiskEstimation.PolyRotation
open Qatlib.Concepts.RiskEstimation.VaRQuantile
open Qatlib.Concepts.RiskEstimation.VaRQuantile.Papers.QuantumRiskAnalysis2018

set_option autoImplicit false
noncomputable section
namespace Qatlib.Concepts.RiskEstimation.PopulationGap
open Matrix
open scoped Classical BigOperators ENNReal

/-- The expanded Figure 2 payoff satisfies the specified readout bound with an added
angle-precision allowance and the polynomial rotation-word length bound; see
[WoernerEgger2019]. -/
theorem polyFigTwoFiniteBitPayoff : FigTwoFiniteBitPayoff := by
  intro n A j u c fp M r bits angleBits hA hM hf hc hc1
  refine ⟨?_, ?_⟩
  · have hread := polyFigTwoExpandedReadout n A j u c fp M r bits hA hM hf hc hc1
    have hpos : 0 ≤ 2 * (1 / 2 : ℝ) ^ angleBits / c := by positivity
    apply (risk_event_mono _ (fun w hw => ?_)).trans hread
    linarith
  · intro hn
    rw [figTwoAngleWord_length]
    exact figTwoTerms_gate_bound n (fp.natDegree * (2 * u + 1)) hn

end Qatlib.Concepts.RiskEstimation.PopulationGap
