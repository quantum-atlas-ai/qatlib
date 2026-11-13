/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.MixedFidelity.FidelityMetric.ChannelHelpers.FinitePOVMTraceDistance

/-!
# Finite-output data processing

`native_finite_output_data_processing` bounds the distinguishing advantage of finite POVM
records after a common positive trace-preserving map by the original state trace distance.
`native_finite_output_advantage_eq_tv` identifies finite-output advantage with total variation.
See [Watrous2018].

## Main statements

* `native_finite_output_data_processing`: input trace distance bounds processed measurement
  advantage.
* `native_finite_output_advantage_eq_tv`: equality of advantage and total variation.

## References

* [Watrous, 2018][Watrous2018]
-/

set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false
namespace Qatlib.Concepts.MixedFidelity.FidelityMetric.FourierLabelHelpers
open Matrix Qatlib.Concepts.MbqcFlow.FlowDecision.MeasurementStatisticsExt
open scoped BigOperators Classical
noncomputable section

/-- A common positive trace-preserving map followed by a finite POVM yields distinguishing
advantage at most the trace distance between the original density operators. -/
theorem native_finite_output_data_processing {O : Type} [Fintype O] [DecidableEq O]
    {d k : ℕ} (E : Qatlib.Concepts.MbqcFlow.FlowDecision.MeasurementStatisticsExt.FinitePOVM O k) (T : MatrixMap (Fin d) (Fin k) ℂ)
    (hT : T.IsPositive) (ht : T.IsTracePreserving)
    (rho sigma : Qatlib.Foundations.PureStateMath.DensityOperator d) :
    let hr : Qatlib.Foundations.PureStateMath.IsDensityOperator (T rho.val) :=
        ⟨hT rho.property.1,(ht rho.val).trans rho.property.2⟩
    let hs : Qatlib.Foundations.PureStateMath.IsDensityOperator (T sigma.val) :=
        ⟨hT sigma.property.1,(ht sigma.val).trans sigma.property.2⟩
    Qatlib.Concepts.MonteCarloMean.FinDistBounds.FiniteOutputDistinguishability.advantage (Qatlib.Concepts.MbqcFlow.FlowDecision.MeasurementStatisticsExt.povmRecordLaw E (T rho.val) hr)
      (Qatlib.Concepts.MbqcFlow.FlowDecision.MeasurementStatisticsExt.povmRecordLaw E (T sigma.val) hs) ≤ Matrix.traceNorm (rho.val-sigma.val)/2 :=
  Qatlib.Concepts.MixedFidelity.FidelityMetric.FinitePOVMTraceDistance.after_common_channel E T hT ht rho.val sigma.val rho.property sigma.property

/-- For finite probability distributions, the distinguishing advantage equals their total
variation distance. -/
theorem native_finite_output_advantage_eq_tv {O : Type} [Fintype O] [DecidableEq O]
    (p q : Qatlib.Concepts.MonteCarloMean.FinDistBounds.FinDist O) : Qatlib.Concepts.MonteCarloMean.FinDistBounds.FiniteOutputDistinguishability.advantage p q =
      Qatlib.Concepts.MonteCarloMean.FinDistBounds.FiniteInformationDivergence.tv p q := Qatlib.Concepts.MonteCarloMean.FinDistBounds.FiniteOutputDistinguishability.advantage_eq_tv p q
end
end Qatlib.Concepts.MixedFidelity.FidelityMetric.FourierLabelHelpers
