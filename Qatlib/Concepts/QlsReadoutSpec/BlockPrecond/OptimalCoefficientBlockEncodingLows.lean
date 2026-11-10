/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.QlsReadoutSpec.BlockPrecond.PreconditionedEndpoint
import Qatlib.Concepts.QlsReadoutSpec.BlockPrecond.OptimalCoefficientBlockEncodingStat
set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

open Qatlib.Concepts.CoherentSim.CoherentOAA
open Qatlib.Foundations.InstrumentCore.ProjectiveMeasurementLaws
open Qatlib.Foundations.OperatorErrors.OperatorError

open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.CoherentSim.CoherentOAA.SignalProcessing
open Qatlib.Concepts.PhaseGeometry.Phase
open Qatlib.Concepts.OperatorErrors.Robustness.SignalProcessing

set_option autoImplicit false
namespace Qatlib.Concepts.QlsReadoutSpec.BlockPrecond
open Qatlib.Concepts.CoherentSim.CoherentOAA.SignalProcessing Qatlib.Concepts.PhaseGeometry.Phase
open Qatlib.Concepts.OperatorErrors.Robustness.SignalProcessing
open Matrix

theorem optimalCoefficientPseudoinverseObstruction :
    (0 : ℝ) < 1 / 2 ∧ (1 / 2 : ℝ) < 1 ∧
      Normalized preconditioningCounterState ∧
      matrixPseudoinverse (stateScaling (1 / 2) preconditioningCounterState *
          preconditioningCounterMatrix) ≠
        matrixPseudoinverse preconditioningCounterMatrix *
          stateScalingInverse (1 / 2) preconditioningCounterState := by
  exact ⟨by norm_num, by norm_num, preconditioningCounterState_normalized,
    stateScaling_pseudoinverse_counterexample⟩

theorem optimalCoefficientBlockEncodingSubgoal : OptimalCoefficientBlockEncodingSubgoal :=
  optimalCoefficientBlockEncoding_complete
end Qatlib.Concepts.QlsReadoutSpec.BlockPrecond
