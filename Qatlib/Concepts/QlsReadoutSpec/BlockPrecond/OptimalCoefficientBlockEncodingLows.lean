/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.QlsReadoutSpec.BlockPrecond.PreconditionedEndpoint
import Qatlib.Concepts.QlsReadoutSpec.BlockPrecond.OptimalCoefficientBlockEncodingStat

/-!
# Optimal-coefficient encoding and its pseudoinverse obstruction

This module establishes `optimalCoefficientBlockEncodingSubgoal` through the completed
preconditioned encoding construction. It also packages
`optimalCoefficientPseudoinverseObstruction`, an explicit normalized example at scale 1/2 where
the unrestricted pseudoinverse product identity fails, highlighting the role of consistency in
the encoding specification.

The reciprocal block transformation is based on the quantum singular value transformation
framework [GilyenSuLowWiebe2019].

## Main statements

* `optimalCoefficientPseudoinverseObstruction`: Packages the concrete failure of the
  unrestricted pseudoinverse identity.
* `optimalCoefficientBlockEncodingSubgoal`: Establishes the optimal-coefficient encoding
  specification.

## References

* [Gilyén et al., 2019][GilyenSuLowWiebe2019]
-/

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

/-- Packages scale `1 / 2` in the open unit interval, normalization of the explicit
counterexample state, and failure of the unrestricted pseudoinverse product identity for its
counterexample matrix. -/
theorem optimalCoefficientPseudoinverseObstruction :
    (0 : ℝ) < 1 / 2 ∧ (1 / 2 : ℝ) < 1 ∧
      Normalized preconditioningCounterState ∧
      matrixPseudoinverse (stateScaling (1 / 2) preconditioningCounterState *
          preconditioningCounterMatrix) ≠
        matrixPseudoinverse preconditioningCounterMatrix *
          stateScalingInverse (1 / 2) preconditioningCounterState := by
  exact ⟨by norm_num, by norm_num, preconditioningCounterState_normalized,
    stateScaling_pseudoinverse_counterexample⟩

/-- Establishes `OptimalCoefficientBlockEncodingSubgoal`, including the preconditioned
reciprocal encoding, degree and compilation counts, success-probability lower bound, and
normalized output error bound. -/
theorem optimalCoefficientBlockEncodingSubgoal : OptimalCoefficientBlockEncodingSubgoal :=
  optimalCoefficientBlockEncoding_complete
end Qatlib.Concepts.QlsReadoutSpec.BlockPrecond
