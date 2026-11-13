/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.GradientOracle.FullRange.GradientDefs

/-!
# Collected Fourier gradient guarantees

This module proves three conjunctions collecting the full-range gradient construction, analytic
error transport, and implementation guarantees. These combine the finite-grid approach of
[Jordan2005Gradient] with robust readout and higher-order approximation results related to
[GilyenArunachalamWiebe2019].

## Main statements

* `stageB_fourier_gradient_gext1`: full-range precision, numerical gradient, variance, and
  step-size guarantees.
* `stageB_fourier_gradient_gext2`: almost-affine and central-difference error guarantees.
* `stageB_fourier_gradient_gext3`: readout, finite-code unitarity, median, and
  character-kickback guarantees.

## References

* [Jordan, 2005][Jordan2005Gradient]
* [Gilyen, Arunachalam and Wiebe, 2019][GilyenArunachalamWiebe2019]
-/

set_option backward.isDefEq.respectTransparency false

open Qatlib.Concepts.ProbabilityCore.Concentration.FiniteDecisionTree
open Qatlib.Concepts.MonteCarloMean.FinDistBounds.FinDist

open Qatlib.Foundations.BornMetrics.EventProbability
open Qatlib.Concepts.GateVocabulary.FiniteGateDescription
open Qatlib.Concepts.GradientOracle.C2GradientAlg
open Qatlib.Concepts.GradientOracle.ReadoutTools

set_option autoImplicit false

namespace Qatlib.Concepts.GradientOracle.FullRange

open Qatlib
open Qatlib
open Qatlib
open Qatlib.Concepts.GradientOracle.StationaryPhase
open Qatlib.Concepts.GradientOracle.StepSizes
open Qatlib.Concepts.GradientOracle.CentralDiff
open Qatlib.Concepts.GradientOracle.DifferenceError
open Qatlib.Concepts.GradientOracle.GradientAlgo
open Qatlib
open Qatlib
open Qatlib.Concepts.HspRecovery.Reduction.GradientOracle
open Qatlib.Concepts.GradientOracle.GradientAlgo
open Qatlib

/-- Combines full-range character kickback, fixed-point precision, gradient readout, numerical
gradient estimation, cube-variance formulas, and classical/quantum step-size guarantees. -/
theorem stageB_fourier_gradient_gext1 : stageB_fourier_gradient_gext1_spec := by
  refine ⟨fullRangeCharacterKickback,
          fullRangeFixedPointPrecision,
          fullRangeGradientReadout,
          numericalGradientAlgorithm,
          stationaryPhaseVariance,
          classicalQuantumStepSizes⟩

/-- Combines rescaled almost-affine gradient estimation, analytic and one-dimensional
central-difference bounds, exceptional phase transport, pure-state event stability, and
full-range character kickback. -/
theorem stageB_fourier_gradient_gext2 : stageB_fourier_gradient_gext2_spec := by
  refine ⟨sourceAlmostAffineGradient,
          analyticCentralDifferenceGridError,
          centralDifferenceDirectionalError,
          centralDifferenceOneDimError,
          exceptionalPhaseGradientTransport,
          pureStateEventLipschitz,
          fullRangeCharacterKickback⟩

/-- Combines the Fourier readout and implementation guarantees of `g8` with finite-code matrix
unitarity, vector-median amplification, and full-range character kickback. -/
theorem stageB_fourier_gradient_gext3 : stageB_fourier_gradient_gext3_spec := by
  refine ⟨g8,
          finiteCodeMatrix_unitary,
          almostAffineVectorMedian,
          fullRangeCharacterKickback⟩

end Qatlib.Concepts.GradientOracle.FullRange
