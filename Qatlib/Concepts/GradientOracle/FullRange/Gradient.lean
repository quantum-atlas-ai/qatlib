/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.GradientOracle.FullRange.GradientDefs
set_option warningAsError false
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

theorem stageB_fourier_gradient_gext1 : stageB_fourier_gradient_gext1_spec := by
  refine ⟨fullRangeCharacterKickback,
          fullRangeFixedPointPrecision,
          fullRangeGradientReadout,
          numericalGradientAlgorithm,
          stationaryPhaseVariance,
          classicalQuantumStepSizes⟩

theorem stageB_fourier_gradient_gext2 : stageB_fourier_gradient_gext2_spec := by
  refine ⟨sourceAlmostAffineGradient,
          analyticCentralDifferenceGridError,
          centralDifferenceDirectionalError,
          centralDifferenceOneDimError,
          exceptionalPhaseGradientTransport,
          pureStateEventLipschitz,
          fullRangeCharacterKickback⟩

theorem stageB_fourier_gradient_gext3 : stageB_fourier_gradient_gext3_spec := by
  refine ⟨g8,
          finiteCodeMatrix_unitary,
          almostAffineVectorMedian,
          fullRangeCharacterKickback⟩

end Qatlib.Concepts.GradientOracle.FullRange
