/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Concepts.AmplitudeCore.PreparedReadout.PreparedAmplitudeEstimation
public import Qatlib.Concepts.LchsSimulation.StaticLchs.BitSampledPreparedSearch
public import Qatlib.Concepts.WalkSearch.QuantumAccess.GeometricSearchBudget
public import Qatlib.Concepts.AEMeanReadout.LocalAEBackend.RandomizedExecution
public import Qatlib.Concepts.AEMeanReadout.LocalAEBackend.FiniteStoppingTail
public import Qatlib.Concepts.AmplitudeCore.PayoffMedian.SignedCenteredQuantumMean
public import Qatlib.Concepts.MonteCarloMean.PilotVariance.UnknownVariancePilot
public import Qatlib.Concepts.MonteCarloMean.FinDistBounds.IndependentWeightedEstimator
public import Qatlib.Concepts.AEMeanReadout.LocalAEBackend.Theorem3QSearchStat
public import Qatlib.Concepts.AEMeanReadout.LocalAEBackend.Theorem3QSearchQuan
public import Qatlib.Concepts.AEMeanReadout.LocalAEBackend.AmplitudeReadoutCore
public import Qatlib.Concepts.AEMeanReadout.LocalAEBackend.AmplitudeReadout
public import Qatlib.Concepts.AEMeanReadout.LocalAEBackend.Theorem15ApproxCountStat
public import Qatlib.Concepts.AEMeanReadout.LocalAEBackend.Theorem15ExpectedCostStat
public import Qatlib.Concepts.AEMeanReadout.LocalAEBackend.Theorem17Stat
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Bound
public import Mathlib.Tactic.SimpRw
public import Mathlib.Tactic.SplitIfs
public import Mathlib.Basic.Real.Basic
public import Mathlib.Analysis.Real.Sqrt
public import Mathlib.Algebra.Order.Star.Real
public import Mathlib.Basic.NNReal.Defs
public import Mathlib.Basic.ENNReal.Basic
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Matrix.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Inverse
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.CStarAlgebra.Matrix

@[expose] public section

/-!
# Amplitude readout imports for population risk

This module collects prepared amplitude-estimation, randomized-execution, finite-stopping, and
finite-distribution imports for the `Qatlib.Concepts.RiskEstimation.PopulationGap` namespace. It
introduces no new mathematical declarations; the imported readout tools provide background for
the population-risk development.

The amplitude-estimation background is given in [BrassardEtAl2002].

## References

* [Brassard et al., 2002][BrassardEtAl2002]
-/

set_option backward.isDefEq.respectTransparency false

open Qatlib.Concepts.ProbabilityCore.Concentration
open Qatlib.Concepts.ProbabilityCore.Concentration.FiniteDecisionTree
open Qatlib.Concepts.AmplitudeCore.PayoffMedian.SignedMean
open Qatlib.Concepts.MonteCarloMean.FinDistBounds
open Qatlib.Concepts.LinearLearning.ConcisePipeline

open Qatlib.Concepts.AEMeanReadout.LocalAEBackend
open Qatlib.Concepts.AmplitudeCore.PayoffMedian
open Qatlib.Concepts.AmplitudeCore.PhaseEstimation
open Qatlib.Concepts.AmplitudeCore.PreparedReadout
open Qatlib.Concepts.MonteCarloMean.FinDistBounds.FinDist
open Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw

namespace Qatlib.Concepts.RiskEstimation.PopulationGap

open Qatlib
open Matrix
open scoped ENNReal Classical
open Qatlib.Concepts.AEMeanReadout.LocalAEBackend.BHMTQSearch
open Qatlib
open Qatlib
open Qatlib.Concepts.AEMeanReadout.LocalAEBackend.BHMTTh17
set_option autoImplicit false
set_option maxHeartbeats 1000000

variable {I : Type} [Fintype I] [DecidableEq I]

open Qatlib.Concepts.AEMeanReadout.LocalAEBackend.RandomizedExecution
open Filter
open scoped Topology

end Qatlib.Concepts.RiskEstimation.PopulationGap
