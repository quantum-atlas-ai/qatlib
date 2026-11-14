/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Concepts.RiskEstimation.PopulationGap.AmplitudeReadoutDefs
public import Qatlib.Concepts.RiskEstimation.PopulationGap.NativeRiskDefs
public import Qatlib.Concepts.NativeNumerics.EmpiricalRisk.EmpiricalRiskConsumers
public import Qatlib.Concepts.RiskEstimation.VaRQuantile.BisectFiniteRoutingSubgoalQuan
public import Qatlib.Concepts.PhaseGeometry.RationalCayleyPhase
public import Qatlib.Concepts.CircuitImpl.MultiControl.NoWorkTwoLevelSynthesis
public import Qatlib.Concepts.RiskEstimation.PopulationGap.Implementation
public import Qatlib.Concepts.RiskEstimation.PopulationGap.ImplementationDefs
public import Qatlib.Concepts.RiskEstimation.PopulationGap.GatesDefs
public import Qatlib.Concepts.RiskEstimation.PopulationGap.OrderShorDefs
public import Qatlib.Concepts.AEMeanReadout.LocalAEBackend.RationalLabelReadout
public import Qatlib.Concepts.AEMeanReadout.LocalAEBackend.ComparativeStrictBounds
public import Qatlib.Concepts.AEMeanReadout.LocalAEBackend.CountingOracleTransport
public import Qatlib.Concepts.AEMeanReadout.LocalAEBackend.EffectiveIntegerReadout
public import Qatlib.Concepts.AEMeanReadout.LocalAEBackend.SearchBudget
public import Qatlib.Concepts.AEMeanReadout.LocalAEBackend.SearchLoop
public import Qatlib.Concepts.AEMeanReadout.LocalAEBackend.SearchProgram
public import Qatlib.Concepts.AEMeanReadout.LocalAEBackend.UnboundedSourceSearch
public import Qatlib.Concepts.AEMeanReadout.LocalAEBackend.UnknownSigmaMean

@[expose] public section

/-!
# Shared imports for population risk continuation

This module gathers the native risk, amplitude readout, numerical preparation, phase,
arithmetic, and search interfaces used by population risk continuation. It introduces no new
declarations; the imported constructions support the quantum risk analysis setting of
[WoernerEgger2019].

## Available interfaces

* `riskNativeVaR` and `riskNativeCVaR`: native probabilistic risk programs.
* `clause11`: arithmetic, workspace, access, and loading accounting.
* `euclid_gcd_fuel`: the fuel bound for Euclidean computation.
* `SpaceSchedule`: live workspace schedule data.

## References

* [Woerner and Egger, 2019][WoernerEgger2019]
-/

set_option backward.isDefEq.respectTransparency false

open Qatlib.Concepts.AmplitudeCore.PayoffMedian.SignedMean
open Qatlib.Concepts.LocalMachine.LocalTransport
open Qatlib.Concepts.LinearLearning.ConcisePipeline

open Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw
open Qatlib.Concepts.PeriodSampling.FactorAlgorithm

namespace Qatlib.Concepts.RiskEstimation.PopulationGap

open Qatlib
open Matrix
open scoped ENNReal Classical BigOperators
open Qatlib
open Qatlib.Concepts.RiskEstimation.CDFEstimation
open Qatlib.Concepts.RiskEstimation.CVaREstimation
open Qatlib
open Qatlib.Concepts.RiskEstimation.PopulationGap
open Qatlib.Concepts.RiskEstimation.VaRQuantile
open Qatlib.Concepts.RiskEstimation.VaRQuantile.Papers.QuantumRiskAnalysis2018
open Qatlib
set_option autoImplicit false
set_option maxHeartbeats 1000000

variable {I : Type} [Fintype I] [DecidableEq I]
variable {n N : ℕ}

open scoped Matrix.Norms.L2Operator
open Qatlib.Concepts.RiskEstimation.PopulationGap (clause11 euclid_gcd_fuel)
open Qatlib.Concepts.RiskEstimation.PopulationGap (shorBitLength euclidGcd euclidStepBound)
open Qatlib.Concepts.RiskEstimation.PopulationGap (SpaceSchedule)

end Qatlib.Concepts.RiskEstimation.PopulationGap
