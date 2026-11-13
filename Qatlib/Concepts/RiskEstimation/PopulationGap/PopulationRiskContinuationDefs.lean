/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.RiskEstimation.PopulationGap.AmplitudeReadoutDefs
import Qatlib.Concepts.RiskEstimation.PopulationGap.NativeRiskDefs
import Qatlib.Concepts.NativeNumerics.EmpiricalRisk.EmpiricalRiskConsumers
import Qatlib.Concepts.RiskEstimation.VaRQuantile.BisectFiniteRoutingSubgoalQuan
import Qatlib.Concepts.PhaseGeometry.RationalCayleyPhase
import Qatlib.Concepts.CircuitImpl.MultiControl.NoWorkTwoLevelSynthesis
import Qatlib.Concepts.RiskEstimation.PopulationGap.Implementation
import Qatlib.Concepts.RiskEstimation.PopulationGap.ImplementationDefs
import Qatlib.Concepts.RiskEstimation.PopulationGap.GatesDefs
import Qatlib.Concepts.RiskEstimation.PopulationGap.OrderShorDefs
import Qatlib.Concepts.AEMeanReadout.LocalAEBackend.RationalLabelReadout
import Qatlib.Concepts.AEMeanReadout.LocalAEBackend.ComparativeStrictBounds
import Qatlib.Concepts.AEMeanReadout.LocalAEBackend.CountingOracleTransport
import Qatlib.Concepts.AEMeanReadout.LocalAEBackend.EffectiveIntegerReadout
import Qatlib.Concepts.AEMeanReadout.LocalAEBackend.SearchBudget
import Qatlib.Concepts.AEMeanReadout.LocalAEBackend.SearchLoop
import Qatlib.Concepts.AEMeanReadout.LocalAEBackend.SearchProgram
import Qatlib.Concepts.AEMeanReadout.LocalAEBackend.UnboundedSourceSearch
import Qatlib.Concepts.AEMeanReadout.LocalAEBackend.UnknownSigmaMean

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
