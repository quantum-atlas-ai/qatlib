/-
Copyright (c) 2026 Quantum Atlas Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quantum Atlas Contributors
-/

module

public import Qatlib.Concepts.GraphQuery.GcBaselines.CycleAlgorithmLabelReductionStat
public import Qatlib.Concepts.GraphQuery.GcBaselines.GadgetOracleQuerySimulationQuan
public import Qatlib.Concepts.GraphQuery.GcBaselines.CycleGadgetEquivalenceQuan
public import Qatlib.Concepts.GraphQuery.GcBaselines.CycleThroughSAdversaryLowerBoundQuan

@[expose] public section
set_option backward.isDefEq.respectTransparency false
open Qatlib.Concepts.BlockEncoding Qatlib.Concepts.BlockEncoding.Encoding Qatlib.Concepts.BlockEncoding.Postselection Qatlib.Concepts.BlockEncoding.Postselection.Encoding Qatlib.Foundations.BornMetrics.EventProbability Qatlib.Foundations.InstrumentCore.Measurement Qatlib.Foundations.InstrumentCore.ProjectiveMeasurement Qatlib.Foundations.InstrumentCore.ProjectiveMeasurementLaws Qatlib.Foundations.OperatorErrors.OperatorError Qatlib.Foundations.PureStateMath.BornBridge Qatlib.Foundations.PureStateMath Qatlib.Foundations.PureStateMath.Reflection Qatlib.Foundations.QueryWordCore.Circuit Qatlib.Concepts.QueryWordCore.QueryMachinery

set_option autoImplicit false
noncomputable section
open Qatlib.Foundations.QueryWordCore.Circuit
open Qatlib.Foundations.PureStateMath

open Qatlib.Concepts.QueryComplexity.AdversarySearch
open Qatlib.Concepts.GraphQuery.GcBaselines.QuantumAlgorithmsForPathAndCycleContainmentProblems2026

namespace Qatlib.Concepts.GraphQuery.GcBaselines
open Matrix
open scoped Classical

/-- Establishes the cycle algorithm reduction to label queries in
`CycleAlgorithmLabelReduction`. -/
theorem cycleAlgorithmLabelReduction : CycleAlgorithmLabelReduction := by
  intro W _ _ n hn C ψ E hC hψ hcorrect adj
  have hsim := gadgetOracleQuerySimulation W n hn adj C
  refine ⟨hsim.1 hC, normalized_tensorState (normalized_ket _) hψ, hsim.2.1, hsim.2.2.1, ?_⟩
  intro x
  have hc : 2/3 ≤ MeasureProb (Run (workspaceBitOracle (W := W) (gadgetOracleBit adj x)) C ψ)
      (if gcOr adj x then E else Eᶜ) := by
    have h := hcorrect ⟨gadgetAdjAt adj x, gadgetAdjAt_simple adj x⟩
    rwa [cycleGadgetEquivalence n adj x] at h
  rw [(hsim.2.2.2 x ψ).2]
  exact hc

end Qatlib.Concepts.GraphQuery.GcBaselines
