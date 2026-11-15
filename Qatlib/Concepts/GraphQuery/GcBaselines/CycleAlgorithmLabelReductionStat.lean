/-
Copyright (c) 2026 Quantum Atlas Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quantum Atlas Contributors
-/

module

public import Qatlib.Concepts.GraphQuery.GcBaselines.GadgetOracleQuerySimulationStat

@[expose] public section
open Qatlib.Concepts.BlockEncoding Qatlib.Concepts.BlockEncoding.Encoding Qatlib.Concepts.BlockEncoding.Postselection Qatlib.Concepts.BlockEncoding.Postselection.Encoding Qatlib.Foundations.BornMetrics.EventProbability Qatlib.Foundations.InstrumentCore.Measurement Qatlib.Foundations.InstrumentCore.ProjectiveMeasurement Qatlib.Foundations.InstrumentCore.ProjectiveMeasurementLaws Qatlib.Foundations.OperatorErrors.OperatorError Qatlib.Foundations.PureStateMath.BornBridge Qatlib.Foundations.PureStateMath Qatlib.Foundations.PureStateMath.Reflection Qatlib.Foundations.QueryWordCore.Circuit Qatlib.Concepts.QueryWordCore.QueryMachinery

set_option autoImplicit false
open Qatlib.Foundations.QueryWordCore.Circuit
open Qatlib.Foundations.PureStateMath

open Qatlib.Concepts.QueryComplexity.AdversarySearch

namespace Qatlib.Concepts.GraphQuery.GcBaselines
open Matrix
open scoped Classical

def CycleAlgorithmLabelReduction : Prop :=
  ∀ (W : Type) [Fintype W] [DecidableEq W] (n : ℕ) (hn : 0 < n)
    (C : Circuit (GadgetHostRegister n W)) (ψ : QState (GadgetHostRegister n W))
    (E : Finset (GadgetHostRegister n W)),
    IsUnitaryCircuit C → Normalized ψ →
    (∀ A : GadgetSimpleAdj n,
      2/3 ≤ MeasureProb (Run (workspaceBitOracle (W := W) (gadgetOracleInput A)) C ψ)
        (if cycle5ThroughStation A.1 then E else Eᶜ)) →
    ∀ adj : Fin n → Fin n → Bool,
      IsUnitaryCircuit (gadgetCompileCircuit n hn adj C) ∧
      Normalized (TensorState (Ket (gadgetSourceZero n hn)) ψ) ∧
      QueryCount (gadgetCompileCircuit n hn adj C) = 2*QueryCount C ∧
      GateCount (gadgetCompileCircuit n hn adj C) = GateCount C+3*QueryCount C ∧
      ∀ x : Fin n → Fin n → Bool,
        2/3 ≤ MeasureProb (Run (workspaceBitOracle (W := GadgetHostRegister n W) (gadgetSourceLabels n x))
          (gadgetCompileCircuit n hn adj C) (TensorState (Ket (gadgetSourceZero n hn)) ψ))
            (Finset.univ ×ˢ (if gcOr adj x then E else Eᶜ))

end Qatlib.Concepts.GraphQuery.GcBaselines
