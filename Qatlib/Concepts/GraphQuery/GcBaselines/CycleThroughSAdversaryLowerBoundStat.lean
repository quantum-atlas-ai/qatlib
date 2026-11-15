/-
Copyright (c) 2026 Quantum Atlas Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quantum Atlas Contributors
-/

module

public import Qatlib.Concepts.GraphQuery.GcBaselines.Section6Gadget

@[expose] public section
open Qatlib.Concepts.BlockEncoding Qatlib.Concepts.BlockEncoding.Encoding Qatlib.Concepts.BlockEncoding.Postselection Qatlib.Concepts.BlockEncoding.Postselection.Encoding Qatlib.Foundations.BornMetrics.EventProbability Qatlib.Foundations.InstrumentCore.Measurement Qatlib.Foundations.InstrumentCore.ProjectiveMeasurement Qatlib.Foundations.InstrumentCore.ProjectiveMeasurementLaws Qatlib.Foundations.OperatorErrors.OperatorError Qatlib.Foundations.PureStateMath.BornBridge Qatlib.Foundations.PureStateMath Qatlib.Foundations.PureStateMath.Reflection Qatlib.Foundations.QueryWordCore.Circuit Qatlib.Concepts.QueryWordCore.QueryMachinery

set_option autoImplicit false

open Qatlib.Foundations.QueryWordCore.Circuit
open Qatlib.Foundations.PureStateMath

open Qatlib.Concepts.GraphQuery.EdgeQuery
open Qatlib.Concepts.QueryComplexity.AdversarySearch

namespace Qatlib.Concepts.GraphQuery.GcBaselines

open Qatlib

def CycleThroughSAdversaryLowerBound : Prop :=
  ∀ (n : ℕ) (adj : Fin n → Fin n → Bool) (edges : Finset (Fin n × Fin n)),
    (∀ e ∈ edges, e.1 ≠ e.2) →
    (∀ e ∈ edges, (e.2, e.1) ∉ edges) →
    (∀ e ∈ edges, adj e.1 e.2 = true) →
    ∀ (W : Type) [Fintype W] [DecidableEq W]
      (C : Circuit ((Fin (gadgetAddrCount n) × Bool) × W))
      (ψ : QState ((Fin (gadgetAddrCount n) × Bool) × W))
      (E : Finset ((Fin (gadgetAddrCount n) × Bool) × W)),
      IsUnitaryCircuit C → Normalized ψ →
      (∀ S : GadgetSimpleAdj n,
        (2 / 3 : ℝ) ≤ MeasureProb
          (Run (workspaceBitOracle (W := W) (gadgetOracleInput S)) C ψ)
          (if cycle5ThroughStation S.1 then E else Eᶜ)) →
      (1 - 2 * Real.sqrt ((1 / 3 : ℝ) * (2 / 3 : ℝ))) * Real.sqrt ((n : ℝ) * (edges.card : ℝ)) ≤
        2 * (QueryCount C : ℝ) * Real.sqrt ((gcMaxDegree edges : ℕ) : ℝ)

end Qatlib.Concepts.GraphQuery.GcBaselines
