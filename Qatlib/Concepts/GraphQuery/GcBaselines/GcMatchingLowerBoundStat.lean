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

def GcMatchingLowerBound : Prop :=
  ∀ (n : ℕ) (W : Type) [Fintype W] [DecidableEq W]
    (C : Circuit ((Fin n × Bool) × W)) (ψ : QState ((Fin n × Bool) × W))
    (E : Finset ((Fin n × Bool) × W)),
    IsUnitaryCircuit C → Normalized ψ →
    (∀ x : Fin n → Bool,
      (2 / 3 : ℝ) ≤ MeasureProb (Run (workspaceBitOracle (W := W) x) C ψ)
        (if graphCollision (matchingAdj n) x then E else Eᶜ)) →
    (1 - 2 * Real.sqrt ((1 / 3 : ℝ) * (2 / 3 : ℝ))) * Real.sqrt ((n / 2 : ℕ) : ℝ) ≤
      2 * (QueryCount C : ℝ)

end Qatlib.Concepts.GraphQuery.GcBaselines
