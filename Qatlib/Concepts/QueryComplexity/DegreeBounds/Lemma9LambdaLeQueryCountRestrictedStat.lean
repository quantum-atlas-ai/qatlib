/-
Copyright (c) 2026 Quantum Atlas Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quantum Atlas Contributors
-/

module

public import Qatlib.Concepts.QueryComplexity.TriangleDegreeBounds.Support

@[expose] public section
set_option backward.isDefEq.respectTransparency false
open Qatlib.Concepts.QueryComplexity.TriangleDegreeBounds Qatlib.Concepts.BlockEncoding Qatlib.Concepts.BlockEncoding.Encoding Qatlib.Concepts.BlockEncoding.Postselection Qatlib.Concepts.BlockEncoding.Postselection.Encoding Qatlib.Foundations.BornMetrics.EventProbability Qatlib.Foundations.InstrumentCore.Measurement Qatlib.Foundations.InstrumentCore.ProjectiveMeasurement Qatlib.Foundations.InstrumentCore.ProjectiveMeasurementLaws Qatlib.Foundations.OperatorErrors.OperatorError Qatlib.Foundations.PureStateMath.BornBridge Qatlib.Foundations.PureStateMath Qatlib.Foundations.PureStateMath.Reflection Qatlib.Foundations.QueryWordCore.Circuit Qatlib.Concepts.QueryWordCore.QueryMachinery

open Qatlib.Foundations.QueryWordCore.Circuit

open Qatlib.Concepts.QueryWordCore.QueryMachinery

namespace Qatlib.Concepts.QueryComplexity.DegreeBounds

def Lemma9LambdaLeQueryCountRestricted : Prop :=
  ∀ (N : ℕ) (W : Type) [Fintype W] [DecidableEq W]
    (C : Qatlib.Foundations.QueryWordCore.Circuit.Circuit ((Fin N × Bool) × W))
    (ψ : Qatlib.Foundations.PureStateMath.QState ((Fin N × Bool) × W))
    (E : Finset ((Fin N × Bool) × W)) (f : (Fin N → Bool) → Bool),
    Qatlib.Foundations.QueryWordCore.Circuit.IsUnitaryCircuit C → Qatlib.Foundations.PureStateMath.Normalized ψ →
    (∀ g : Fin N → Bool,
      2 / 3 ≤ Qatlib.Foundations.PureStateMath.MeasureProb
        (Qatlib.Foundations.QueryWordCore.Circuit.Run (Qatlib.Concepts.QueryComplexity.AdversarySearch.workspaceBitOracle (W := W) g) C ψ)
        (if f g then E else Eᶜ)) →
    spectralSensitivity f ≤ 6 * (3 + 2 * Real.sqrt 2) * (Qatlib.Foundations.QueryWordCore.Circuit.QueryCount C : ℝ)

end Qatlib.Concepts.QueryComplexity.DegreeBounds
