/-
Copyright (c) 2026 Quantum Atlas Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quantum Atlas Contributors
-/

module

public import Qatlib.Papers.CheatSheet15.BornBaseline.CheatSheetFramework

@[expose] public section
open Qatlib.Concepts.BlockEncoding Qatlib.Concepts.BlockEncoding.Encoding Qatlib.Concepts.BlockEncoding.Postselection Qatlib.Concepts.BlockEncoding.Postselection.Encoding Qatlib.Foundations.BornMetrics.EventProbability Qatlib.Foundations.InstrumentCore.Measurement Qatlib.Foundations.InstrumentCore.ProjectiveMeasurement Qatlib.Foundations.InstrumentCore.ProjectiveMeasurementLaws Qatlib.Foundations.OperatorErrors.OperatorError Qatlib.Foundations.PureStateMath.BornBridge Qatlib.Foundations.PureStateMath Qatlib.Foundations.PureStateMath.Reflection Qatlib.Foundations.QueryWordCore.Circuit Qatlib.Concepts.QueryWordCore.QueryMachinery

open Qatlib.Foundations.PureStateMath

namespace Qatlib.Papers.KForrelation20.BornBaseline

open Qatlib.Papers.CheatSheet15.BornBaseline

open scoped Matrix

def ForrelationRange : Prop :=
  ∀ (N k : ℕ) (H : Matrix (Fin N) (Fin N) ℝ) (z : Fin k → Fin N → Bool),
    Hᵀ * H = 1 → |forrK k H z| ≤ 1
end Qatlib.Papers.KForrelation20.BornBaseline
