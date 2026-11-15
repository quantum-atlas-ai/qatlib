/-
Copyright (c) 2026 Quantum Atlas Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quantum Atlas Contributors
-/

module

public import Qatlib.Papers.CheatSheet15.BornBaseline.CheatSheetFramework

@[expose] public section
open Qatlib.Concepts.BlockEncoding Qatlib.Concepts.BlockEncoding.Encoding Qatlib.Concepts.BlockEncoding.Postselection Qatlib.Concepts.BlockEncoding.Postselection.Encoding Qatlib.Foundations.BornMetrics.EventProbability Qatlib.Foundations.InstrumentCore.Measurement Qatlib.Foundations.InstrumentCore.ProjectiveMeasurement Qatlib.Foundations.InstrumentCore.ProjectiveMeasurementLaws Qatlib.Foundations.OperatorErrors.OperatorError Qatlib.Foundations.PureStateMath.BornBridge Qatlib.Foundations.PureStateMath Qatlib.Foundations.PureStateMath.Reflection Qatlib.Foundations.QueryWordCore.Circuit Qatlib.Concepts.QueryWordCore.QueryMachinery

open Qatlib.Concepts.QueryComplexity.DegreeMethod

namespace Qatlib.Papers.CheatSheet15.BornBaseline

def QueryTreeAgreementInvariance : Prop :=
  ∀ (Q : Type) [Fintype Q] [DecidableEq Q] (o₁ o₂ : Q → Bool) (B : Finset Q)
    (τ : BoolQueryTree Q Bool),
    (∀ q : Q, q ∉ B → o₁ q = o₂ q) →
    ((∃ q : Q, q ∈ B ∧ q ∈ queriesOf o₁ τ) ↔ ∃ q : Q, q ∈ B ∧ q ∈ queriesOf o₂ τ)
      ∧ ((¬ ∃ q : Q, q ∈ B ∧ q ∈ queriesOf o₁ τ) →
          (Qatlib.Concepts.QueryComplexity.DegreeMethod.BoolQueryTree.Run o₁ τ).1 = (Qatlib.Concepts.QueryComplexity.DegreeMethod.BoolQueryTree.Run o₂ τ).1)

end Qatlib.Papers.CheatSheet15.BornBaseline
