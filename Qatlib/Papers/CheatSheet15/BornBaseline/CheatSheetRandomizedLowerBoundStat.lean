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

def CheatSheetRandomizedLowerBound : Prop :=
  ∀ (c M κ t T : ℕ) (hκ : 0 < κ)
    (dom : (Fin M → Bool) → Prop) (g : (Fin M → Bool) → Bool)
    (φ : (Fin M → Bool) → (Fin κ → Bool) → Bool)
    (D₀ D₁ : PMF (Fin M → Bool))
    (A : PMF (BoolQueryTree (CheatSheetIndex c M κ) Bool)),
    IsCertifying M κ hκ dom g φ →
    (∀ x, D₀ x ≠ 0 → dom x ∧ g x = false) →
    (∀ x, D₁ x ≠ 0 → dom x ∧ g x = true) →
    (∀ P : PMF (BoolQueryTree (Fin M) Bool),
      Qatlib.Concepts.QueryComplexity.DegreeMethod.BoolQueryTree.BoundedQueries P t →
        DistAdvantage (Q := Fin M) P D₀ D₁ ≤ 1 / (12 * (c : ℝ))) →
    6 * t ≤ 2 ^ c →
    Qatlib.Concepts.QueryComplexity.DegreeMethod.BoolQueryTree.BoundedQueries A T →
    SolvesTotalTree (cheatSheetFun (c := c) g φ) A (1 / 3) →
    t ≤ T

end Qatlib.Papers.CheatSheet15.BornBaseline
