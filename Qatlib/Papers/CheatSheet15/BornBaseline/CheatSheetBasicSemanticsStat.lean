/-
Copyright (c) 2026 Quantum Atlas Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quantum Atlas Contributors
-/

module

public import Qatlib.Papers.CheatSheet15.BornBaseline.CheatSheetFramework

@[expose] public section
open Qatlib.Concepts.BlockEncoding Qatlib.Concepts.BlockEncoding.Encoding Qatlib.Concepts.BlockEncoding.Postselection Qatlib.Concepts.BlockEncoding.Postselection.Encoding Qatlib.Foundations.BornMetrics.EventProbability Qatlib.Foundations.InstrumentCore.Measurement Qatlib.Foundations.InstrumentCore.ProjectiveMeasurement Qatlib.Foundations.InstrumentCore.ProjectiveMeasurementLaws Qatlib.Foundations.OperatorErrors.OperatorError Qatlib.Foundations.PureStateMath.BornBridge Qatlib.Foundations.PureStateMath Qatlib.Foundations.PureStateMath.Reflection Qatlib.Foundations.QueryWordCore.Circuit Qatlib.Concepts.QueryWordCore.QueryMachinery

namespace Qatlib.Papers.CheatSheet15.BornBaseline

def CheatSheetBasicSemantics : Prop :=
  ∀ (c M κ : ℕ) (g : (Fin M → Bool) → Bool) (φ : (Fin M → Bool) → (Fin κ → Bool) → Bool),
    (∀ x, φ x (fun _ => false) = false) →
      (0 < c → cheatSheetFun (c := c) g φ (fun _ => false) = false)
        ∧ ∀ (z : CheatSheetIndex c M κ → Bool) (ℓ : Fin (2 ^ c)),
            ℓ = sheetIndex (fun i => g (cheatBlock z i)) →
            (∀ i : Fin c, φ (cheatBlock z i) (cheatCert z ℓ i) = true) →
            cheatSheetFun (c := c) g φ z = true

end Qatlib.Papers.CheatSheet15.BornBaseline
