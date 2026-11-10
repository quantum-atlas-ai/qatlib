/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Foundations.QueryWordCore.Circuit

set_option autoImplicit false
namespace Qatlib.Concepts.GateVocabulary.GateVocab
open Matrix
open Qatlib.Foundations.QueryWordCore.Circuit
open Qatlib.Foundations.PureStateMath
variable {I : Type}

def queryFrame (B : Matrix I I ℂ) : Circuit I → Circuit I
  | [] => []
  | Step.gate U :: C => Step.gate U :: queryFrame B C
  | Step.query :: C => Step.gate B :: Step.query :: Step.gate B :: queryFrame B C

theorem queryFrame_run [Fintype I] (B O : Matrix I I ℂ) (C : Circuit I) (psi : QState I) :
    Run O (queryFrame B C) psi = Run (B*O*B) C psi := by
  induction C generalizing psi with
  | nil => rfl
  | cons step C ih =>
    cases step with
    | gate U => exact ih (ApplyGate U psi)
    | query =>
      change Run O (queryFrame B C) (ApplyGate B (ApplyGate O (ApplyGate B psi))) =
        Run (B*O*B) C (ApplyGate (B*O*B) psi)
      rw [ih]
      congr 1
      change B *ᵥ (O *ᵥ (B *ᵥ psi)) = (B*O*B) *ᵥ psi
      simp only [Matrix.mulVec_mulVec,Matrix.mul_assoc]

theorem queryFrame_queries (B : Matrix I I ℂ) (C : Circuit I) :
    QueryCount (queryFrame B C) = QueryCount C := by
  induction C with
  | nil => rfl
  | cons step C ih => cases step <;> simp [queryFrame,QueryCount,ih]

theorem queryFrame_gates (B : Matrix I I ℂ) (C : Circuit I) :
    GateCount (queryFrame B C) = GateCount C + 2*QueryCount C := by
  induction C with
  | nil => rfl
  | cons step C ih => cases step <;> simp [queryFrame,GateCount,QueryCount,ih] <;> omega

theorem queryFrame_unitary [Fintype I] [DecidableEq I] (B : Matrix I I ℂ) (hB : B ∈ Matrix.unitaryGroup I ℂ)
    (C : Circuit I) (hC : IsUnitaryCircuit C) : IsUnitaryCircuit (queryFrame B C) := by
  induction C with
  | nil => simp [queryFrame]
  | cons step C ih =>
    cases step with
    | gate U =>
      have h := (isUnitaryCircuit_gate U C).mp hC
      simpa only [queryFrame,isUnitaryCircuit_gate] using And.intro h.1 (ih h.2)
    | query =>
      have h := (isUnitaryCircuit_query C).mp hC
      simpa only [queryFrame,isUnitaryCircuit_gate,isUnitaryCircuit_query] using
        And.intro hB (And.intro hB (ih h))

theorem queryFrame_readout [Fintype I] (B O : Matrix I I ℂ) (C : Circuit I) (psi : QState I) (S : Finset I) :
    MeasureProb (Run O (queryFrame B C) psi) S = MeasureProb (Run (B*O*B) C psi) S := by
  rw [queryFrame_run]

end Qatlib.Concepts.GateVocabulary.GateVocab
