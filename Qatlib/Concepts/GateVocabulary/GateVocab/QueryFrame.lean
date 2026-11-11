/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Foundations.QueryWordCore.Circuit

/-!
# Two-sided query frames

`queryFrame` inserts the same matrix `B` immediately before and after each oracle query.
`queryFrame_run` identifies the resulting circuit execution with execution using oracle `B * O *
B`.

The transformation preserves the number of queries, adds two gates per query, and preserves
unitary-circuit legality when `B` is unitary. Its measurement identity follows the query-circuit
conventions of [NielsenChuang2010].

## Main statements

* `queryFrame_run`: identifies the framed execution on every input state.
* `queryFrame_gates`: counts the two additional gates per query.
* `queryFrame_readout`: identifies every event probability of the two executions.

## References

* [Nielsen and Chuang, 2010][NielsenChuang2010]
-/

set_option autoImplicit false
namespace Qatlib.Concepts.GateVocabulary.GateVocab
open Matrix
open Qatlib.Foundations.QueryWordCore.Circuit
open Qatlib.Foundations.PureStateMath
variable {I : Type}

/-- Inserts a gate with matrix `B` before and after each query, preserving all existing gate
steps. -/
def queryFrame (B : Matrix I I ℂ) : Circuit I → Circuit I
  | [] => []
  | Step.gate U :: C => Step.gate U :: queryFrame B C
  | Step.query :: C => Step.gate B :: Step.query :: Step.gate B :: queryFrame B C

/-- Running the framed circuit with oracle `O` equals running the original circuit with oracle
`B * O * B`. -/
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

/-- Framing each query preserves the circuit's query count. -/
theorem queryFrame_queries (B : Matrix I I ℂ) (C : Circuit I) :
    QueryCount (queryFrame B C) = QueryCount C := by
  induction C with
  | nil => rfl
  | cons step C ih => cases step <;> simp [queryFrame,QueryCount,ih]

/-- Framing each query adds exactly two gates per query to the circuit's gate count. -/
theorem queryFrame_gates (B : Matrix I I ℂ) (C : Circuit I) :
    GateCount (queryFrame B C) = GateCount C + 2*QueryCount C := by
  induction C with
  | nil => rfl
  | cons step C ih => cases step <;> simp [queryFrame,GateCount,QueryCount,ih] <;> omega

/-- If `B` is unitary, framing the queries of a unitary circuit gives a unitary circuit. -/
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

/-- Every measurement event has the same probability for the framed circuit with oracle `O` as
for the original circuit with oracle `B * O * B`. -/
theorem queryFrame_readout [Fintype I] (B O : Matrix I I ℂ) (C : Circuit I) (psi : QState I) (S : Finset I) :
    MeasureProb (Run O (queryFrame B C) psi) S = MeasureProb (Run (B*O*B) C psi) S := by
  rw [queryFrame_run]

end Qatlib.Concepts.GateVocabulary.GateVocab
