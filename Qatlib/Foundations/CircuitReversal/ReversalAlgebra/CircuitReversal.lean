/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Foundations.QueryWordCore.Circuit

/-!
# Reversing oracle circuits

Defines `reverseStep` by taking adjoints of fixed gates while preserving oracle queries, and
`ReverseCircuit` by reversing the resulting word. Reversal preserves gate and query counts and
the unitary-circuit predicate.

For a Hermitian unitary oracle, `run_reverseCircuit_run` proves restoration of every input
state. This is a formal circuit-inversion construction in the setting of [NielsenChuang2010].

## Main statements

* `ReverseCircuit`: Reverses the order of circuit steps and applies `reverseStep` to each step.
* `queryCount_reverseCircuit`: Circuit reversal preserves the number of oracle queries.
* `run_reverseCircuit_run`: For a Hermitian unitary oracle and a unitary circuit, running the
  reversed circuit after the original circuit restores every input state.

## References

* [Nielsen and Chuang, 2010][NielsenChuang2010]
-/

open Qatlib.Foundations.QueryWordCore.Circuit
open Qatlib.Foundations.PureStateMath
open Qatlib
open Qatlib

namespace Qatlib.Foundations.CircuitReversal.ReversalAlgebra

open Matrix

set_option autoImplicit false
set_option linter.unusedSectionVars false

variable {I : Type*} [Fintype I] [DecidableEq I]

/-- Reverses one circuit step by replacing a fixed gate with its conjugate transpose and leaving
an oracle query unchanged. -/
noncomputable def reverseStep : Step I → Step I
  | Step.gate U => Step.gate Uᴴ
  | Step.query => Step.query

/-- Reverses the order of circuit steps and applies `reverseStep` to each step. -/
noncomputable def ReverseCircuit (C : Circuit I) : Circuit I :=
  C.reverse.map reverseStep

/-- The reverse of the empty circuit is empty. -/
@[simp] theorem reverseCircuit_nil : ReverseCircuit ([] : Circuit I) = [] := rfl

/-- Reversing a circuit with an initial step appends the reversed step to the reversed tail. -/
theorem reverseCircuit_cons (s : Step I) (C : Circuit I) :
    ReverseCircuit (s :: C) = ReverseCircuit C ++ [reverseStep s] := by
  simp [ReverseCircuit]

/-- Circuit reversal preserves the number of fixed gates. -/
theorem gateCount_reverseCircuit (C : Circuit I) : GateCount (ReverseCircuit C) = GateCount C := by
  induction C with
  | nil => rfl
  | cons s C ih =>
    cases s with
    | gate U => rw [reverseCircuit_cons, gateCount_append, ih]; simp [reverseStep]
    | query => rw [reverseCircuit_cons, gateCount_append, ih]; simp [reverseStep]

/-- Circuit reversal preserves the number of oracle queries. -/
theorem queryCount_reverseCircuit (C : Circuit I) : QueryCount (ReverseCircuit C) = QueryCount C := by
  induction C with
  | nil => rfl
  | cons s C ih =>
    cases s with
    | gate U => rw [reverseCircuit_cons, queryCount_append, ih]; simp [reverseStep]
    | query => rw [reverseCircuit_cons, queryCount_append, ih]; simp [reverseStep]

/-- The reverse of a unitary circuit is unitary. -/
theorem isUnitaryCircuit_reverseCircuit {C : Circuit I} (hC : IsUnitaryCircuit C) :
    IsUnitaryCircuit (ReverseCircuit C) := by
  induction C with
  | nil => exact isUnitaryCircuit_nil
  | cons s C ih =>
    cases s with
    | gate U =>
      rw [reverseCircuit_cons, isUnitaryCircuit_append]
      refine ⟨ih (fun V hV => hC V (List.mem_cons_of_mem _ hV)), ?_⟩
      show IsUnitaryCircuit [Step.gate Uᴴ]
      rw [isUnitaryCircuit_gate]
      exact ⟨conjTranspose_mem_unitaryGroup (hC U List.mem_cons_self), isUnitaryCircuit_nil⟩
    | query =>
      rw [reverseCircuit_cons, isUnitaryCircuit_append]
      exact ⟨ih (fun V hV => hC V (List.mem_cons_of_mem _ hV)),
        (isUnitaryCircuit_query []).mpr isUnitaryCircuit_nil⟩

/-- For a Hermitian unitary oracle and a unitary circuit, running the reversed circuit after the
original circuit restores every input state. -/
theorem run_reverseCircuit_run (O : Matrix I I ℂ) (hO : O ∈ Matrix.unitaryGroup I ℂ)
    (hOH : Oᴴ = O) (C : Circuit I) (hC : IsUnitaryCircuit C) (ψ : QState I) :
    Run O (ReverseCircuit C) (Run O C ψ) = ψ := by
  revert hC
  induction C generalizing ψ with
  | nil => intro _; rfl
  | cons s C ih =>
    intro hC
    cases s with
    | gate U =>
      have hU : U ∈ Matrix.unitaryGroup I ℂ := hC U List.mem_cons_self
      have hC' : IsUnitaryCircuit C := fun V hV => hC V (List.mem_cons_of_mem _ hV)
      have hUU : Uᴴ * U = 1 := by
        rw [Matrix.mem_unitaryGroup_iff', Matrix.star_eq_conjTranspose] at hU
        exact hU
      rw [reverseCircuit_cons, run_append, run_gate, ih (ApplyGate U ψ) hC']
      show ApplyGate Uᴴ (ApplyGate U ψ) = ψ
      rw [← applyGate_mul, hUU, applyGate_one]
    | query =>
      have hC' : IsUnitaryCircuit C := fun V hV => hC V (List.mem_cons_of_mem _ hV)
      have hOU : Oᴴ * O = 1 := by
        rw [Matrix.mem_unitaryGroup_iff', Matrix.star_eq_conjTranspose] at hO
        exact hO
      have hOO : O * O = 1 := by rw [hOH] at hOU; exact hOU
      rw [reverseCircuit_cons, run_append, run_query, ih (ApplyGate O ψ) hC']
      show ApplyGate O (ApplyGate O ψ) = ψ
      rw [← applyGate_mul, hOO, applyGate_one]

end Qatlib.Foundations.CircuitReversal.ReversalAlgebra
