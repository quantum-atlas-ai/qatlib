/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Foundations.QueryWordCore.Circuit
open Qatlib.Foundations.QueryWordCore.Circuit
open Qatlib.Foundations.PureStateMath
open Qatlib
open Qatlib

namespace Qatlib.Foundations.CircuitReversal.ReversalAlgebra

open Matrix

set_option autoImplicit false
set_option linter.unusedSectionVars false

variable {I : Type*} [Fintype I] [DecidableEq I]

noncomputable def reverseStep : Step I → Step I
  | Step.gate U => Step.gate Uᴴ
  | Step.query => Step.query

noncomputable def ReverseCircuit (C : Circuit I) : Circuit I :=
  C.reverse.map reverseStep

@[simp] theorem reverseCircuit_nil : ReverseCircuit ([] : Circuit I) = [] := rfl

theorem reverseCircuit_cons (s : Step I) (C : Circuit I) :
    ReverseCircuit (s :: C) = ReverseCircuit C ++ [reverseStep s] := by
  simp [ReverseCircuit]

theorem gateCount_reverseCircuit (C : Circuit I) : GateCount (ReverseCircuit C) = GateCount C := by
  induction C with
  | nil => rfl
  | cons s C ih =>
    cases s with
    | gate U => rw [reverseCircuit_cons, gateCount_append, ih]; simp [reverseStep]
    | query => rw [reverseCircuit_cons, gateCount_append, ih]; simp [reverseStep]

theorem queryCount_reverseCircuit (C : Circuit I) : QueryCount (ReverseCircuit C) = QueryCount C := by
  induction C with
  | nil => rfl
  | cons s C ih =>
    cases s with
    | gate U => rw [reverseCircuit_cons, queryCount_append, ih]; simp [reverseStep]
    | query => rw [reverseCircuit_cons, queryCount_append, ih]; simp [reverseStep]

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
