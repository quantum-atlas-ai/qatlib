/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Foundations.PureStateMath.Tensor

/-!
# Query circuits and resource counts

This module defines `Circuit` as a list of explicit gates and oracle queries, with left-to-right
execution `Run`. It tracks queries, explicit gates, and total size, and proves how these
quantities behave under concatenation, repetition, and extension by a Boolean register. This
implements the circuit bookkeeping used in the quantum query model [BealsEtAl2001].

## Main statements

* `run_append`: concatenation agrees with successive execution.
* `normalized_run`: unitary gates and oracle preserve normalization.
* `run_eq_of_queryCount_eq_zero`: circuits without queries are independent of the oracle.
* `queryCount_liftCircuit`: Boolean-register extension preserves the query count.

## References

* [Beals et al., 2001][BealsEtAl2001]
-/

open Qatlib.Foundations.PureStateMath
open Qatlib

namespace Qatlib.Foundations.QueryWordCore.Circuit

open Matrix

set_option linter.unusedSectionVars false

variable {I : Type*} [Fintype I] [DecidableEq I]

/-- A circuit instruction consisting of either an explicit complex matrix gate or an oracle
query. -/
inductive Step (I : Type*) where
  | gate : Matrix I I ℂ → Step I
  | query : Step I

/-- A finite list of gate and query instructions in execution order. -/
abbrev Circuit (I : Type*) := List (Step I)

/-- The predicate that every explicit matrix gate occurring in a circuit is unitary. -/
def IsUnitaryCircuit (C : Circuit I) : Prop :=
  ∀ U : Matrix I I ℂ, Step.gate U ∈ C → U ∈ Matrix.unitaryGroup I ℂ

/-- The empty circuit satisfies `IsUnitaryCircuit`. -/
@[simp] theorem isUnitaryCircuit_nil : IsUnitaryCircuit ([] : Circuit I) := by
  intro U hU
  simp at hU

/-- Prepending an explicit gate gives a unitary circuit exactly when the gate is unitary and the
remaining circuit is unitary. -/
@[simp] theorem isUnitaryCircuit_gate (U : Matrix I I ℂ) (C : Circuit I) :
    IsUnitaryCircuit (Step.gate U :: C) ↔
      U ∈ Matrix.unitaryGroup I ℂ ∧ IsUnitaryCircuit C := by
  constructor
  · intro h
    exact ⟨h U List.mem_cons_self, fun V hV => h V (List.mem_cons_of_mem _ hV)⟩
  · rintro ⟨hU, hC⟩ V hV
    rcases List.mem_cons.mp hV with hV | hV
    · cases hV
      exact hU
    · exact hC V hV

/-- Prepending an oracle query preserves the predicate `IsUnitaryCircuit`. -/
@[simp] theorem isUnitaryCircuit_query (C : Circuit I) :
    IsUnitaryCircuit (Step.query :: C) ↔ IsUnitaryCircuit C := by
  constructor
  · intro h U hU
    exact h U (List.mem_cons_of_mem _ hU)
  · intro h U hU
    rcases List.mem_cons.mp hU with hU | hU
    · cases hU
    · exact h U hU

/-- A concatenation is a unitary circuit exactly when both constituent circuits are unitary. -/
@[simp] theorem isUnitaryCircuit_append (C D : Circuit I) :
    IsUnitaryCircuit (C ++ D) ↔ IsUnitaryCircuit C ∧ IsUnitaryCircuit D := by
  constructor
  · intro h
    exact ⟨fun U hU => h U (List.mem_append.mpr (Or.inl hU)),
      fun U hU => h U (List.mem_append.mpr (Or.inr hU))⟩
  · rintro ⟨hC, hD⟩ U hU
    exact (List.mem_append.mp hU).elim (hC U) (hD U)

/-- The number of oracle-query instructions in a circuit. -/
def QueryCount : Circuit I → ℕ
  | [] => 0
  | Step.query :: C => QueryCount C + 1
  | Step.gate _ :: C => QueryCount C

/-- The number of explicit matrix-gate instructions in a circuit. -/
def GateCount : Circuit I → ℕ
  | [] => 0
  | Step.gate _ :: C => GateCount C + 1
  | Step.query :: C => GateCount C

/-- The total number of instructions in a circuit. -/
def Size (C : Circuit I) : ℕ := C.length

/-- Execute a circuit from left to right on a state, substituting `oracle` for each query
instruction. -/
noncomputable def Run (oracle : Matrix I I ℂ) : Circuit I → QState I → QState I
  | [], ψ => ψ
  | Step.gate U :: C, ψ => Run oracle C (ApplyGate U ψ)
  | Step.query :: C, ψ => Run oracle C (ApplyGate oracle ψ)

/-- Concatenate `k` copies of a circuit, with zero copies giving the empty circuit. -/
def RepeatCircuit (C : Circuit I) : ℕ → Circuit I
  | 0 => []
  | k + 1 => C ++ RepeatCircuit C k

/-- Repeating a unitary circuit preserves `IsUnitaryCircuit`. -/
theorem IsUnitaryCircuit.repeatCircuit {C : Circuit I} (hC : IsUnitaryCircuit C) (k : ℕ) :
    IsUnitaryCircuit (RepeatCircuit C k) := by
  induction k with
  | zero => exact isUnitaryCircuit_nil
  | succ k ih => exact (isUnitaryCircuit_append C (RepeatCircuit C k)).mpr ⟨hC, ih⟩

/-- The empty circuit makes zero oracle queries. -/
@[simp] theorem queryCount_nil : QueryCount ([] : Circuit I) = 0 := rfl

/-- Prepending an oracle-query instruction increases the query count by one. -/
@[simp] theorem queryCount_query (C : Circuit I) :
    QueryCount (Step.query :: C) = QueryCount C + 1 := rfl

/-- Prepending an explicit matrix gate leaves the query count unchanged. -/
@[simp] theorem queryCount_gate (U : Matrix I I ℂ) (C : Circuit I) :
    QueryCount (Step.gate U :: C) = QueryCount C := rfl

/-- The empty circuit contains zero explicit gates. -/
@[simp] theorem gateCount_nil : GateCount ([] : Circuit I) = 0 := rfl

/-- Prepending an explicit matrix gate increases the gate count by one. -/
@[simp] theorem gateCount_gate (U : Matrix I I ℂ) (C : Circuit I) :
    GateCount (Step.gate U :: C) = GateCount C + 1 := rfl

/-- Prepending an oracle query leaves the explicit gate count unchanged. -/
@[simp] theorem gateCount_query (C : Circuit I) :
    GateCount (Step.query :: C) = GateCount C := rfl

/-- The empty circuit has size zero. -/
@[simp] theorem size_nil : Size ([] : Circuit I) = 0 := rfl

/-- Prepending any instruction increases circuit size by one. -/
@[simp] theorem size_cons (s : Step I) (C : Circuit I) : Size (s :: C) = Size C + 1 := rfl

/-- Executing the empty circuit returns the input state. -/
@[simp] theorem run_nil (oracle : Matrix I I ℂ) (ψ : QState I) : Run oracle [] ψ = ψ := rfl

/-- Executing a circuit beginning with an explicit gate applies that gate before executing the
remaining instructions. -/
@[simp] theorem run_gate (oracle U : Matrix I I ℂ) (C : Circuit I) (ψ : QState I) :
    Run oracle (Step.gate U :: C) ψ = Run oracle C (ApplyGate U ψ) := rfl

/-- Executing a circuit beginning with a query applies the oracle before executing the remaining
instructions. -/
@[simp] theorem run_query (oracle : Matrix I I ℂ) (C : Circuit I) (ψ : QState I) :
    Run oracle (Step.query :: C) ψ = Run oracle C (ApplyGate oracle ψ) := rfl

/-- Query counts add under circuit concatenation. -/
theorem queryCount_append (C D : Circuit I) :
    QueryCount (C ++ D) = QueryCount C + QueryCount D := by
  induction C with
  | nil => simp
  | cons s C ih => cases s <;> simp [ih, Nat.add_right_comm]

/-- Explicit gate counts add under circuit concatenation. -/
theorem gateCount_append (C D : Circuit I) :
    GateCount (C ++ D) = GateCount C + GateCount D := by
  induction C with
  | nil => simp [GateCount]
  | cons s C ih => cases s <;> simp [GateCount, ih, Nat.add_right_comm]

/-- Circuit sizes add under concatenation. -/
theorem size_append (C D : Circuit I) : Size (C ++ D) = Size C + Size D :=
  List.length_append

/-- Repeating a circuit `k` times multiplies its query count by `k`. -/
theorem queryCount_repeatCircuit (C : Circuit I) (k : ℕ) :
    QueryCount (RepeatCircuit C k) = k * QueryCount C := by
  induction k with
  | zero => simp [RepeatCircuit]
  | succ k ih => simp [RepeatCircuit, queryCount_append, ih, Nat.succ_mul, Nat.add_comm]

/-- Repeating a circuit `k` times multiplies its explicit gate count by `k`. -/
theorem gateCount_repeatCircuit (C : Circuit I) (k : ℕ) :
    GateCount (RepeatCircuit C k) = k * GateCount C := by
  induction k with
  | zero => simp [RepeatCircuit]
  | succ k ih => simp [RepeatCircuit, gateCount_append, ih, Nat.succ_mul, Nat.add_comm]

/-- Repeating a circuit `k` times multiplies its size by `k`. -/
theorem size_repeatCircuit (C : Circuit I) (k : ℕ) :
    Size (RepeatCircuit C k) = k * Size C := by
  induction k with
  | zero => simp [RepeatCircuit, Size]
  | succ k ih => simp [RepeatCircuit, size_append, ih, Nat.succ_mul, Nat.add_comm]

/-- Executing a concatenation runs its first circuit and then its second circuit. -/
theorem run_append (oracle : Matrix I I ℂ) (C D : Circuit I) (ψ : QState I) :
    Run oracle (C ++ D) ψ = Run oracle D (Run oracle C ψ) := by
  induction C generalizing ψ with
  | nil => rfl
  | cons s C ih => cases s <;> simp only [List.cons_append, Run, ih]

/-- Execution of a circuit with zero queries is independent of the chosen oracle matrix. -/
theorem run_eq_of_queryCount_eq_zero (oracle oracle' : Matrix I I ℂ) :
    ∀ (C : Circuit I), QueryCount C = 0 → ∀ (ψ : QState I),
      Run oracle C ψ = Run oracle' C ψ := by
  intro C
  induction C with
  | nil => intro _ ψ; rfl
  | cons s C ih =>
    cases s with
    | gate U =>
      intro h ψ
      exact ih h (ApplyGate U ψ)
    | query =>
      intro h ψ
      simp [QueryCount] at h

/-- The conjugate transpose of a unitary matrix is unitary. -/
theorem conjTranspose_mem_unitaryGroup {U : Matrix I I ℂ}
    (hU : U ∈ Matrix.unitaryGroup I ℂ) : Uᴴ ∈ Matrix.unitaryGroup I ℂ := by
  rw [← Matrix.star_eq_conjTranspose]
  exact Unitary.star_mem hU

/-- Circuit execution preserves normalization when the oracle and every explicit gate are
unitary. -/
theorem normalized_run (oracle : Matrix I I ℂ) (horacle : oracle ∈ Matrix.unitaryGroup I ℂ)
    (C : Circuit I)
    (hgates : ∀ U : Matrix I I ℂ, Step.gate U ∈ C → U ∈ Matrix.unitaryGroup I ℂ)
    {ψ : QState I} (hψ : Normalized ψ) : Normalized (Run oracle C ψ) := by
  induction C generalizing ψ with
  | nil => exact hψ
  | cons s C ih =>
    cases s with
    | gate U =>
      exact ih (fun V hV => hgates V (List.mem_cons_of_mem _ hV))
        (normalized_applyGate (hgates U List.mem_cons_self) hψ)
    | query =>
      exact ih (fun V hV => hgates V (List.mem_cons_of_mem _ hV))
        (normalized_applyGate horacle hψ)

/-- A unitary circuit with a unitary oracle sends normalized input states to normalized output
states. -/
theorem IsUnitaryCircuit.normalized_run {C : Circuit I} (hC : IsUnitaryCircuit C)
    {oracle : Matrix I I ℂ} (horacle : oracle ∈ Matrix.unitaryGroup I ℂ)
    {ψ : QState I} (hψ : Normalized ψ) : Normalized (Run oracle C ψ) :=
  Qatlib.Foundations.QueryWordCore.Circuit.normalized_run oracle horacle C hC hψ

/-- Lift every explicit gate to an additional Boolean register while retaining query
instructions. -/
noncomputable def LiftCircuit : Circuit I → Circuit (I × Bool)
  | [] => []
  | Step.gate U :: C => Step.gate (LiftGate U) :: LiftCircuit C
  | Step.query :: C => Step.query :: LiftCircuit C

/-- Lifting the empty circuit gives the empty circuit. -/
@[simp] theorem liftCircuit_nil : LiftCircuit ([] : Circuit I) = [] := rfl

/-- Lifting a circuit beginning with `U` begins with `LiftGate U` and continues with the lifted
remaining circuit. -/
@[simp] theorem liftCircuit_gate (U : Matrix I I ℂ) (C : Circuit I) :
    LiftCircuit (Step.gate U :: C) = Step.gate (LiftGate U) :: LiftCircuit C := rfl

/-- Lifting a circuit beginning with a query retains that query and lifts the remaining circuit. -/
@[simp] theorem liftCircuit_query (C : Circuit I) :
    LiftCircuit (Step.query :: C) = Step.query :: LiftCircuit C := rfl

/-- Lifting a circuit preserves `IsUnitaryCircuit`. -/
theorem IsUnitaryCircuit.lift {C : Circuit I} (hC : IsUnitaryCircuit C) :
    IsUnitaryCircuit (LiftCircuit C) := by
  revert hC
  induction C with
  | nil => intro _; exact isUnitaryCircuit_nil
  | cons s C ih =>
    cases s with
    | gate U =>
      intro h
      obtain ⟨hU, hC⟩ := (isUnitaryCircuit_gate U C).mp h
      rw [liftCircuit_gate, isUnitaryCircuit_gate]
      exact ⟨liftGate_unitary hU, ih hC⟩
    | query =>
      intro h
      rw [liftCircuit_query, isUnitaryCircuit_query]
      exact ih ((isUnitaryCircuit_query C).mp h)

/-- Lifting a circuit preserves its query count. -/
theorem queryCount_liftCircuit (C : Circuit I) : QueryCount (LiftCircuit C) = QueryCount C := by
  induction C with
  | nil => rfl
  | cons s C ih => cases s <;> simp [ih]

/-- Lifting a circuit preserves its explicit gate count. -/
theorem gateCount_liftCircuit (C : Circuit I) : GateCount (LiftCircuit C) = GateCount C := by
  induction C with
  | nil => rfl
  | cons s C ih => cases s <;> simp [ih]

/-- Lifting a circuit preserves its total size. -/
theorem size_liftCircuit (C : Circuit I) : Size (LiftCircuit C) = Size C := by
  induction C with
  | nil => rfl
  | cons s C ih => cases s <;> simp [ih]

end Qatlib.Foundations.QueryWordCore.Circuit

open Matrix

set_option linter.unusedSectionVars false

variable {I : Type*} [Fintype I] [DecidableEq I]
namespace Qatlib.Foundations.QueryWordCore.Circuit
open Matrix
set_option linter.unusedSectionVars false
variable {I : Type*} [Fintype I] [DecidableEq I]

/-- Select the forward gates, an identity at position `n`, and the conjugate-transposed gates in
reverse order on `Fin (2 * n + 1)`. -/
noncomputable def cyclicFiberGate {n : ℕ} (gates : Fin n → Matrix I I ℂ)
    (p : Fin (2 * n + 1)) : Matrix I I ℂ :=
  if h1 : p.val < n then gates ⟨p.val, h1⟩
  else if h2 : n < p.val then (gates ⟨2 * n - p.val, by have := p.isLt; omega⟩)ᴴ
  else 1

/-- At any position strictly below `n`, `cyclicFiberGate` equals the corresponding forward gate. -/
theorem cyclicFiberGate_of_lt {n : ℕ} (gates : Fin n → Matrix I I ℂ) (m : ℕ)
    (hm : m < n) (hmM : m < 2 * n + 1) :
    cyclicFiberGate gates (⟨m, hmM⟩ : Fin (2 * n + 1)) = gates ⟨m, hm⟩ := by
  unfold cyclicFiberGate
  exact dif_pos hm
end Qatlib.Foundations.QueryWordCore.Circuit
