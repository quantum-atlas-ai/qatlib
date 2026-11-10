/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Foundations.PureStateMath.Tensor
open Qatlib.Foundations.PureStateMath
open Qatlib

namespace Qatlib.Foundations.QueryWordCore.Circuit

open Matrix

set_option linter.unusedSectionVars false

variable {I : Type*} [Fintype I] [DecidableEq I]

inductive Step (I : Type*) where
  | gate : Matrix I I ℂ → Step I
  | query : Step I

abbrev Circuit (I : Type*) := List (Step I)

def IsUnitaryCircuit (C : Circuit I) : Prop :=
  ∀ U : Matrix I I ℂ, Step.gate U ∈ C → U ∈ Matrix.unitaryGroup I ℂ

@[simp] theorem isUnitaryCircuit_nil : IsUnitaryCircuit ([] : Circuit I) := by
  intro U hU
  simp at hU

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

@[simp] theorem isUnitaryCircuit_query (C : Circuit I) :
    IsUnitaryCircuit (Step.query :: C) ↔ IsUnitaryCircuit C := by
  constructor
  · intro h U hU
    exact h U (List.mem_cons_of_mem _ hU)
  · intro h U hU
    rcases List.mem_cons.mp hU with hU | hU
    · cases hU
    · exact h U hU

@[simp] theorem isUnitaryCircuit_append (C D : Circuit I) :
    IsUnitaryCircuit (C ++ D) ↔ IsUnitaryCircuit C ∧ IsUnitaryCircuit D := by
  constructor
  · intro h
    exact ⟨fun U hU => h U (List.mem_append.mpr (Or.inl hU)),
      fun U hU => h U (List.mem_append.mpr (Or.inr hU))⟩
  · rintro ⟨hC, hD⟩ U hU
    exact (List.mem_append.mp hU).elim (hC U) (hD U)

def QueryCount : Circuit I → ℕ
  | [] => 0
  | Step.query :: C => QueryCount C + 1
  | Step.gate _ :: C => QueryCount C

def GateCount : Circuit I → ℕ
  | [] => 0
  | Step.gate _ :: C => GateCount C + 1
  | Step.query :: C => GateCount C

def Size (C : Circuit I) : ℕ := C.length

noncomputable def Run (oracle : Matrix I I ℂ) : Circuit I → QState I → QState I
  | [], ψ => ψ
  | Step.gate U :: C, ψ => Run oracle C (ApplyGate U ψ)
  | Step.query :: C, ψ => Run oracle C (ApplyGate oracle ψ)

def RepeatCircuit (C : Circuit I) : ℕ → Circuit I
  | 0 => []
  | k + 1 => C ++ RepeatCircuit C k

theorem IsUnitaryCircuit.repeatCircuit {C : Circuit I} (hC : IsUnitaryCircuit C) (k : ℕ) :
    IsUnitaryCircuit (RepeatCircuit C k) := by
  induction k with
  | zero => exact isUnitaryCircuit_nil
  | succ k ih => exact (isUnitaryCircuit_append C (RepeatCircuit C k)).mpr ⟨hC, ih⟩

@[simp] theorem queryCount_nil : QueryCount ([] : Circuit I) = 0 := rfl

@[simp] theorem queryCount_query (C : Circuit I) :
    QueryCount (Step.query :: C) = QueryCount C + 1 := rfl

@[simp] theorem queryCount_gate (U : Matrix I I ℂ) (C : Circuit I) :
    QueryCount (Step.gate U :: C) = QueryCount C := rfl

@[simp] theorem gateCount_nil : GateCount ([] : Circuit I) = 0 := rfl

@[simp] theorem gateCount_gate (U : Matrix I I ℂ) (C : Circuit I) :
    GateCount (Step.gate U :: C) = GateCount C + 1 := rfl

@[simp] theorem gateCount_query (C : Circuit I) :
    GateCount (Step.query :: C) = GateCount C := rfl

@[simp] theorem size_nil : Size ([] : Circuit I) = 0 := rfl

@[simp] theorem size_cons (s : Step I) (C : Circuit I) : Size (s :: C) = Size C + 1 := rfl

@[simp] theorem run_nil (oracle : Matrix I I ℂ) (ψ : QState I) : Run oracle [] ψ = ψ := rfl

@[simp] theorem run_gate (oracle U : Matrix I I ℂ) (C : Circuit I) (ψ : QState I) :
    Run oracle (Step.gate U :: C) ψ = Run oracle C (ApplyGate U ψ) := rfl

@[simp] theorem run_query (oracle : Matrix I I ℂ) (C : Circuit I) (ψ : QState I) :
    Run oracle (Step.query :: C) ψ = Run oracle C (ApplyGate oracle ψ) := rfl

theorem queryCount_append (C D : Circuit I) :
    QueryCount (C ++ D) = QueryCount C + QueryCount D := by
  induction C with
  | nil => simp
  | cons s C ih => cases s <;> simp [ih, Nat.add_right_comm]

theorem gateCount_append (C D : Circuit I) :
    GateCount (C ++ D) = GateCount C + GateCount D := by
  induction C with
  | nil => simp [GateCount]
  | cons s C ih => cases s <;> simp [GateCount, ih, Nat.add_right_comm]

theorem size_append (C D : Circuit I) : Size (C ++ D) = Size C + Size D :=
  List.length_append

theorem queryCount_repeatCircuit (C : Circuit I) (k : ℕ) :
    QueryCount (RepeatCircuit C k) = k * QueryCount C := by
  induction k with
  | zero => simp [RepeatCircuit]
  | succ k ih => simp [RepeatCircuit, queryCount_append, ih, Nat.succ_mul, Nat.add_comm]

theorem gateCount_repeatCircuit (C : Circuit I) (k : ℕ) :
    GateCount (RepeatCircuit C k) = k * GateCount C := by
  induction k with
  | zero => simp [RepeatCircuit]
  | succ k ih => simp [RepeatCircuit, gateCount_append, ih, Nat.succ_mul, Nat.add_comm]

theorem size_repeatCircuit (C : Circuit I) (k : ℕ) :
    Size (RepeatCircuit C k) = k * Size C := by
  induction k with
  | zero => simp [RepeatCircuit, Size]
  | succ k ih => simp [RepeatCircuit, size_append, ih, Nat.succ_mul, Nat.add_comm]

theorem run_append (oracle : Matrix I I ℂ) (C D : Circuit I) (ψ : QState I) :
    Run oracle (C ++ D) ψ = Run oracle D (Run oracle C ψ) := by
  induction C generalizing ψ with
  | nil => rfl
  | cons s C ih => cases s <;> simp only [List.cons_append, Run, ih]

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

theorem conjTranspose_mem_unitaryGroup {U : Matrix I I ℂ}
    (hU : U ∈ Matrix.unitaryGroup I ℂ) : Uᴴ ∈ Matrix.unitaryGroup I ℂ := by
  rw [← Matrix.star_eq_conjTranspose]
  exact Unitary.star_mem hU

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

theorem IsUnitaryCircuit.normalized_run {C : Circuit I} (hC : IsUnitaryCircuit C)
    {oracle : Matrix I I ℂ} (horacle : oracle ∈ Matrix.unitaryGroup I ℂ)
    {ψ : QState I} (hψ : Normalized ψ) : Normalized (Run oracle C ψ) :=
  Qatlib.Foundations.QueryWordCore.Circuit.normalized_run oracle horacle C hC hψ

noncomputable def LiftCircuit : Circuit I → Circuit (I × Bool)
  | [] => []
  | Step.gate U :: C => Step.gate (LiftGate U) :: LiftCircuit C
  | Step.query :: C => Step.query :: LiftCircuit C

@[simp] theorem liftCircuit_nil : LiftCircuit ([] : Circuit I) = [] := rfl

@[simp] theorem liftCircuit_gate (U : Matrix I I ℂ) (C : Circuit I) :
    LiftCircuit (Step.gate U :: C) = Step.gate (LiftGate U) :: LiftCircuit C := rfl

@[simp] theorem liftCircuit_query (C : Circuit I) :
    LiftCircuit (Step.query :: C) = Step.query :: LiftCircuit C := rfl

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

theorem queryCount_liftCircuit (C : Circuit I) : QueryCount (LiftCircuit C) = QueryCount C := by
  induction C with
  | nil => rfl
  | cons s C ih => cases s <;> simp [ih]

theorem gateCount_liftCircuit (C : Circuit I) : GateCount (LiftCircuit C) = GateCount C := by
  induction C with
  | nil => rfl
  | cons s C ih => cases s <;> simp [ih]

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

noncomputable def cyclicFiberGate {n : ℕ} (gates : Fin n → Matrix I I ℂ)
    (p : Fin (2 * n + 1)) : Matrix I I ℂ :=
  if h1 : p.val < n then gates ⟨p.val, h1⟩
  else if h2 : n < p.val then (gates ⟨2 * n - p.val, by have := p.isLt; omega⟩)ᴴ
  else 1

theorem cyclicFiberGate_of_lt {n : ℕ} (gates : Fin n → Matrix I I ℂ) (m : ℕ)
    (hm : m < n) (hmM : m < 2 * n + 1) :
    cyclicFiberGate gates (⟨m, hmM⟩ : Fin (2 * n + 1)) = gates ⟨m, hm⟩ := by
  unfold cyclicFiberGate
  exact dif_pos hm
end Qatlib.Foundations.QueryWordCore.Circuit
