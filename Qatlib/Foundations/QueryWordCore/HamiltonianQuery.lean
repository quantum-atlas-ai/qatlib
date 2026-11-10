/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Foundations.PureStateMath.Qubit
open Qatlib.Foundations.PureStateMath
open Qatlib

namespace Qatlib.Foundations.QueryWordCore.HamiltonianQuery

inductive HamiltonianQueryStep (I : Type*) where
  | gate : Matrix I I ℂ → HamiltonianQueryStep I
  | evolve : ℝ → HamiltonianQueryStep I

variable {I : Type*}

def HamiltonianQueryCount : List (HamiltonianQueryStep I) → ℕ
  | [] => 0
  | .gate _ :: rest => HamiltonianQueryCount rest
  | .evolve _ :: rest => 1 + HamiltonianQueryCount rest

noncomputable def HamiltonianEvolutionTime : List (HamiltonianQueryStep I) → ℝ
  | [] => 0
  | .gate _ :: rest => HamiltonianEvolutionTime rest
  | .evolve t :: rest => |t| + HamiltonianEvolutionTime rest

variable [Fintype I] [DecidableEq I]

noncomputable def HamiltonianQueryRun (H : Matrix I I ℂ) :
    List (HamiltonianQueryStep I) → QState I → QState I
  | [], ψ => ψ
  | .gate U :: rest, ψ => HamiltonianQueryRun H rest (ApplyGate U ψ)
  | .evolve t :: rest, ψ =>
      HamiltonianQueryRun H rest (ApplyGate (HamiltonianEvolution H t) ψ)

def HamiltonianQueryValid (program : List (HamiltonianQueryStep I)) : Prop :=
  ∀ U, HamiltonianQueryStep.gate U ∈ program → U ∈ Matrix.unitaryGroup I ℂ

noncomputable def ComponentEvolution (L : ℕ)
    (terms : Fin L → Matrix I I ℂ) (time : ℝ) :
    Matrix (Fin L × I) (Fin L × I) ℂ :=
  fun row col => if row.1 = col.1 then
    HamiltonianEvolution (terms row.1) time row.2 col.2 else 0

omit [Fintype I] [DecidableEq I] in

theorem hamiltonianQueryCount_append (left right : List (HamiltonianQueryStep I)) :
    HamiltonianQueryCount (left ++ right) =
      HamiltonianQueryCount left + HamiltonianQueryCount right := by
  induction left with
  | nil => simp [HamiltonianQueryCount]
  | cons step rest ih => cases step <;> simp [HamiltonianQueryCount, ih, Nat.add_assoc]

omit [Fintype I] [DecidableEq I] in

theorem hamiltonianEvolutionTime_nonneg (program : List (HamiltonianQueryStep I)) :
    0 ≤ HamiltonianEvolutionTime program := by
  induction program with
  | nil => exact le_rfl
  | cons step rest ih =>
    cases step with
    | gate _ => exact ih
    | evolve t => exact add_nonneg (abs_nonneg t) ih

end Qatlib.Foundations.QueryWordCore.HamiltonianQuery
