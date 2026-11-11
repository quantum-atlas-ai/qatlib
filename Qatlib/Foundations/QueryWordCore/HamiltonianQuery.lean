/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Foundations.PureStateMath.Qubit

/-!
# Hamiltonian query programs

This module defines `HamiltonianQueryStep` and `HamiltonianQueryRun` for programs interleaving
explicit gates with Hamiltonian evolution. `HamiltonianQueryCount` counts evolution calls,
`HamiltonianEvolutionTime` sums their absolute durations, and `ComponentEvolution` packages a
family of evolutions as a block-diagonal matrix. Hamiltonian oracle models are discussed in
[Mochon2007].

## Main statements

* `hamiltonianQueryCount_append`: evolution-call counts add under concatenation.
* `hamiltonianEvolutionTime_nonneg`: total absolute evolution time is nonnegative.

## References

* [Mochon, 2007][Mochon2007]
-/

open Qatlib.Foundations.PureStateMath
open Qatlib

namespace Qatlib.Foundations.QueryWordCore.HamiltonianQuery

/-- An instruction consisting of an explicit matrix gate or evolution under a supplied
Hamiltonian for a real time. -/
inductive HamiltonianQueryStep (I : Type*) where
  | gate : Matrix I I ℂ → HamiltonianQueryStep I
  | evolve : ℝ → HamiltonianQueryStep I

variable {I : Type*}

/-- Count the Hamiltonian-evolution instructions in a program, ignoring explicit gates. -/
def HamiltonianQueryCount : List (HamiltonianQueryStep I) → ℕ
  | [] => 0
  | .gate _ :: rest => HamiltonianQueryCount rest
  | .evolve _ :: rest => 1 + HamiltonianQueryCount rest

/-- The sum of the absolute evolution times in a Hamiltonian-query program. -/
noncomputable def HamiltonianEvolutionTime : List (HamiltonianQueryStep I) → ℝ
  | [] => 0
  | .gate _ :: rest => HamiltonianEvolutionTime rest
  | .evolve t :: rest => |t| + HamiltonianEvolutionTime rest

variable [Fintype I] [DecidableEq I]

/-- Execute gates and Hamiltonian evolutions in list order, using `exp (-itH)` for an evolution
instruction of duration `t`. -/
noncomputable def HamiltonianQueryRun (H : Matrix I I ℂ) :
    List (HamiltonianQueryStep I) → QState I → QState I
  | [], ψ => ψ
  | .gate U :: rest, ψ => HamiltonianQueryRun H rest (ApplyGate U ψ)
  | .evolve t :: rest, ψ =>
      HamiltonianQueryRun H rest (ApplyGate (HamiltonianEvolution H t) ψ)

/-- The predicate that all explicit gates occurring in a Hamiltonian-query program are unitary. -/
def HamiltonianQueryValid (program : List (HamiltonianQueryStep I)) : Prop :=
  ∀ U, HamiltonianQueryStep.gate U ∈ program → U ∈ Matrix.unitaryGroup I ℂ

/-- The block-diagonal matrix whose block indexed by `l` is evolution under `terms l` for the
specified time. -/
noncomputable def ComponentEvolution (L : ℕ)
    (terms : Fin L → Matrix I I ℂ) (time : ℝ) :
    Matrix (Fin L × I) (Fin L × I) ℂ :=
  fun row col => if row.1 = col.1 then
    HamiltonianEvolution (terms row.1) time row.2 col.2 else 0

omit [Fintype I] [DecidableEq I] in

/-- Hamiltonian-query counts add under concatenation of instruction lists. -/
theorem hamiltonianQueryCount_append (left right : List (HamiltonianQueryStep I)) :
    HamiltonianQueryCount (left ++ right) =
      HamiltonianQueryCount left + HamiltonianQueryCount right := by
  induction left with
  | nil => simp [HamiltonianQueryCount]
  | cons step rest ih => cases step <;> simp [HamiltonianQueryCount, ih, Nat.add_assoc]

omit [Fintype I] [DecidableEq I] in

/-- The total absolute evolution time of any Hamiltonian-query program is nonnegative. -/
theorem hamiltonianEvolutionTime_nonneg (program : List (HamiltonianQueryStep I)) :
    0 ≤ HamiltonianEvolutionTime program := by
  induction program with
  | nil => exact le_rfl
  | cons step rest ih =>
    cases step with
    | gate _ => exact ih
    | evolve t => exact add_nonneg (abs_nonneg t) ih

end Qatlib.Foundations.QueryWordCore.HamiltonianQuery
