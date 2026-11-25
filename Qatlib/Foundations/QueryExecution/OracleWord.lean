/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Foundations.QueryWordCore.Circuit

@[expose] public section

/-!
# Reusable oracle-word execution bridges

This module packages the public finite query-word semantics into a small interface that can be
shared by paper consumers.  A word carries its unitary-gate obligation, sequential composition is
the circuit append operation, and controlled or iterated use is represented by a finite repetition
of the same word.  The execution equations expose the exact state evolution while the count
equations keep the query resource in the same orientation as the public circuit API.
-/

set_option autoImplicit false

open Qatlib
open Qatlib.Foundations.PureStateMath
open Qatlib.Foundations.QueryWordCore.Circuit

namespace Qatlib.Foundations.QueryExecution

variable {I : Type*} [Fintype I] [DecidableEq I]

/-- A finite oracle word together with the obligation that every explicit gate is unitary. -/
structure OracleWord (I : Type*) [Fintype I] [DecidableEq I] where
  circuit : Circuit I
  unitary : IsUnitaryCircuit circuit

/-- The number of oracle calls made by an oracle word. -/
def OracleWord.queryCount (w : OracleWord I) : ℕ :=
  QueryCount w.circuit

/-- Sequential composition of two oracle words. -/
def OracleWord.sequential (w₁ w₂ : OracleWord I) : OracleWord I where
  circuit := w₁.circuit ++ w₂.circuit
  unitary := (isUnitaryCircuit_append _ _).mpr ⟨w₁.unitary, w₂.unitary⟩

/-- The exact state produced by running an oracle word. -/
noncomputable def OracleWord.run (w : OracleWord I) (oracle : Matrix I I ℂ) (ψ : QState I) :
    QState I :=
  Run oracle w.circuit ψ

/-- Sequential execution is exact circuit execution in order. -/
theorem OracleWord.run_sequential (oracle : Matrix I I ℂ) (w₁ w₂ : OracleWord I)
    (ψ : QState I) :
    (w₁.sequential w₂).run oracle ψ = w₂.run oracle (w₁.run oracle ψ) := by
  exact run_append oracle w₁.circuit w₂.circuit ψ

/-- Sequential query counts add. -/
theorem OracleWord.queryCount_sequential (w₁ w₂ : OracleWord I) :
    (w₁.sequential w₂).queryCount = w₁.queryCount + w₂.queryCount := by
  exact queryCount_append w₁.circuit w₂.circuit

/-- Repeating a word `k` times is the standard finite iterated oracle execution. -/
def OracleWord.iterate (w : OracleWord I) (k : ℕ) : OracleWord I where
  circuit := RepeatCircuit w.circuit k
  unitary := IsUnitaryCircuit.repeatCircuit w.unitary k

/-- A controlled batch of `k` uses has the same resource law as `k` finite repetitions.

The control register is supplied by the consumer's circuit layer.  This bridge deliberately keeps
the resource statement independent of the concrete control encoding.
-/
def OracleWord.controlled (w : OracleWord I) (k : ℕ) : OracleWord I :=
  w.iterate k

/-- The recursive state evolution of an iterated word. -/
noncomputable def iterateRun (oracle : Matrix I I ℂ) (w : OracleWord I) : ℕ → QState I → QState I
  | 0, ψ => ψ
  | k + 1, ψ => iterateRun oracle w k (w.run oracle ψ)

/-- Iterated execution agrees definitionally with the public repeated circuit semantics. -/
theorem OracleWord.run_iterate (oracle : Matrix I I ℂ) (w : OracleWord I) (k : ℕ)
    (ψ : QState I) :
    (w.iterate k).run oracle ψ = iterateRun oracle w k ψ := by
  induction k generalizing ψ with
  | zero => rfl
  | succ k ih =>
      change Run oracle (RepeatCircuit w.circuit (k + 1)) ψ = iterateRun oracle w (k + 1) ψ
      rw [RepeatCircuit.eq_def, run_append]
      exact ih (w.run oracle ψ)

/-- Iterated query counts multiply by the number of repetitions. -/
theorem OracleWord.queryCount_iterate (w : OracleWord I) (k : ℕ) :
    (w.iterate k).queryCount = k * w.queryCount := by
  exact queryCount_repeatCircuit w.circuit k

/-- Controlled batches have the multiplicative query law inherited from iteration. -/
theorem OracleWord.queryCount_controlled (w : OracleWord I) (k : ℕ) :
    (w.controlled k).queryCount = k * w.queryCount := by
  exact w.queryCount_iterate k

/-- A zero-query word has oracle-independent state evolution. -/
theorem OracleWord.run_independent_of_oracle (w : OracleWord I)
    (hzero : w.queryCount = 0) (oracle oracle' : Matrix I I ℂ) (ψ : QState I) :
    w.run oracle ψ = w.run oracle' ψ := by
  exact run_eq_of_queryCount_eq_zero oracle oracle' w.circuit hzero ψ

end Qatlib.Foundations.QueryExecution
