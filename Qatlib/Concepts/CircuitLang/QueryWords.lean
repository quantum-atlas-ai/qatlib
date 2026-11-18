/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Foundations.QueryWordCore.Circuit

@[expose] public section

/-!
# Matrix denotation of pure-unitary query words

This module reuses the public `Step` / `Circuit` / `Run` word machinery without redefining
it, and bridges word execution to matrix semantics through a denotation `Denote`, so that
left-to-right execution, concatenation order, and unitarity preservation become matrix
equations. This is the pure-word semantic bridge of the circuit language: only pure unitary
words are modeled here; measurement and classical branching belong to the program slot and
are deliberately absent from this word language.

## Main statements

* `run_denote`: executing a word equals applying its denotation matrix.
* `denote_append`: the denotation of `C ++ D` is the reversed product `Denote D * Denote C`.
* `denote_unitary`: a unitary oracle and a unitary word denote a unitary matrix.
-/

set_option autoImplicit false
set_option warningAsError true

open Qatlib.Foundations.QueryWordCore.Circuit
open Qatlib.Foundations.PureStateMath

namespace Qatlib.Concepts.CircuitLang.QueryWords

/-- The matrix of a single instruction relative to the oracle: explicit gates carry their
own matrix, queries carry the oracle matrix. -/
def InstMat {I : Type*} (oracle : Matrix I I ℂ) (s : Step I) : Matrix I I ℂ :=
  match s with
  | Step.gate U => U
  | Step.query => oracle

/-- The matrix denotation of a word: instruction matrices fold right-to-left, so the
instruction executed first acts rightmost. -/
noncomputable def Denote {I : Type*} [Fintype I] [DecidableEq I] (oracle : Matrix I I ℂ)
    (C : Circuit I) : Matrix I I ℂ := C.foldr (fun s M => M * InstMat oracle s) 1

/-- The empty word denotes the identity matrix. -/
theorem denote_nil {I : Type*} [Fintype I] [DecidableEq I] (oracle : Matrix I I ℂ) :
    Denote oracle [] = 1 := by
  simp [Denote]

/-- A gate-prepended word denotes the remaining word times the gate. -/
theorem denote_gate {I : Type*} [Fintype I] [DecidableEq I] (oracle : Matrix I I ℂ)
    (U : Matrix I I ℂ) (C : Circuit I) :
    Denote oracle (Step.gate U :: C) = Denote oracle C * U := by
  simp [Denote, InstMat]

/-- A query-prepended word denotes the remaining word times the oracle. -/
theorem denote_query {I : Type*} [Fintype I] [DecidableEq I] (oracle : Matrix I I ℂ)
    (C : Circuit I) : Denote oracle (Step.query :: C) = Denote oracle C * oracle := by
  simp [Denote, InstMat]

/-- Executing a word on a state equals applying the word's denotation matrix. -/
theorem run_denote {I : Type*} [Fintype I] [DecidableEq I] (oracle : Matrix I I ℂ)
    (C : Circuit I) (ψ : QState I) :
    Run oracle C ψ = ApplyGate (Denote oracle C) ψ := by
  induction C generalizing ψ with
  | nil => simp [Denote]
  | cons s C ih =>
    cases s with
    | gate U =>
      rw [run_gate, denote_gate, applyGate_mul]
      exact ih (ApplyGate U ψ)
    | query =>
      rw [run_query, denote_query, applyGate_mul]
      exact ih (ApplyGate oracle ψ)

/-- The denotation of a concatenation is the reversed product: the second word's matrix acts
on the left, matching left-to-right execution of `Run`. -/
theorem denote_append {I : Type*} [Fintype I] [DecidableEq I] (oracle : Matrix I I ℂ)
    (C D : Circuit I) :
    Denote oracle (C ++ D) = Denote oracle D * Denote oracle C := by
  induction C generalizing D with
  | nil =>
    rw [List.nil_append, denote_nil, Matrix.mul_one]
  | cons s C ih =>
    cases s with
    | gate U =>
      rw [List.cons_append, denote_gate oracle U (C ++ D), ih, denote_gate oracle U C,
        Matrix.mul_assoc]
    | query =>
      rw [List.cons_append, denote_query oracle (C ++ D), ih, denote_query oracle C,
        Matrix.mul_assoc]

/-- A two-gate word denotes the product with the gate executed second on the left. -/
theorem denote_pair {I : Type*} [Fintype I] [DecidableEq I] (oracle : Matrix I I ℂ)
    (U V : Matrix I I ℂ) :
    Denote oracle [Step.gate U, Step.gate V] = V * U := by
  rw [denote_gate, denote_gate, denote_nil, Matrix.one_mul]

/-- A unitary oracle and a unitary word denote a unitary matrix: the semantic bridge
preserves unitarity. -/
theorem denote_unitary {I : Type*} [Fintype I] [DecidableEq I] (oracle : Matrix I I ℂ)
    (horacle : oracle ∈ Matrix.unitaryGroup I ℂ) {C : Circuit I} (hC : IsUnitaryCircuit C) :
    Denote oracle C ∈ Matrix.unitaryGroup I ℂ := by
  induction C with
  | nil =>
    rw [denote_nil]
    exact Submonoid.one_mem _
  | cons s C ih =>
    cases s with
    | gate U =>
      have h := (isUnitaryCircuit_gate U C).mp hC
      rw [denote_gate]
      exact Submonoid.mul_mem (Matrix.unitaryGroup I ℂ) (ih h.2) h.1
    | query =>
      rw [denote_query]
      exact Submonoid.mul_mem (Matrix.unitaryGroup I ℂ)
        (ih ((isUnitaryCircuit_query C).mp hC)) horacle

end Qatlib.Concepts.CircuitLang.QueryWords
