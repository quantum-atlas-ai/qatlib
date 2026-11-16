/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Foundations.PureStateMath.Qubit
public import Qatlib.Papers.BoolMatMult11.MainResults.ThresholdReduction

@[expose] public section


/-! # Actual oracle substitution for the identity reduction

A fixed word is chosen before the unknown matrix. Replacing every first
oracle by the known identity oracle preserves its matrix action, including
on an entangled finite workspace. The remaining cost counts query letters.
This supplies the substitution step, not a threshold lower-bound theorem.
-/
set_option autoImplicit false
noncomputable section
namespace Qatlib.Papers.BoolMatMult11.MainResults.OracleWord
open Qatlib.Foundations.PureStateMath
open Qatlib.Papers.BoolMatMult11.MainResults.ThresholdReduction

/-- A Boolean matrix supplied as an oracle. -/
abbrev BMatrix (n : ℕ) := Fin n → Fin n → Bool

/-- Joint answer, matrix address and arbitrary finite workspace basis. -/
abbrev Basis (n : ℕ) (I : Type) := (Bool × (Fin n × Fin n)) × I

/-- The standard XOR query leaves the address and workspace untouched. -/
def xorMap {n : ℕ} {I : Type} (A : BMatrix n) (p : Basis n I) : Basis n I :=
  ((Bool.xor p.1.1 (A p.1.2.1 p.1.2.2),p.1.2),p.2)

/-- XOR by a truth-table bit is an involution for every workspace. -/
theorem xorInv {n : ℕ} {I : Type} (A : BMatrix n) :
    Function.Involutive (xorMap (I := I) A) := by
  rintro ⟨⟨b,⟨i,j⟩⟩,w⟩
  cases b <;> cases h : A i j <;> simp [xorMap,h]

/-- Actual unitary matrix of one Boolean matrix oracle call. -/
def oracle {n : ℕ} {I : Type} [DecidableEq I]
    (A : BMatrix n) : Matrix (Basis n I) (Basis n I) ℂ := permMatrix (xorMap A)

/-- The actual XOR matrix is unitary, without any oracle promise. -/
theorem oracleUnit {n : ℕ} {I : Type} [Fintype I] [DecidableEq I]
    (A : BMatrix n) : oracle (I := I) A ∈ Matrix.unitaryGroup (Basis n I) ℂ :=
  permMatrix_unitary (xorInv A)

/-- Oracle action is the source's answer-bit XOR on arbitrary joint amplitudes. -/
theorem oracleApply {n : ℕ} {I : Type} [Fintype I] [DecidableEq I]
    (A : BMatrix n) (ψ : QState (Basis n I)) (p : Basis n I) :
    ApplyGate (oracle A) ψ p = ψ (xorMap A p) :=
  applyGate_permMatrix (xorInv A) ψ p

/-- Fixed unitary or one of the two unknown matrix query letters. -/
inductive Gate (n : ℕ) (I : Type) [Fintype I] [DecidableEq I] where
  | free (U : Matrix (Basis n I) (Basis n I) ℂ)
      (unitary : U ∈ Matrix.unitaryGroup (Basis n I) ℂ)
  | queryA
  | queryB

/-- Interpret a word letter using the two supplied truth tables. -/
def matrix {n : ℕ} {I : Type} [Fintype I] [DecidableEq I]
    (A B : BMatrix n) : Gate n I → Matrix (Basis n I) (Basis n I) ℂ
  | .free U _ => U
  | .queryA => oracle A
  | .queryB => oracle B

/-- Every allowed letter acts unitarily on the entire joint state. -/
theorem gateUnit {n : ℕ} {I : Type} [Fintype I] [DecidableEq I]
    (A B : BMatrix n) (g : Gate n I) :
    matrix A B g ∈ Matrix.unitaryGroup (Basis n I) ℂ := by
  cases g with
  | free U h => exact h
  | queryA => exact oracleUnit A
  | queryB => exact oracleUnit B

/-- Execute a fixed finite word by successive matrix actions. -/
def eval {n : ℕ} {I : Type} [Fintype I] [DecidableEq I]
    (A B : BMatrix n) (gs : List (Gate n I)) (ψ : QState (Basis n I)) :=
  gs.foldl (fun v g => ApplyGate (matrix A B g) v) ψ

/-- Count literal first- or second-oracle query constructors. -/
def count {n : ℕ} {I : Type} [Fintype I] [DecidableEq I]
    (second : Bool) : List (Gate n I) → ℕ
  | [] => 0
  | g :: gs => (match g with
      | .free _ _ => 0
      | .queryA => if second then 0 else 1
      | .queryB => if second then 1 else 0) + count second gs

/-- Replace a first-oracle letter by the known identity matrix query as a free gate. -/
def fixGate {n : ℕ} {I : Type} [Fintype I] [DecidableEq I] : Gate n I → Gate n I
  | .queryA => .free (oracle (identity n)) (oracleUnit _)
  | .queryB => .queryB
  | .free U h => .free U h

/-- A substituted letter has the same actual matrix when the first input is identity. -/
theorem fixMatrix {n : ℕ} {I : Type} [Fintype I] [DecidableEq I]
    (A B : BMatrix n) (g : Gate n I) :
    matrix A B (fixGate g) = matrix (identity n) B g := by
  cases g <;> rfl

/-- Substitution preserves the actual output state on every input amplitude. -/
theorem fixEval {n : ℕ} {I : Type} [Fintype I] [DecidableEq I]
    (A B : BMatrix n) (gs : List (Gate n I)) (ψ : QState (Basis n I)) :
    eval A B (gs.map fixGate) ψ = eval (identity n) B gs ψ := by
  induction gs generalizing ψ with
  | nil => rfl
  | cons g gs ih =>
    simpa only [List.map_cons,eval,List.foldl_cons,fixMatrix] using
      (ih (ApplyGate (matrix (identity n) B g) ψ))

/-- No first-oracle queries remain in the substituted word. -/
theorem firstZero {n : ℕ} {I : Type} [Fintype I] [DecidableEq I]
    (gs : List (Gate n I)) : count false (gs.map fixGate) = 0 := by
  induction gs with
  | nil => rfl
  | cons g gs ih => cases g <;> simp [count,fixGate,ih]

/-- The exact number of remaining queries equals the original second-oracle count. -/
theorem secondSame {n : ℕ} {I : Type} [Fintype I] [DecidableEq I]
    (gs : List (Gate n I)) : count true (gs.map fixGate) = count true gs := by
  induction gs with
  | nil => rfl
  | cons g gs ih => cases g <;> simp [count,fixGate,ih]

/-- Total charged cost after substitution is exactly the old second-query count. -/
theorem remainingCost {n : ℕ} {I : Type} [Fintype I] [DecidableEq I]
    (gs : List (Gate n I)) :
    count false (gs.map fixGate) + count true (gs.map fixGate) = count true gs := by
  rw [firstZero,secondSame,Nat.zero_add]

/-- Every word preserves normalization by its actual unitary execution. -/
theorem evalNorm {n : ℕ} {I : Type} [Fintype I] [DecidableEq I]
    (A B : BMatrix n) (gs : List (Gate n I)) (ψ : QState (Basis n I))
    (hψ : Normalized ψ) : Normalized (eval A B gs ψ) := by
  induction gs generalizing ψ with
  | nil => exact hψ
  | cons g gs ih => exact ih _ (normalized_applyGate (gateUnit A B g) hψ)

/-- Substitution preserves every actual Born outcome probability. -/
theorem bornSame {n : ℕ} {I : Type} [Fintype I] [DecidableEq I]
    (A B : BMatrix n) (gs : List (Gate n I)) (ψ : QState (Basis n I))
    (p : Basis n I) :
    BornProb (eval A B (gs.map fixGate) ψ) p =
      BornProb (eval (identity n) B gs ψ) p := by rw [fixEval]

/-- Every finite measurement event, including a fixed classical readout fiber,
has exactly the same weight after identity substitution. -/
theorem eventSame {n : ℕ} {I : Type} [Fintype I] [DecidableEq I]
    (A B : BMatrix n) (gs : List (Gate n I)) (ψ : QState (Basis n I))
    (S : Finset (Basis n I)) :
    MeasureProb (eval A B (gs.map fixGate) ψ) S =
      MeasureProb (eval (identity n) B gs ψ) S := by rw [fixEval]

/-- A word with no second query has no dependence on the second truth table. -/
theorem noSecond {n : ℕ} {I : Type} [Fintype I] [DecidableEq I]
    (A B C : BMatrix n) (gs : List (Gate n I)) (ψ : QState (Basis n I))
    (h : count true gs = 0) : eval A B gs ψ = eval A C gs ψ := by
  induction gs generalizing ψ with
  | nil => rfl
  | cons g gs ih =>
    cases g with
    | free U hu =>
      exact ih (ApplyGate U ψ) (by simpa [count] using h)
    | queryA =>
      exact ih (ApplyGate (oracle A) ψ) (by simpa [count] using h)
    | queryB => simp [count] at h

/-- Unlike a free-cost record, a fixed zero-query word cannot compute even
the one-bit threshold with an input-independent deterministic readout. -/
theorem zeroImpossible {I : Type} [Fintype I] [DecidableEq I]
    (gs : List (Gate 1 I)) (ψ : QState (Basis 1 I))
    (readout : QState (Basis 1 I) → Bool) (h : count true gs = 0) :
    ¬ ∀ B, readout (eval (identity 1) B gs ψ) = thresholdAnswer 1 B := by
  intro hc
  have hfalse := hc (fun _ _ => false)
  have htrue := hc (fun _ _ => true)
  have he := noSecond (identity 1) (fun _ _ => false) (fun _ _ => true) gs ψ h
  rw [he] at hfalse
  rw [htrue] at hfalse
  norm_num [thresholdAnswer,onesCount] at hfalse

end Qatlib.Papers.BoolMatMult11.MainResults.OracleWord
