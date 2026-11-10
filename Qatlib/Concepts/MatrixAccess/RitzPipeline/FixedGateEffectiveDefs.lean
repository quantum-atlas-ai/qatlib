/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.MatrixAccess.RitzPipeline.FixedGateSynthesis
import Qatlib.Concepts.PhaseErrorBound.PhaseErrorSum.LocalDyadicGate
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option linter.unusedVariables false
set_option linter.unusedTactic false

noncomputable section

open Qatlib.Foundations.InstrumentCore.ProjectiveMeasurement
open Qatlib.Concepts.PhaseErrorBound.PhaseErrorSum
open Qatlib.Foundations.PureStateMath

open Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.Emitter
open Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.GuardedCounter
open Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.Increment

namespace Qatlib.Concepts.MatrixAccess.RitzPipeline

open Matrix
open scoped Matrix.Norms.L2Operator

def cpExponent {n : ℕ} : LocalQFTGate n → Reg n → ℝ
  | .cp a c k neg, x => if x a && x c then dyadicPhaseAngle k neg else 0
  | _, _ => 0

def cpOnly {n : ℕ} (gs : List (LocalQFTGate n)) : Prop :=
  ∀ g ∈ gs, ∃ a c : Fin n, ∃ k : ℕ, ∃ neg : Bool, g = .cp a c k neg

def cpOnlyFixed {n : ℕ} (gs : List (LocalQFTGate n)) : Prop :=
  ∀ g ∈ gs, ∃ a c : Fin n, ∃ k : ℕ, ∃ neg : Bool, g = .cp a c k neg ∧ k ≤ 3

def wordExponent {n : ℕ} (gs : List (LocalQFTGate n)) (x : Reg n) : ℝ :=
  (gs.map (fun g => cpExponent g x)).sum

def wordPhase {n : ℕ} (gs : List (LocalQFTGate n)) (x : Reg n) : ℂ :=
  Complex.exp (wordExponent gs x * Complex.I)

theorem localGateMatrix_cp_eq_diagonal {n : ℕ} (a c : Fin n) (k : ℕ) (neg : Bool) :
    localGateMatrix (.cp a c k neg)
      = Matrix.diagonal (fun x : Reg n =>
          if x a && x c then Complex.exp (dyadicPhaseAngle k neg * Complex.I) else 1) := rfl

theorem cpExponent_exp {n : ℕ} (a c : Fin n) (k : ℕ) (neg : Bool) (x : Reg n) :
    (if x a && x c then Complex.exp (dyadicPhaseAngle k neg * Complex.I) else 1)
      = Complex.exp (cpExponent (.cp a c k neg) x * Complex.I) := by
  by_cases ha : x a = true <;> by_cases hc : x c = true <;>
    simp [cpExponent, ha, hc, Complex.exp_zero]

theorem localProgramMatrix_cp_eq_diagonal {n : ℕ} (gs : List (LocalQFTGate n)) :
    cpOnly gs →
      localProgramMatrix gs = Matrix.diagonal (wordPhase gs) := by
  induction gs with
  | nil =>
      intro _
      have hone : wordPhase [] = (fun _ : Reg n => (1 : ℂ)) := by
        funext x
        simp [wordPhase, wordExponent, Complex.exp_zero]
      rw [localProgramMatrix_nil, hone, Matrix.diagonal_one]
  | cons g gs ih =>
      intro h
      have hgs : cpOnly gs := fun g' hg' => h g' (List.mem_cons_of_mem g hg')
      obtain ⟨a, c, k, neg, rfl⟩ := h g (List.mem_cons_self)
      rw [localProgramMatrix_cons, ih hgs, localGateMatrix_cp_eq_diagonal,
        Matrix.diagonal_mul_diagonal]
      congr 1
      funext x
      simp only [wordPhase, wordExponent, List.map_cons, List.sum_cons]
      have hsplit : (↑(cpExponent (.cp a c k neg) x
            + (gs.map (fun g => cpExponent g x)).sum) : ℂ) * Complex.I
          = (↑(cpExponent (.cp a c k neg) x) : ℂ) * Complex.I
            + (↑((gs.map (fun g => cpExponent g x)).sum) : ℂ) * Complex.I := by
        push_cast
        ring
      rw [hsplit, Complex.exp_add, cpExponent_exp]
      exact mul_comm _ _

theorem localProgramMatrix_cp_apply {n : ℕ} (gs : List (LocalQFTGate n)) (h : cpOnly gs)
    (x : Reg n) :
    localProgramMatrix gs x x = wordPhase gs x := by
  have hdiag := localProgramMatrix_cp_eq_diagonal gs h
  rw [hdiag, Matrix.diagonal_apply_eq]

theorem localProgramMatrix_cp_offdiag {n : ℕ} (gs : List (LocalQFTGate n)) (h : cpOnly gs)
    (x y : Reg n) (hxy : x ≠ y) :
    localProgramMatrix gs x y = 0 := by
  have hdiag := localProgramMatrix_cp_eq_diagonal gs h
  rw [hdiag]
  exact Matrix.diagonal_apply_ne (wordPhase gs) hxy

def eighthRoot (m : ℤ) : ℂ :=
  Complex.exp (((m : ℝ) * (Real.pi / 4)) * Complex.I)

def cpQuarterTurns {n : ℕ} : LocalQFTGate n → Reg n → ℤ
  | .cp a c k neg, x => if x a && x c then (2 : ℤ) ^ (3 - k) * (if neg then -1 else 1) else 0
  | _, _ => 0

theorem dyadicPhaseAngle_eq_sign_mul (k : ℕ) (neg : Bool) :
    dyadicPhaseAngle k neg = (if neg then -1 else 1 : ℝ) * (2 * Real.pi / (2 : ℝ) ^ k) := by
  cases neg <;> simp [dyadicPhaseAngle]

theorem dyadicPhaseAngle_quarter_turns (k : ℕ) (neg : Bool) (hk : k ≤ 3) :
    dyadicPhaseAngle k neg
      = (2 : ℝ) ^ (3 - k) * ((if neg then -1 else 1 : ℝ)) * (Real.pi / 4) := by
  interval_cases k <;> cases neg <;> simp [dyadicPhaseAngle] <;> ring

theorem cpExponent_quarter_turns {n : ℕ} (a c : Fin n) (k : ℕ) (neg : Bool) (hk : k ≤ 3)
    (x : Reg n) :
    cpExponent (.cp a c k neg) x
      = (cpQuarterTurns (.cp a c k neg) x : ℝ) * (Real.pi / 4) := by
  interval_cases k <;> cases neg <;>
    by_cases ha : x a = true <;> by_cases hc : x c = true <;>
      simp [cpExponent, cpQuarterTurns, ha, hc, dyadicPhaseAngle] <;>
    push_cast <;> ring

theorem wordExponent_eq_quarter_turns {n : ℕ} (gs : List (LocalQFTGate n))
    (h : cpOnlyFixed gs) (x : Reg n) :
    wordExponent gs x = ((gs.map (fun g => cpQuarterTurns g x)).sum : ℝ) * (Real.pi / 4) := by
  classical
  induction gs with
  | nil => simp [wordExponent]
  | cons g gs ih =>
      have hgs : cpOnlyFixed gs := fun g' hg' => h g' (List.mem_cons_of_mem g hg')
      obtain ⟨a, c, k, neg, rfl, hk⟩ := h g (List.mem_cons_self)
      have hstep : wordExponent (.cp a c k neg :: gs) x
          = cpExponent (.cp a c k neg) x + wordExponent gs x := by
        simp [wordExponent, List.map_cons, List.sum_cons]
      rw [hstep, ih hgs]
      have hexp := cpExponent_quarter_turns a c k neg hk x
      rw [hexp]
      simp only [List.map_cons, List.sum_cons]
      have hcast : (↑(cpQuarterTurns (.cp a c k neg) x
              + (gs.map (fun g => cpQuarterTurns g x)).sum) : ℝ)
          = (↑(cpQuarterTurns (.cp a c k neg) x) : ℝ)
            + (↑((gs.map (fun g => cpQuarterTurns g x)).sum) : ℝ) := Int.cast_add _ _
      rw [hcast]
      ring

theorem cpOnly_diag_eq_eighthRoot {n : ℕ} (gs : List (LocalQFTGate n))
    (h : cpOnlyFixed gs) (x : Reg n) :
    ∃ m : ℤ, localProgramMatrix gs x x = eighthRoot m := by
  have hcp : cpOnly gs := fun g hg => by
    obtain ⟨a, c, k, neg, rfl, hk⟩ := h g hg
    exact ⟨a, c, k, neg, rfl⟩
  have hdiag := localProgramMatrix_cp_apply gs hcp x
  have hexp := wordExponent_eq_quarter_turns gs h x
  refine ⟨(gs.map (fun g => cpQuarterTurns g x)).sum, ?_⟩
  rw [hdiag, wordPhase, hexp, eighthRoot]
  congr 1
  push_cast
  ring

theorem cpOnlyFixed_phase_content {n : ℕ} (gs : List (LocalQFTGate n))
    (h : cpOnlyFixed gs) (x : Reg n) :
    ∃ m : ℤ, localProgramMatrix gs x x = eighthRoot m :=
  cpOnly_diag_eq_eighthRoot gs h x

theorem dyadicPhaseAngle_pred (k : ℕ) (neg : Bool) (hk : 1 ≤ k) :
    dyadicPhaseAngle (k - 1) neg = 2 * dyadicPhaseAngle k neg := by
  have hpow : (2 : ℝ) ^ (k - 1) * 2 = (2 : ℝ) ^ k := by
    rw [← pow_succ, show k - 1 + 1 = k by omega]
  cases neg <;> simp [dyadicPhaseAngle] <;> field_simp <;> rw [← hpow] <;> ring

theorem dyadicPhaseAngle_pred_neg (k : ℕ) (neg : Bool) (hk : 1 ≤ k) :
    dyadicPhaseAngle (k - 1) (!neg) = -2 * dyadicPhaseAngle k neg := by
  rw [dyadicPhaseAngle_neg, dyadicPhaseAngle_pred k neg hk]
  ring

def oneWirePhaseMatrix {n : ℕ} (r : Fin n) (θ : ℝ) : Matrix (Reg n) (Reg n) ℂ :=
  Matrix.diagonal (fun x => if x r then Complex.exp (θ * Complex.I) else 1)

def parityPhaseMatrix {n : ℕ} (a c : Fin n) (θ : ℝ) : Matrix (Reg n) (Reg n) ℂ :=
  Matrix.diagonal (fun x => if x a = x c then 1 else Complex.exp (θ * Complex.I))

def controlledPhaseMatrix {n : ℕ} (a c : Fin n) (θ : ℝ) : Matrix (Reg n) (Reg n) ℂ :=
  Matrix.diagonal (fun x => if x a && x c then Complex.exp (θ * Complex.I) else 1)

def singlePhaseWord {n : ℕ} (r : Fin n) (k : ℕ) (neg : Bool) : List (LocalQFTGate n) :=
  [.cp r r k neg]

def parityPhaseWord {n : ℕ} (a c : Fin n) (k : ℕ) (neg : Bool) : List (LocalQFTGate n) :=
  [.cp a a k neg, .cp c c k neg, .cp a c (k - 1) (!neg)]

theorem parityPhaseWord_exponent {n : ℕ} (a c : Fin n) (k : ℕ) (neg : Bool) (hk : 1 ≤ k)
    (x : Reg n) :
    wordExponent (parityPhaseWord a c k neg) x
      = if x a = x c then 0 else dyadicPhaseAngle k neg := by
  have hpred := dyadicPhaseAngle_pred_neg k neg hk
  by_cases ha : x a = true <;> by_cases hc : x c = true <;>
    simp [parityPhaseWord, wordExponent, cpExponent, ha, hc] <;>
    try rw [hpred] <;> ring

theorem parityPhaseWord_matrix {n : ℕ} (a c : Fin n) (k : ℕ) (neg : Bool) (hk : 1 ≤ k) :
    localProgramMatrix (parityPhaseWord a c k neg)
      = parityPhaseMatrix a c (dyadicPhaseAngle k neg) := by
  have hcp : cpOnly (parityPhaseWord a c k neg) := by
    intro g hg
    have hg' : g = .cp a a k neg ∨ g = .cp c c k neg ∨ g = .cp a c (k - 1) (!neg) := by
      simpa [parityPhaseWord] using hg
    rcases hg' with rfl | rfl | rfl
    · exact ⟨a, a, k, neg, rfl⟩
    · exact ⟨c, c, k, neg, rfl⟩
    · exact ⟨a, c, k - 1, !neg, rfl⟩
  have hdiag := localProgramMatrix_cp_eq_diagonal (parityPhaseWord a c k neg) hcp
  have hexp := parityPhaseWord_exponent a c k neg hk
  rw [hdiag, parityPhaseMatrix]
  congr 1
  funext x
  by_cases ha : x a = true <;> by_cases hc : x c = true <;>
    simp [wordPhase, hexp, ha, hc] <;>
    ring

theorem controlledPhase_transport {n : ℕ} (a c : Fin n) (θ : ℝ) :
    controlledPhaseMatrix a c (2 * θ) * parityPhaseMatrix a c θ
      = oneWirePhaseMatrix c θ * oneWirePhaseMatrix a θ := by
  rw [controlledPhaseMatrix, parityPhaseMatrix, oneWirePhaseMatrix,
    oneWirePhaseMatrix, Matrix.diagonal_mul_diagonal, Matrix.diagonal_mul_diagonal]
  congr 1
  funext x
  by_cases ha : x a = true <;> by_cases hc : x c = true <;>
    simp [ha, hc]
  have hsplit : (2 : ℂ) * (θ : ℂ) * Complex.I = (θ : ℂ) * Complex.I + (θ : ℂ) * Complex.I := by
    ring
  rw [hsplit, Complex.exp_add]

end Qatlib.Concepts.MatrixAccess.RitzPipeline
