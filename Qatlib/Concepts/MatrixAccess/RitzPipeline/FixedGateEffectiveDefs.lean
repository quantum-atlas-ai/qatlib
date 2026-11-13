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

/-!
# Diagonal phase semantics for controlled-phase words

`cpExponent`, `wordExponent`, and `wordPhase` describe the diagonal action of controlled-phase
gate words. Words using only exponents at most three have phases that are eighth roots of unity.
The module also relates single-wire, parity, and controlled phases, using the phase-gate
conventions discussed in [NielsenChuang2010].

## Main statements

* `localProgramMatrix_cp_eq_diagonal`: controlled-phase words act diagonally.
* `cpOnlyFixed_phase_content`: fixed controlled-phase words have eighth-root diagonal entries.
* `parityPhaseWord_matrix`: a three-gate word realizes a parity phase.
* `controlledPhase_transport`: a controlled phase and a parity phase factor into single-wire
  phases.

## References

* [Nielsen and Chuang, 2010][NielsenChuang2010]
-/

set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false
set_option maxHeartbeats 1000000

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

/-- The signed phase angle contributed by a controlled-phase instruction on a basis register, or
zero for another instruction. -/
def cpExponent {n : ℕ} : LocalQFTGate n → Reg n → ℝ
  | .cp a c k neg, x => if x a && x c then dyadicPhaseAngle k neg else 0
  | _, _ => 0

/-- The predicate that every instruction in a gate word is a controlled-phase gate. -/
def cpOnly {n : ℕ} (gs : List (LocalQFTGate n)) : Prop :=
  ∀ g ∈ gs, ∃ a c : Fin n, ∃ k : ℕ, ∃ neg : Bool, g = .cp a c k neg

/-- The predicate that every instruction is a controlled-phase gate with exponent at most three. -/
def cpOnlyFixed {n : ℕ} (gs : List (LocalQFTGate n)) : Prop :=
  ∀ g ∈ gs, ∃ a c : Fin n, ∃ k : ℕ, ∃ neg : Bool, g = .cp a c k neg ∧ k ≤ 3

/-- The sum of controlled-phase angles contributed by a gate word on a given basis register. -/
def wordExponent {n : ℕ} (gs : List (LocalQFTGate n)) (x : Reg n) : ℝ :=
  (gs.map (fun g => cpExponent g x)).sum

/-- The complex phase obtained by exponentiating `wordExponent` times the imaginary unit. -/
def wordPhase {n : ℕ} (gs : List (LocalQFTGate n)) (x : Reg n) : ℂ :=
  Complex.exp (wordExponent gs x * Complex.I)

/-- A controlled-phase gate is diagonal, with its phase factor exactly when both selected bits
are true. -/
theorem localGateMatrix_cp_eq_diagonal {n : ℕ} (a c : Fin n) (k : ℕ) (neg : Bool) :
    localGateMatrix (.cp a c k neg)
      = Matrix.diagonal (fun x : Reg n =>
          if x a && x c then Complex.exp (dyadicPhaseAngle k neg * Complex.I) else 1) := rfl

/-- The conditional diagonal phase of a controlled-phase gate equals the exponential of its
`cpExponent` times the imaginary unit. -/
theorem cpExponent_exp {n : ℕ} (a c : Fin n) (k : ℕ) (neg : Bool) (x : Reg n) :
    (if x a && x c then Complex.exp (dyadicPhaseAngle k neg * Complex.I) else 1)
      = Complex.exp (cpExponent (.cp a c k neg) x * Complex.I) := by
  by_cases ha : x a = true <;> by_cases hc : x c = true <;>
    simp [cpExponent, ha, hc, Complex.exp_zero]

/-- A word consisting only of controlled-phase gates has diagonal matrix `wordPhase`. -/
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

/-- The diagonal entry of a controlled-phase word at a basis register equals its accumulated
`wordPhase`. -/
theorem localProgramMatrix_cp_apply {n : ℕ} (gs : List (LocalQFTGate n)) (h : cpOnly gs)
    (x : Reg n) :
    localProgramMatrix gs x x = wordPhase gs x := by
  have hdiag := localProgramMatrix_cp_eq_diagonal gs h
  rw [hdiag, Matrix.diagonal_apply_eq]

/-- Every off-diagonal entry of a controlled-phase-only word is zero. -/
theorem localProgramMatrix_cp_offdiag {n : ℕ} (gs : List (LocalQFTGate n)) (h : cpOnly gs)
    (x y : Reg n) (hxy : x ≠ y) :
    localProgramMatrix gs x y = 0 := by
  have hdiag := localProgramMatrix_cp_eq_diagonal gs h
  rw [hdiag]
  exact Matrix.diagonal_apply_ne (wordPhase gs) hxy

/-- The integer-indexed eighth root of unity `exp(i m π / 4)`. -/
def eighthRoot (m : ℤ) : ℂ :=
  Complex.exp (((m : ℝ) * (Real.pi / 4)) * Complex.I)

/-- The signed integer phase count for a controlled-phase instruction, in units of `π / 4` when
its exponent is at most three. It is zero unless both selected bits are true, and for other
instruction kinds. -/
def cpQuarterTurns {n : ℕ} : LocalQFTGate n → Reg n → ℤ
  | .cp a c k neg, x => if x a && x c then (2 : ℤ) ^ (3 - k) * (if neg then -1 else 1) else 0
  | _, _ => 0

/-- Express a dyadic phase angle as its sign times `2π / 2^k`. -/
theorem dyadicPhaseAngle_eq_sign_mul (k : ℕ) (neg : Bool) :
    dyadicPhaseAngle k neg = (if neg then -1 else 1 : ℝ) * (2 * Real.pi / (2 : ℝ) ^ k) := by
  cases neg <;> simp [dyadicPhaseAngle]

/-- For exponent at most three, a dyadic phase angle is a signed integer multiple of `π / 4`
with magnitude multiplier `2^(3 - k)`. -/
theorem dyadicPhaseAngle_quarter_turns (k : ℕ) (neg : Bool) (hk : k ≤ 3) :
    dyadicPhaseAngle k neg
      = (2 : ℝ) ^ (3 - k) * ((if neg then -1 else 1 : ℝ)) * (Real.pi / 4) := by
  interval_cases k <;> cases neg <;> simp [dyadicPhaseAngle] <;> ring

/-- For a controlled phase with exponent at most three, `cpExponent` is `cpQuarterTurns` times
`π / 4`. -/
theorem cpExponent_quarter_turns {n : ℕ} (a c : Fin n) (k : ℕ) (neg : Bool) (hk : k ≤ 3)
    (x : Reg n) :
    cpExponent (.cp a c k neg) x
      = (cpQuarterTurns (.cp a c k neg) x : ℝ) * (Real.pi / 4) := by
  interval_cases k <;> cases neg <;>
    by_cases ha : x a = true <;> by_cases hc : x c = true <;>
      simp [cpExponent, cpQuarterTurns, ha, hc, dyadicPhaseAngle] <;>
    ring

/-- For a fixed controlled-phase word, the total exponent equals the sum of its integer phase
counts times `π / 4`. -/
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

/-- Every diagonal entry of a controlled-phase word with exponents at most three is an eighth
root of unity. -/
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

/-- A word satisfying `cpOnlyFixed` has eighth roots of unity as its diagonal entries. -/
theorem cpOnlyFixed_phase_content {n : ℕ} (gs : List (LocalQFTGate n))
    (h : cpOnlyFixed gs) (x : Reg n) :
    ∃ m : ℤ, localProgramMatrix gs x x = eighthRoot m :=
  cpOnly_diag_eq_eighthRoot gs h x

/-- Decreasing a positive dyadic exponent by one doubles the phase angle. -/
theorem dyadicPhaseAngle_pred (k : ℕ) (neg : Bool) (hk : 1 ≤ k) :
    dyadicPhaseAngle (k - 1) neg = 2 * dyadicPhaseAngle k neg := by
  have hpow : (2 : ℝ) ^ (k - 1) * 2 = (2 : ℝ) ^ k := by
    rw [← pow_succ, show k - 1 + 1 = k by omega]
  cases neg <;> simp [dyadicPhaseAngle] <;> field_simp <;> rw [← hpow] <;> ring

/-- Decreasing a positive dyadic exponent by one and reversing its sign multiplies the angle by
negative two. -/
theorem dyadicPhaseAngle_pred_neg (k : ℕ) (neg : Bool) (hk : 1 ≤ k) :
    dyadicPhaseAngle (k - 1) (!neg) = -2 * dyadicPhaseAngle k neg := by
  rw [dyadicPhaseAngle_neg, dyadicPhaseAngle_pred k neg hk]
  ring

/-- The diagonal matrix applying `exp(iθ)` exactly when the selected wire is true. -/
def oneWirePhaseMatrix {n : ℕ} (r : Fin n) (θ : ℝ) : Matrix (Reg n) (Reg n) ℂ :=
  Matrix.diagonal (fun x => if x r then Complex.exp (θ * Complex.I) else 1)

/-- The diagonal matrix applying `exp(iθ)` exactly when the two selected bits differ. -/
def parityPhaseMatrix {n : ℕ} (a c : Fin n) (θ : ℝ) : Matrix (Reg n) (Reg n) ℂ :=
  Matrix.diagonal (fun x => if x a = x c then 1 else Complex.exp (θ * Complex.I))

/-- The diagonal matrix applying `exp(iθ)` exactly when both selected bits are true. -/
def controlledPhaseMatrix {n : ℕ} (a c : Fin n) (θ : ℝ) : Matrix (Reg n) (Reg n) ℂ :=
  Matrix.diagonal (fun x => if x a && x c then Complex.exp (θ * Complex.I) else 1)

/-- The singleton controlled-phase word with coincident control and target, representing a
single-wire dyadic phase. -/
def singlePhaseWord {n : ℕ} (r : Fin n) (k : ℕ) (neg : Bool) : List (LocalQFTGate n) :=
  [.cp r r k neg]

/-- The three-gate word combining two single-wire dyadic phases and an oppositely signed
controlled phase at the preceding exponent. -/
def parityPhaseWord {n : ℕ} (a c : Fin n) (k : ℕ) (neg : Bool) : List (LocalQFTGate n) :=
  [.cp a a k neg, .cp c c k neg, .cp a c (k - 1) (!neg)]

/-- For a positive exponent, `parityPhaseWord` contributes the dyadic phase angle when the
selected bits differ and zero otherwise. -/
theorem parityPhaseWord_exponent {n : ℕ} (a c : Fin n) (k : ℕ) (neg : Bool) (hk : 1 ≤ k)
    (x : Reg n) :
    wordExponent (parityPhaseWord a c k neg) x
      = if x a = x c then 0 else dyadicPhaseAngle k neg := by
  have hpred := dyadicPhaseAngle_pred_neg k neg hk
  by_cases ha : x a = true
  all_goals by_cases hc : x c = true
  all_goals
    simp [parityPhaseWord, wordExponent, cpExponent, ha, hc];
    try rw [hpred]; ring

/-- For a positive exponent, `parityPhaseWord` realizes the corresponding `parityPhaseMatrix`. -/
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
    simp [wordPhase, hexp, ha, hc]

/-- A controlled phase of angle `2θ` multiplied by the parity phase of angle `θ` equals the
product of the two single-wire phase matrices of angle `θ`. -/
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
