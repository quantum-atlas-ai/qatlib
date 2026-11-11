/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.ElemGates95.QubitControl.Section4
import Qatlib.Concepts.MatrixAccess.KnownFrameSynth.KnownQubitControl

/-!
# Controlled one-qubit gate decompositions

This module formalizes the single-control constructions of Section 5 of [BarencoEtAl1995]. The
predicate `SU2` packages unitarity and determinant one. Theorems `lemma5_1` and `lemma5_2`
separate the special-unitary target factorization from the scalar phase applied on the control
wire.

The symmetric Euler helpers characterize the matrices that permit the reduced constructions in
`lemma5_4` and `lemma5_5`. The results `corollary5_3` and `corollary5_6` give exact six-gate
circuit semantics, using two CNOT gates or two controlled gates from the specified symmetric
Euler family.

## Main statements

* `lemma5_1`: the `A * PauliX * B * PauliX * C` factorization by special unitaries characterizes
  special-unitary targets.
* `lemma5_2`: a controlled scalar phase is a one-qubit operation on the control.
* `corollary5_3`: four one-qubit gates and two CNOT gates implement an arbitrary controlled
  unitary.
* `lemma5_4` and `lemma5_5`: symmetric Euler characterizations for the reduced gate families.
* `corollary5_6`: the same six-gate construction works with any controlled gate in the stated
  family.

## References

* [Barenco et al., 1995][BarencoEtAl1995]
-/

set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false
noncomputable section

open Matrix
open Qatlib.Concepts.MatrixAccess.KnownFrameSynth
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.QueryComplexity.DegreeMethod
open Qatlib.Concepts.BlockEncoding.LCU Qatlib.Foundations.PureStateMath.BornBridge
open Qatlib.Concepts.CopyEvolution.Discriminate
open Qatlib.Foundations.QueryWordCore.Circuit
open Qatlib.Papers.ElemGates95.QubitControl.Section4

namespace Qatlib.Papers.ElemGates95.QubitControl.Section5

/-- The predicate that a one-qubit matrix is unitary and has determinant one. -/
def SU2 (U : Matrix Bool Bool ℂ) : Prop :=
  U ∈ Matrix.unitaryGroup Bool ℂ ∧ U.det = 1

/-- The determinant of the one-qubit Pauli-X matrix is `-1`. -/
theorem det_pauliX : PauliX.det = -1 := by
  rw [det_apply_bool, PauliX, permMatrix]
  norm_num

/-- The scalar phase matrix `paperPh δ` is unitary for every real `δ`. -/
theorem paperPh_unitary (δ : ℝ) : paperPh δ ∈ Matrix.unitaryGroup Bool ℂ := by
  have hc : star (Complex.exp ((δ : ℂ) * Complex.I))
      * Complex.exp ((δ : ℂ) * Complex.I) = 1 := by
    have hstar : star (Complex.exp ((δ : ℂ) * Complex.I))
        = (starRingEnd ℂ) (Complex.exp ((δ : ℂ) * Complex.I)) := rfl
    rw [hstar, ← Complex.exp_conj, ← Complex.exp_add]
    have hz : (starRingEnd ℂ) ((δ : ℂ) * Complex.I) + (δ : ℂ) * Complex.I = 0 := by
      simp [map_mul, Complex.conj_I]
    rw [hz, Complex.exp_zero]
  rw [Matrix.mem_unitaryGroup_iff', Matrix.star_eq_conjTranspose, paperPh,
    Matrix.conjTranspose_smul, Matrix.conjTranspose_one, Matrix.smul_mul, Matrix.mul_smul,
    Matrix.mul_one, smul_smul, hc, one_smul]

/-- Lemma 5.1 of [BarencoEtAl1995]: a unitary `W` possesses special-unitary factors with `ABC =
I` and `AXBXC = W` if and only if `W` is special unitary. -/
theorem lemma5_1 (W : Matrix Bool Bool ℂ) (hW : W ∈ Matrix.unitaryGroup Bool ℂ) :
    (∃ A B C : Matrix Bool Bool ℂ,
        SU2 A ∧ SU2 B ∧ SU2 C ∧ A * B * C = 1 ∧ A * PauliX * B * PauliX * C = W)
      ↔ SU2 W := by
  constructor
  · rintro ⟨A, B, C, ⟨hA, hAd⟩, ⟨hB, hBd⟩, ⟨hC, hCd⟩, hABC, hW'⟩
    refine ⟨?_, ?_⟩
    · rw [← hW']
      exact mul_mem_unitaryGroup
        (mul_mem_unitaryGroup
          (mul_mem_unitaryGroup
            (mul_mem_unitaryGroup hA pauliX_unitary) hB) pauliX_unitary) hC
    · rw [← hW', Matrix.det_mul, Matrix.det_mul, Matrix.det_mul, Matrix.det_mul,
        hAd, hBd, hCd, det_pauliX]
      ring
  · intro hSU
    obtain ⟨A, B, C, hAu, hBu, hCu, hAd, hBd, hCd, hABC, hW'⟩ :=
      lemma4_3 W hW hSU.2
    exact ⟨A, B, C, ⟨hAu, hAd⟩, ⟨hBu, hBd⟩, ⟨hCu, hCd⟩, hABC, hW'⟩

/-- The control-wire phase factor `paperRz (-δ) * paperPh (δ / 2)` used to implement a
controlled scalar phase. -/
def lemma52E (δ : ℝ) : Matrix Bool Bool ℂ := paperRz (-δ) * paperPh (δ / 2)

/-- The control-wire factor `lemma52E δ` equals the phase gate `Rz δ`. -/
theorem lemma52E_eq_rz (δ : ℝ) : lemma52E δ = Rz δ := by
  simp only [lemma52E, paperPh, Matrix.mul_smul, Matrix.mul_one]
  ext i j
  rcases i <;> rcases j <;>
    simp [Matrix.smul_apply, qubitEulerPhase_ff, qubitEulerPhase_ft,
      qubitEulerPhase_tf, qubitEulerPhase_tt, Rz]
  · rw [show (1 : ℂ) = Complex.exp 0 from Complex.exp_zero.symm, ← Complex.exp_add]
    congr 1
    ring
  · rw [← Complex.exp_add]
    congr 1
    ring

/-- The two-qubit network applying `lemma52E δ` to the control and the identity to the target. -/
def controlPhaseNetwork (δ : ℝ) : Matrix (Bool × Bool) (Bool × Bool) ℂ :=
  TensorGate (lemma52E δ) (1 : Matrix Bool Bool ℂ)

/-- Lemma 5.2 of [BarencoEtAl1995]: the controlled scalar phase `paperPh δ` equals
`controlPhaseNetwork δ`. The witness `E = lemma52E δ` is unitary. -/
theorem lemma5_2 (δ : ℝ) :
    ∃ E : Matrix Bool Bool ℂ,
      E ∈ Matrix.unitaryGroup Bool ℂ ∧
      E = lemma52E δ ∧
      ControlledGate (paperPh δ) = controlPhaseNetwork δ := by
  refine ⟨lemma52E δ, ?_, rfl, ?_⟩
  · exact mul_mem_unitaryGroup (qubitEulerPhase_unitary (-δ)) (paperPh_unitary (δ / 2))
  · rw [controlPhaseNetwork, lemma52E_eq_rz]
    ext ⟨i, a⟩ ⟨j, b⟩
    cases i <;> cases j <;> cases a <;> cases b <;>
      simp [ControlledGate, BlockDiag, TensorGate, Rz, paperPh]

/-- Corollary 5.3 of [BarencoEtAl1995]: the known-angle circuit implements controlled `U`
exactly on every two-qubit input using four one-qubit gates and two CNOT gates. Its gate
count is six and its query count is zero. -/
theorem corollary5_3 (U : Matrix Bool Bool ℂ) (hU : U ∈ Matrix.unitaryGroup Bool ℂ)
    (ψ : QState (Bool × Bool)) :
    Run (1 : Matrix (Bool × Bool) (Bool × Bool) ℂ)
        (knownQubitControlCircuit (knownQubitAnglesOfUnitary U)) ψ =
      ApplyGate (ControlledGate U) ψ ∧
    ((knownQubitControlSteps (knownQubitAnglesOfUnitary U)).filter
        (fun s => match s with | .single _ _ => true | .cnot => false)).length = 4 ∧
    ((knownQubitControlSteps (knownQubitAnglesOfUnitary U)).filter
        (fun s => match s with | .single _ _ => false | .cnot => true)).length = 2 ∧
    GateCount (knownQubitControlCircuit (knownQubitAnglesOfUnitary U)) = 6 ∧
    QueryCount (knownQubitControlCircuit (knownQubitAnglesOfUnitary U)) = 0 := by
  obtain ⟨hrec, -⟩ := knownQubitEuler_explicit_angles_cover_unitaries U hU
  obtain ⟨-, -, hsingle, hcnot, hgate, hquery⟩ :=
    knownQubitControl_exact_six_gate_table (knownQubitAnglesOfUnitary U)
  obtain ⟨hrun, -, -, -⟩ := knownQubitControl_any_known_unitary_six_gate_compilation U ψ hU
  refine ⟨?_, hsingle, hcnot, hgate, hquery⟩
  rw [hrun, ← hrec]

/-- A matrix with diagonal entries `a` and `star a` and real off-diagonal entries `b` and `-b`
has a symmetric Euler representation when `‖a‖ ^ 2 + b ^ 2 = 1`. -/
theorem symmetricEuler_reconstruction (a : ℂ) (b : ℝ)
    (h : ‖a‖ ^ 2 + b ^ 2 = 1) :
    ∃ α θ : ℝ, paperRz α * paperRy θ * paperRz α =
      Matrix.of (fun i j : Bool => match i,j with
        | false,false => a | false,true => (b : ℂ)
        | true,false => -(b : ℂ) | true,true => star a) := by
  have hb1 : b ≤ 1 := by nlinarith [sq_nonneg ‖a‖]
  have hb0 : -1 ≤ b := by nlinarith [sq_nonneg ‖a‖]
  have hc : Real.cos (Real.arcsin b) = ‖a‖ := by
    rw [Real.cos_arcsin, Real.sqrt_eq_iff_mul_self_eq (by nlinarith) (norm_nonneg _)]
    nlinarith
  have hs : Real.sin (Real.arcsin b) = b := Real.sin_arcsin hb0 hb1
  have hnorm := Complex.norm_mul_exp_arg_mul_I a
  refine ⟨Complex.arg a, 2 * Real.arcsin b, ?_⟩
  ext i j
  cases i <;> cases j <;>
    simp only [eulerPRP_ff, eulerPRP_ft, eulerPRP_tf, eulerPRP_tt,
      show (2 * Real.arcsin b) / 2 = Real.arcsin b by ring, hc, hs, Matrix.of_apply]
  · rw [mul_right_comm, ← Complex.exp_add]
    calc
      _ = Complex.exp ((Complex.arg a : ℂ) * Complex.I) * (‖a‖ : ℂ) := by
        congr 2
        push_cast
        ring
      _ = a := by rw [mul_comm]; exact hnorm
  · rw [mul_right_comm, ← Complex.exp_add]
    simp
  · rw [mul_right_comm, ← Complex.exp_add]
    simp
  · rw [mul_right_comm, ← Complex.exp_add]
    calc
      _ = Complex.exp (-(Complex.arg a : ℂ) * Complex.I) * (‖a‖ : ℂ) := by
        congr 2
        push_cast
        ring
      _ = star a := by rw [mul_comm]; exact (star_eq_norm_mul_exp a).symm

/-- A unitary `W = A * PauliX * B * PauliX` with `B * A = 1` has a symmetric Euler form `paperRz
α * paperRy θ * paperRz α`. -/
theorem symmetricEuler_of_commutator (A B W : Matrix Bool Bool ℂ)
    (hW : W ∈ Matrix.unitaryGroup Bool ℂ) (hBA : B * A = 1)
    (he : W = A * PauliX * B * PauliX) :
    ∃ α θ : ℝ, W = paperRz α * paperRy θ * paperRz α := by
  have hd : W.det = 1 := by
    calc
      W.det = (B * A).det := by
        rw [he, Matrix.det_mul, Matrix.det_mul, Matrix.det_mul, Matrix.det_mul]
        have hx : PauliX.det = -1 := by
          rw [det_apply_bool, PauliX, permMatrix]
          norm_num
        rw [hx]
        ring
      _ = 1 := by rw [hBA, Matrix.det_one]
  obtain ⟨hdiag, hoff⟩ := bool_unitary_det_one hW hd
  have htr : (A * PauliX * B).trace = 0 := by
    rw [Matrix.trace_mul_cycle, hBA, Matrix.one_mul]
    simp [Matrix.trace, PauliX, permMatrix]
  have hWX : W * PauliX = A * PauliX * B := by
    rw [he, Matrix.mul_assoc (A * PauliX * B), pauliX_mul_self, Matrix.mul_one]
  rw [← hWX] at htr
  have hsum : W false true + W true false = 0 := by
    simpa [Matrix.trace, Matrix.mul_apply, PauliX, permMatrix, add_comm] using! htr
  rw [hoff] at hsum
  have hb : (starRingEnd ℂ) (W false true) = W false true := by
    linear_combination -hsum
  have hreal : ((W false true).re : ℂ) = W false true :=
    Complex.conj_eq_iff_re.mp hb
  have hn : Complex.normSq (W false false) + Complex.normSq (W false true) = 1 := by
    have hR : W * Wᴴ = 1 := by
      simpa only [Matrix.star_eq_conjTranspose] using!
        (Matrix.mem_unitaryGroup_iff).mp hW
    have h1 := congrArg (fun M : Matrix Bool Bool ℂ => M false false) hR
    have e2 (z : ℂ) : z * (starRingEnd ℂ) z = (Complex.normSq z : ℂ) := by
      rw [mul_comm]
      exact (Complex.normSq_eq_conj_mul_self (z := z)).symm
    simp only [Matrix.mul_apply, Fintype.sum_bool, conjTranspose_apply', e2] at h1
    norm_num only [Matrix.one_apply_eq] at h1
    rw [add_comm]
    exact_mod_cast h1
  rw [← hreal, Complex.normSq_ofReal, Complex.normSq_eq_norm_sq] at hn
  obtain ⟨α, θ, hs⟩ :=
      symmetricEuler_reconstruction (W false false) (W false true).re (by nlinarith)
  refine ⟨α, θ, ?_⟩
  rw [hs]
  ext i j
  cases i <;> cases j <;> simp only [Matrix.of_apply]
  · exact hreal.symm
  · rw [hoff, hb, hreal]
  · exact hdiag

/-- Every symmetric Euler matrix has special-unitary factors `A` and `B` with `B * A = 1` and
equals `A * PauliX * B * PauliX`. -/
theorem symmetricEuler_factors (α θ : ℝ) :
    ∃ A B : Matrix Bool Bool ℂ,
      (A ∈ Matrix.unitaryGroup Bool ℂ ∧ A.det = 1) ∧
      (B ∈ Matrix.unitaryGroup Bool ℂ ∧ B.det = 1) ∧
      B * A = 1 ∧
      paperRz α * paperRy θ * paperRz α = A * PauliX * B * PauliX := by
  let p : KnownQubitAngles := ⟨0, α, θ, α⟩
  let A := knownQubitUnitary (knownControlA p)
  let B := knownQubitUnitary (knownControlB p)
  have hC : knownQubitUnitary (knownControlC p) = 1 := by
    rw [knownQubitUnitary_controlC]
    simp [p, qubitEulerPhase_zero]
  obtain ⟨hAB, hX, _⟩ := knownQubitControl_ABC_phase_factorization p
  rw [hC, Matrix.mul_one] at hAB hX
  have hA : A ∈ Matrix.unitaryGroup Bool ℂ := knownQubitUnitary_unitary _
  have hB : B ∈ Matrix.unitaryGroup Bool ℂ := knownQubitUnitary_unitary _
  refine ⟨A, B, ⟨hA, ?_⟩, ⟨hB, ?_⟩, ?_, ?_⟩
  · dsimp only [A]
    rw [knownQubitUnitary_controlA]
    exact det_paperRz_mul_paperRy _ _
  · dsimp only [B]
    rw [knownQubitUnitary_controlB]
    exact det_paperRy_mul_paperRz _ _
  · have hL : star A * A = 1 := (Matrix.mem_unitaryGroup_iff').mp hA
    calc
      B * A = (star A * (A * B)) * A := by rw [← Matrix.mul_assoc, hL, Matrix.one_mul]
      _ = 1 := by rw [hAB, Matrix.mul_one, hL]
  · have hp : knownQubitUnitary p = paperRz α * paperRy θ * paperRz α := by
      simp [knownQubitUnitary, p]
    simpa only [show p.delta = 0 from rfl, Complex.ofReal_zero, zero_mul,
      Complex.exp_zero, one_smul, hp] using! hX.symm

/-- Multiplication of Boolean-indexed block-diagonal matrices multiplies the corresponding
blocks. -/
theorem boolBlockDiag_mul (F G : Bool → Matrix Bool Bool ℂ) :
    BlockDiag F * BlockDiag G = BlockDiag (fun b => F b * G b) := by
  ext ⟨i,a⟩ ⟨j,b⟩
  cases i <;> cases j <;>
    simp [BlockDiag, Matrix.mul_apply, Fintype.sum_prod_type]

/-- Applying `A` to the target and the identity to the control is the block-diagonal matrix with
constant block `A`. -/
theorem target_as_boolBlockDiag (A : Matrix Bool Bool ℂ) :
    TensorGate (1 : Matrix Bool Bool ℂ) A = BlockDiag (fun _ : Bool => A) := by
  ext ⟨i,a⟩ ⟨j,b⟩
  cases i <;> cases j <;> simp [TensorGate, BlockDiag, Matrix.kroneckerMap_apply]

/-- The CNOT matrix equals the controlled Pauli-X matrix. -/
theorem cnot_as_controlledX : CNOT = ControlledGate PauliX := by
  ext ⟨i,a⟩ ⟨j,b⟩
  cases i <;> cases j <;> cases a <;> cases b <;>
    simp [CNOT, ControlledGate, BlockDiag, PauliX, permMatrix, cnotFlip]

/-- A target-gate product interleaved with two controlled-`V` gates is block diagonal. Its
false-control block is `A * B * C`, and its true-control block is `A * V * B * V * C`. -/
theorem controlledFamily_target_product (A B C V : Matrix Bool Bool ℂ) :
    TensorGate (1 : Matrix Bool Bool ℂ) A * ControlledGate V *
      TensorGate 1 B * ControlledGate V * TensorGate 1 C =
      BlockDiag (fun b : Bool => if b then A * V * B * V * C else A * B * C) := by
  simp only [target_as_boolBlockDiag, ControlledGate, boolBlockDiag_mul]
  congr 1
  funext b
  cases b <;> simp

/-- Lemma 5.4 of [BarencoEtAl1995]: a unitary possesses the two-factor special-unitary
construction `A * X * B * X` with `B * A = I` exactly when it has a symmetric Euler form. -/
theorem lemma5_4 (W : Matrix Bool Bool ℂ) (hW : W ∈ Matrix.unitaryGroup Bool ℂ) :
    (∃ A B : Matrix Bool Bool ℂ,
        SU2 A ∧ SU2 B ∧ B * A = 1 ∧ W = A * PauliX * B * PauliX)
      ↔ ∃ α θ : ℝ, W = paperRz α * paperRy θ * paperRz α := by
  constructor
  · rintro ⟨A, B, _, _, hBA, he⟩
    exact symmetricEuler_of_commutator A B W hW hBA he
  · rintro ⟨α, θ, rfl⟩
    exact symmetricEuler_factors α θ

/-- Lemma 5.5 of [BarencoEtAl1995]: a unitary is `A * PauliX * B` for unitary inverse factors
`A` and `B` exactly when it is a symmetric Euler matrix followed by Pauli X. -/
theorem lemma5_5 (V : Matrix Bool Bool ℂ) (hV : V ∈ Matrix.unitaryGroup Bool ℂ) :
    (∃ A B : Matrix Bool Bool ℂ,
        A ∈ Matrix.unitaryGroup Bool ℂ ∧ B ∈ Matrix.unitaryGroup Bool ℂ ∧
        B * A = 1 ∧ V = A * PauliX * B)
      ↔ ∃ α θ : ℝ, V = paperRz α * paperRy θ * paperRz α * PauliX := by
  constructor
  · rintro ⟨A, B, _, _, hBA, he⟩
    have hW := mul_mem_unitaryGroup hV pauliX_unitary
    obtain ⟨α, θ, hshape⟩ := symmetricEuler_of_commutator A B (V * PauliX)
      hW hBA (by rw [he])
    refine ⟨α, θ, ?_⟩
    calc
      V = (V * PauliX) * PauliX := by
        rw [Matrix.mul_assoc, pauliX_mul_self, Matrix.mul_one]
      _ = _ := by rw [hshape]
  · rintro ⟨α, θ, rfl⟩
    obtain ⟨A, B, hA, hB, hBA, he⟩ := symmetricEuler_factors α θ
    refine ⟨A, B, hA.1, hB.1, hBA, ?_⟩
    rw [he, Matrix.mul_assoc (A * PauliX * B), pauliX_mul_self, Matrix.mul_one]

/-- The six-gate program applying target gates `C`, `B`, and `A`, interleaved with two
controlled-`V` gates, followed by `E` on the control. -/
def familySixGateProgram (E A B C V : Matrix Bool Bool ℂ) : Circuit (Bool × Bool) :=
  [.gate (TensorGate 1 C), .gate (ControlledGate V), .gate (TensorGate 1 B),
    .gate (ControlledGate V), .gate (TensorGate 1 A), .gate (TensorGate E 1)]

/-- The family program contains six gate instructions and makes no oracle queries. -/
theorem familySixGateProgram_cost (E A B C V : Matrix Bool Bool ℂ) :
    GateCount (familySixGateProgram E A B C V) = 6 ∧
      QueryCount (familySixGateProgram E A B C V) = 0 := by
  simp [familySixGateProgram, GateCount, QueryCount]

set_option maxHeartbeats 800000 in

/-- Corollary 5.6 of [BarencoEtAl1995]: for any `V` in the specified symmetric Euler family
followed by Pauli X, unitary one-qubit factors turn two controlled-`V` gates into an exact
controlled-`U` circuit. The resulting program has six gates and no queries. -/
theorem corollary5_6 (U : Matrix Bool Bool ℂ) (hU : U ∈ Matrix.unitaryGroup Bool ℂ)
    (V : Matrix Bool Bool ℂ)
    (hV : ∃ α θ : ℝ, V = paperRz α * paperRy θ * paperRz α * PauliX) :
    ∃ E A B C : Matrix Bool Bool ℂ,
      E ∈ Matrix.unitaryGroup Bool ℂ ∧ A ∈ Matrix.unitaryGroup Bool ℂ ∧
      B ∈ Matrix.unitaryGroup Bool ℂ ∧ C ∈ Matrix.unitaryGroup Bool ℂ ∧
      GateCount (familySixGateProgram E A B C V) = 6 ∧
      QueryCount (familySixGateProgram E A B C V) = 0 ∧
      ∀ ψ : QState (Bool × Bool),
        Run 1 (familySixGateProgram E A B C V) ψ = ApplyGate (ControlledGate U) ψ := by
  obtain ⟨α, θ, hV⟩ := hV
  obtain ⟨P, Q, hP, hQ, hQP, hshape⟩ := symmetricEuler_factors α θ
  have hVP : V = P * PauliX * Q := by
    rw [hV, hshape, Matrix.mul_assoc (P * PauliX * Q), pauliX_mul_self, Matrix.mul_one]
  let p := knownQubitAnglesOfUnitary U
  let E := knownQubitUnitary (knownControlE p)
  let A₀ := knownQubitUnitary (knownControlA p)
  let B₀ := knownQubitUnitary (knownControlB p)
  let C₀ := knownQubitUnitary (knownControlC p)
  let A := A₀ * Q
  let B := P * B₀ * Q
  let C := P * C₀
  have hrec : knownQubitUnitary p = U := (knownQubitEuler_explicit_angles_cover_unitaries U hU).1
  have hbase : TensorGate E 1 * TensorGate 1 A₀ * ControlledGate PauliX *
      TensorGate 1 B₀ * ControlledGate PauliX * TensorGate 1 C₀ = ControlledGate U := by
    have hb := knownControlProgramMatrix_steps p
    simp only [knownQubitControlSteps, knownControlProgramMatrix,
      knownControlStepMatrix, Matrix.one_mul, hrec] at hb
    simpa only [cnot_as_controlledX] using! hb
  have htarget : TensorGate (1 : Matrix Bool Bool ℂ) A * ControlledGate V *
      TensorGate 1 B * ControlledGate V * TensorGate 1 C =
      TensorGate (1 : Matrix Bool Bool ℂ) A₀ * ControlledGate PauliX *
      TensorGate 1 B₀ * ControlledGate PauliX * TensorGate 1 C₀ := by
    rw [controlledFamily_target_product, controlledFamily_target_product]
    apply congrArg (fun F : Bool → Matrix Bool Bool ℂ => BlockDiag F)
    funext b
    cases b <;> simp only [Bool.false_eq_true, if_false, if_true]
    · simp only [A, B, C, Matrix.mul_assoc, ← Matrix.mul_assoc Q P, hQP, Matrix.one_mul]
    · simp only [A, B, C, hVP, Matrix.mul_assoc, ← Matrix.mul_assoc Q P, hQP, Matrix.one_mul]
  have hmatrix : TensorGate E (1 : Matrix Bool Bool ℂ) *
      (TensorGate (1 : Matrix Bool Bool ℂ) A * ControlledGate V *
        TensorGate 1 B * ControlledGate V * TensorGate 1 C) = ControlledGate U := by
    rw [htarget]
    simpa only [Matrix.mul_assoc] using! hbase
  obtain ⟨hg, hq⟩ := familySixGateProgram_cost E A B C V
  refine ⟨E, A, B, C, knownQubitUnitary_unitary _,
    mul_mem_unitaryGroup (knownQubitUnitary_unitary _) hQ.1,
    mul_mem_unitaryGroup (mul_mem_unitaryGroup hP.1 (knownQubitUnitary_unitary _)) hQ.1,
    mul_mem_unitaryGroup hP.1 (knownQubitUnitary_unitary _), hg, hq, ?_⟩
  intro ψ
  simp only [familySixGateProgram, run_gate, run_nil, ← applyGate_mul]
  rw [← hmatrix]
  simp only [Matrix.mul_assoc]

end Qatlib.Papers.ElemGates95.QubitControl.Section5
