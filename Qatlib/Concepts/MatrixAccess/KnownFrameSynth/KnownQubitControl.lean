/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.MatrixAccess.KnownFrameSynth.KnownQubitEuler
import Qatlib.Concepts.QueryComplexity.DegreeMethod.LocalCapability
import Qatlib.Foundations.QueryWordCore.Circuit
import Qatlib.Concepts.LocalMachine.LocalTransport.ControlledQueryCircuit

/-!
# Six-gate control of a known qubit unitary

A known qubit unitary is decomposed into factors `knownControlA`, `knownControlB`,
`knownControlC`, and a control phase correction `knownControlE`. `knownQubitControlSteps`
combines four single-qubit gates and two CNOTs to implement its controlled gate exactly, in the
elementary-gate framework of [BarencoEtAl1995].

Control programs have matrix and circuit semantics, unitary gates, explicit gate and query
counts, and adjoint programs. The six-gate implementation extends to arbitrary finite
workspaces, inverses, and repeated controlled powers.

## Main statements

* `knownQubitControl_ABC_phase_factorization`: the algebraic identities behind the controlled
  construction.
* `knownQubitControl_any_known_unitary_six_gate_compilation`: exact control with six gates and
  zero queries.
* `knownQubitControl_inverse_repeat_real_costs`: inverse, cancellation, and repetition semantics
  with gate counts.

## References

* [Barenco et al., 1995][BarencoEtAl1995]
-/

set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

open Qatlib.Foundations.QueryWordCore.Circuit
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.QueryComplexity.DegreeMethod

open Qatlib.Concepts.LocalMachine.LocalTransport
open Qatlib.Concepts.QspSimulation.Achievability.WellFormedAdjointCircuit

namespace Qatlib.Concepts.MatrixAccess.KnownFrameSynth

open Matrix
open Qatlib.Concepts.QueryWordCore.AdjointCircuits
open Qatlib
open Qatlib.Concepts.CoherentSim.CoherentOAA.SignalProcessing
open Qatlib
open Qatlib
open Qatlib
open Qatlib
open Qatlib.Concepts.SignalPrimitive.PhaseFrontend
open Qatlib
open Qatlib
open Qatlib
open Qatlib
open Qatlib.Concepts.PhaseGeometry.Phase Qatlib.Concepts.QspSimulation.WordModel
open Qatlib
open Qatlib
open Qatlib
open Qatlib
open Qatlib
open Qatlib.Concepts.OperatorErrors.Robustness.SignalProcessing
open Qatlib
open Qatlib.Concepts.NonNormalSpec.ResolventWord
open Qatlib
open Qatlib
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false

/-- A two-qubit instruction consisting of a known single-qubit gate on a selected factor or a
CNOT. -/
inductive KnownQubitControlStep where
  | single : Bool → KnownQubitAngles → KnownQubitControlStep
  | cnot : KnownQubitControlStep

/-- The Euler-angle parameters for the factor whose matrix is `qubitEulerPhase p.alpha *
qubitEulerRotation (p.theta / 2)`. -/
noncomputable def knownControlA (p : KnownQubitAngles) : KnownQubitAngles :=
    ⟨0, p.alpha, p.theta / 2, 0⟩

/-- The Euler-angle parameters for the factor whose matrix is `qubitEulerRotation (-p.theta / 2)
* qubitEulerPhase (-(p.alpha + p.beta) / 2)`. -/
noncomputable def knownControlB (p : KnownQubitAngles) : KnownQubitAngles :=
  ⟨0, 0, -p.theta / 2, -(p.alpha + p.beta) / 2⟩

/-- The Euler-angle parameters for the factor whose matrix is `qubitEulerPhase ((p.beta -
p.alpha) / 2)`. -/
noncomputable def knownControlC (p : KnownQubitAngles) : KnownQubitAngles :=
    ⟨0, (p.beta - p.alpha) / 2, 0, 0⟩

/-- The Euler-angle parameters for the control phase correction whose matrix is `Rz p.delta`. -/
noncomputable def knownControlE (p : KnownQubitAngles) : KnownQubitAngles :=
    ⟨p.delta / 2, -p.delta, 0, 0⟩

/-- Interprets a control instruction as a single-qubit gate on the first or second factor, or as
CNOT. -/
noncomputable def knownControlStepMatrix : KnownQubitControlStep →
    Matrix (Bool × Bool) (Bool × Bool) ℂ
  | .single true p => TensorGate (knownQubitUnitary p) 1
  | .single false p => TensorGate 1 (knownQubitUnitary p)
  | .cnot => CNOT

/-- Compiles a list of control instructions into a circuit containing their gate matrices in the
same order. -/
noncomputable def knownControlProgramCircuit (gs : List KnownQubitControlStep) :
    Circuit (Bool × Bool) :=
  gs.map (fun s => Step.gate (knownControlStepMatrix s))

/-- The matrix of a control program, multiplying instruction matrices in execution order. -/
noncomputable def knownControlProgramMatrix : List KnownQubitControlStep →
    Matrix (Bool × Bool) (Bool × Bool) ℂ
  | [] => 1
  | s :: gs => knownControlProgramMatrix gs * knownControlStepMatrix s

/-- The empty control program has identity matrix. -/
@[simp] theorem knownControlProgramMatrix_nil :
    knownControlProgramMatrix [] = 1 := rfl

/-- The matrix of a control program with head `s` is the tail matrix multiplied by the matrix of
`s`. -/
theorem knownControlProgramMatrix_cons (s : KnownQubitControlStep)
    (gs : List KnownQubitControlStep) :
    knownControlProgramMatrix (s :: gs)
      = knownControlProgramMatrix gs * knownControlStepMatrix s := rfl

/-- Takes the adjoint of a single-qubit instruction and leaves CNOT unchanged. -/
def knownControlStepAdjoint : KnownQubitControlStep → KnownQubitControlStep
  | .single b p => .single b (knownQubitAngleAdjoint p)
  | .cnot => .cnot

/-- Reverses a control program and takes the adjoint of every instruction. -/
def knownControlProgramAdjoint (gs : List KnownQubitControlStep) : List KnownQubitControlStep :=
  gs.reverse.map knownControlStepAdjoint

/-- The six-instruction controlled-unitary decomposition: target `C`, CNOT, target `B`, CNOT,
target `A`, and control phase correction `E`. -/
noncomputable def knownQubitControlSteps (p : KnownQubitAngles) : List KnownQubitControlStep :=
  [.single false (knownControlC p), .cnot,
   .single false (knownControlB p), .cnot,
   .single false (knownControlA p), .single true (knownControlE p)]

/-- The circuit compiled from the six control instructions associated with the supplied Euler
angles. -/
noncomputable def knownQubitControlCircuit (p : KnownQubitAngles) : Circuit (Bool × Bool) :=
  knownControlProgramCircuit (knownQubitControlSteps p)

/-- The matrix of `knownControlA` is the phase by `p.alpha` followed in matrix order by the
rotation by `p.theta / 2`. -/
theorem knownQubitUnitary_controlA (p : KnownQubitAngles) :
    knownQubitUnitary (knownControlA p)
      = qubitEulerPhase p.alpha * qubitEulerRotation (p.theta / 2) := by
  simp only [knownQubitUnitary, knownControlA, Complex.ofReal_zero, zero_mul,
    Complex.exp_zero, one_smul, qubitEulerPhase_zero, Matrix.mul_one]

/-- The matrix of `knownControlB` is the rotation by `-p.theta / 2` times the phase by
`-(p.alpha + p.beta) / 2`. -/
theorem knownQubitUnitary_controlB (p : KnownQubitAngles) :
    knownQubitUnitary (knownControlB p)
      = qubitEulerRotation (-p.theta / 2) * qubitEulerPhase (-(p.alpha + p.beta) / 2) := by
  simp only [knownQubitUnitary, knownControlB, Complex.ofReal_zero, zero_mul,
    Complex.exp_zero, one_smul, qubitEulerPhase_zero, Matrix.one_mul]

/-- The matrix of `knownControlC` is the Euler phase by `(p.beta - p.alpha) / 2`. -/
theorem knownQubitUnitary_controlC (p : KnownQubitAngles) :
    knownQubitUnitary (knownControlC p) = qubitEulerPhase ((p.beta - p.alpha) / 2) := by
  simp only [knownQubitUnitary, knownControlC, Complex.ofReal_zero, zero_mul,
    Complex.exp_zero, one_smul, qubitEulerPhase_zero, qubitEulerRotation_zero,
    Matrix.one_mul, Matrix.mul_one]

/-- The matrix of the control phase correction is `Rz p.delta`. -/
theorem knownQubitUnitary_controlE (p : KnownQubitAngles) :
    knownQubitUnitary (knownControlE p) = Rz p.delta := by
  simp only [knownQubitUnitary, knownControlE, qubitEulerRotation_zero, qubitEulerPhase_zero,
    Matrix.mul_one, Matrix.one_mul]
  ext i j
  rcases i <;> rcases j <;>
    simp [qubitEulerPhase_ff, qubitEulerPhase_ft, qubitEulerPhase_tf, qubitEulerPhase_tt, Rz]
  · rw [show (1 : ℂ) = Complex.exp 0 from Complex.exp_zero.symm, ← Complex.exp_add]
    congr 1
    push_cast
    ring
  · rw [← Complex.exp_add]
    congr 1
    push_cast
    ring

/-- The square of the Pauli X matrix is the identity. -/
theorem pauliX_mul_self : PauliX * PauliX = (1 : Matrix Bool Bool ℂ) := by
  rw [show PauliX * PauliX = permMatrix Bool.not * permMatrix Bool.not from rfl,
    permMatrix_mul_self Bool.not_not]

/-- Conjugation by Pauli X preserves multiplication of two qubit matrices. -/
theorem pauliX_mul_mul_pauliX (M N : Matrix Bool Bool ℂ) :
    PauliX * (M * N) * PauliX = (PauliX * M * PauliX) * (PauliX * N * PauliX) := by
  simp only [Matrix.mul_assoc]
  rw [← Matrix.mul_assoc PauliX PauliX (N * PauliX), pauliX_mul_self, Matrix.one_mul]

/-- The factors satisfy `A * B * C = I` and recover the target unitary from `A * X * B * X * C`
with its scalar phase; the control correction is `Rz p.delta`. This is the
controlled-unitary factorization used in [BarencoEtAl1995]. -/
theorem knownQubitControl_ABC_phase_factorization :
    ∀ p : KnownQubitAngles,
      let A := knownQubitUnitary (knownControlA p)
      let B := knownQubitUnitary (knownControlB p)
      let C := knownQubitUnitary (knownControlC p)
      let E := knownQubitUnitary (knownControlE p)
      A * B * C = (1 : Matrix Bool Bool ℂ) ∧
      Complex.exp ((p.delta : ℂ) * Complex.I) • (A * PauliX * B * PauliX * C) = knownQubitUnitary p ∧
      E = Rz p.delta := by
  intro p
  (try dsimp only)
  rw [knownQubitUnitary_controlA p, knownQubitUnitary_controlB p,
    knownQubitUnitary_controlC p, knownQubitUnitary_controlE p]
  refine ⟨?_, ?_, rfl⟩
  · simp only [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc (qubitEulerRotation (p.theta / 2))
        (qubitEulerRotation (-p.theta / 2))
        (qubitEulerPhase (-(p.alpha + p.beta) / 2) * qubitEulerPhase ((p.beta - p.alpha) / 2)),
      qubitEulerRotation_mul, qubitEulerPhase_mul,
      show p.theta / 2 + -p.theta / 2 = 0 from by ring,
      show -(p.alpha + p.beta) / 2 + (p.beta - p.alpha) / 2 = -p.alpha from by ring,
      qubitEulerRotation_zero, Matrix.one_mul, qubitEulerPhase_mul,
      show p.alpha + -p.alpha = 0 from by ring, qubitEulerPhase_zero]
  · have hconjB : PauliX
        * (qubitEulerRotation (-p.theta / 2) * qubitEulerPhase (-(p.alpha + p.beta) / 2)) * PauliX
      = qubitEulerRotation (p.theta / 2) * qubitEulerPhase ((p.alpha + p.beta) / 2) := by
      rw [pauliX_mul_mul_pauliX, pauliX_mul_qubitEulerRotation, pauliX_mul_qubitEulerPhase]
      simp only [neg_div, neg_neg]
    have hreg : (qubitEulerPhase p.alpha * qubitEulerRotation (p.theta / 2)) * PauliX
        * (qubitEulerRotation (-p.theta / 2) * qubitEulerPhase (-(p.alpha + p.beta) / 2))
        * PauliX * qubitEulerPhase ((p.beta - p.alpha) / 2)
      = (qubitEulerPhase p.alpha * qubitEulerRotation (p.theta / 2))
        * (PauliX * (qubitEulerRotation (-p.theta / 2)
            * qubitEulerPhase (-(p.alpha + p.beta) / 2)) * PauliX)
        * qubitEulerPhase ((p.beta - p.alpha) / 2) := by
      rw [Matrix.mul_assoc _ PauliX
          (qubitEulerRotation (-p.theta / 2) * qubitEulerPhase (-(p.alpha + p.beta) / 2)),
        Matrix.mul_assoc _ (PauliX
          * (qubitEulerRotation (-p.theta / 2) * qubitEulerPhase (-(p.alpha + p.beta) / 2))) PauliX]
    rw [hreg, hconjB]
    have hfinal : (qubitEulerPhase p.alpha * qubitEulerRotation (p.theta / 2))
        * (qubitEulerRotation (p.theta / 2) * qubitEulerPhase ((p.alpha + p.beta) / 2))
        * qubitEulerPhase ((p.beta - p.alpha) / 2)
      = qubitEulerPhase p.alpha * qubitEulerRotation p.theta * qubitEulerPhase p.beta := by
      simp only [Matrix.mul_assoc]
      rw [← Matrix.mul_assoc (qubitEulerRotation (p.theta / 2))
          (qubitEulerRotation (p.theta / 2))
          (qubitEulerPhase ((p.alpha + p.beta) / 2) * qubitEulerPhase ((p.beta - p.alpha) / 2)),
        qubitEulerRotation_mul, qubitEulerPhase_mul,
        show (p.alpha + p.beta) / 2 + (p.beta - p.alpha) / 2 = p.beta from by ring,
        show p.theta / 2 + p.theta / 2 = p.theta from by ring]
    rw [hfinal, knownQubitUnitary]

/-- Two matrices are equal if their actions agree on every computational basis state. -/
theorem eq_of_forall_applyGate_ket {I : Type*} [Fintype I] [DecidableEq I]
    {M N : Matrix I I ℂ} (h : ∀ i, ApplyGate M (Qatlib.Foundations.PureStateMath.Ket i) = ApplyGate N (Qatlib.Foundations.PureStateMath.Ket i)) : M = N := by
  ext a b
  have hb := h b
  have eM : ApplyGate M (Qatlib.Foundations.PureStateMath.Ket b) a = M a b := by
    simp only [ApplyGate, Matrix.mulVec, dotProduct]
    rw [Finset.sum_eq_single b (fun k _ hk => by rw [ket_ne hk, mul_zero])
      (by intro hcon; exact absurd (Finset.mem_univ b) hcon)]
    simp [Qatlib.Foundations.PureStateMath.Ket]
  have eN : ApplyGate N (Qatlib.Foundations.PureStateMath.Ket b) a = N a b := by
    simp only [ApplyGate, Matrix.mulVec, dotProduct]
    rw [Finset.sum_eq_single b (fun k _ hk => by rw [ket_ne hk, mul_zero])
      (by intro hcon; exact absurd (Finset.mem_univ b) hcon)]
    simp [Qatlib.Foundations.PureStateMath.Ket]
  rw [← eM, ← eN]
  exact congrFun hb a

/-- CNOT leaves a basis control unchanged and applies Pauli X to the target exactly when that
control is true. -/
theorem applyGate_cnot_tensorState_ket (c : Bool) (φ : QState Bool) :
    ApplyGate CNOT (TensorState (Qatlib.Foundations.PureStateMath.Ket c) φ)
      = TensorState (Qatlib.Foundations.PureStateMath.Ket c) (ApplyGate (if c then PauliX else (1 : Matrix Bool Bool ℂ)) φ) := by
  funext p
  obtain ⟨c', y'⟩ := p
  rw [show CNOT = permMatrix cnotFlip from rfl, applyGate_permMatrix cnotFlip_involutive]
  show (Qatlib.Foundations.PureStateMath.Ket c c' : ℂ) * φ (y' ^^ c')
      = (Qatlib.Foundations.PureStateMath.Ket c c' : ℂ) * ApplyGate (if c then PauliX else (1 : Matrix Bool Bool ℂ)) φ y'
  by_cases hc : c' = c
  · rw [hc]
    cases c with
    | false => simp [TensorState, Bool.xor_false, applyGate_one]
    | true =>
      simp only [TensorState, ket_self, one_mul, Bool.xor_true, if_true]
      rw [show PauliX = permMatrix Bool.not from rfl, applyGate_permMatrix Bool.not_not]
  · rw [ket_ne hc, zero_mul, zero_mul]

/-- A diagonal matrix multiplies each basis state by its corresponding diagonal entry. -/
theorem applyGate_diagonal_ket {I : Type*} [Fintype I] [DecidableEq I] (d : I → ℂ) (c : I) :
    ApplyGate (Matrix.diagonal d) (Qatlib.Foundations.PureStateMath.Ket c) = d c • Qatlib.Foundations.PureStateMath.Ket c := by
  funext j
  by_cases h : j = c
  · rw [h, ApplyGate, Matrix.mulVec, dotProduct, Finset.sum_eq_single c]
    · rw [Matrix.diagonal_apply, if_pos rfl, ket_apply, if_pos rfl, mul_one, Pi.smul_apply,
        smul_eq_mul, ket_apply, if_pos rfl]
      simp
    · intro k _ hk
      rw [Matrix.diagonal_apply, if_neg (fun e => hk e.symm), zero_mul]
    · intro hcon
      exact absurd (Finset.mem_univ c) hcon
  · have hzero : ∀ k ∈ (Finset.univ : Finset I),
        Matrix.diagonal d j k * Qatlib.Foundations.PureStateMath.Ket c k = 0 := by
      intro k _
      rw [Matrix.diagonal_apply, ket_apply]
      by_cases hkj : j = k
      · rw [if_pos hkj, if_neg (fun e => h (hkj ▸ e)), mul_zero]
      · rw [if_neg (fun e => hkj e), zero_mul]
    rw [ApplyGate, Matrix.mulVec, dotProduct, Finset.sum_eq_zero hzero, Pi.smul_apply,
      smul_eq_mul, ket_apply, if_neg h, mul_zero]

/-- The gate `Rz t` fixes the false basis state and multiplies the true basis state by `exp(i
t)`. -/
theorem applyGate_rz_ket (t : ℝ) (b : Bool) :
    ApplyGate (Rz t) (Qatlib.Foundations.PureStateMath.Ket b)
      = (if b then Complex.exp ((t : ℂ) * Complex.I) else 1) • Qatlib.Foundations.PureStateMath.Ket b := by
  rw [show Rz t = Matrix.diagonal fun a => if a then Complex.exp ((t : ℂ) * Complex.I) else 1
      from rfl, applyGate_diagonal_ket]

/-- A scalar on the left tensor factor can be pulled out of the tensor state. -/
theorem tensorState_smul_left {I J : Type*} [Fintype I] [Fintype J] (k : ℂ)
    (ψ : QState I) (χ : QState J) : TensorState (k • ψ) χ = k • TensorState ψ χ := by
  funext p
  simp only [TensorState, Pi.smul_apply, smul_eq_mul]
  ring

/-- A scalar on the right tensor factor can be pulled out of the tensor state. -/
theorem tensorState_smul_right {I J : Type*} [Fintype I] [Fintype J] (k : ℂ)
    (ψ : QState I) (χ : QState J) : TensorState ψ (k • χ) = k • TensorState ψ χ := by
  funext p
  simp only [TensorState, Pi.smul_apply, smul_eq_mul]
  ring

/-- Scaling a gate matrix scales its action on a state by the same complex scalar. -/
theorem applyGate_smul {I : Type*} [Fintype I] [DecidableEq I] (k : ℂ) (M : Matrix I I ℂ)
    (ψ : QState I) : ApplyGate (k • M) ψ = k • ApplyGate M ψ := by
  rw [ApplyGate, ApplyGate, Matrix.smul_mulVec]

/-- Every control instruction has a unitary two-qubit matrix. -/
theorem knownControlStepMatrix_unitary (s : KnownQubitControlStep) :
    knownControlStepMatrix s ∈ Matrix.unitaryGroup (Bool × Bool) ℂ := by
  cases s with
  | single b p =>
    cases b with
    | true => exact tensorGate_unitary (knownQubitUnitary_unitary p) (Submonoid.one_mem _)
    | false => exact tensorGate_unitary (Submonoid.one_mem _) (knownQubitUnitary_unitary p)
  | cnot => exact cnot_unitary

/-- Every control program has a unitary two-qubit matrix. -/
theorem knownControlProgramMatrix_unitary (gs : List KnownQubitControlStep) :
    knownControlProgramMatrix gs ∈ Matrix.unitaryGroup (Bool × Bool) ℂ := by
  induction gs with
  | nil => exact Submonoid.one_mem _
  | cons s gs ih =>
    rw [knownControlProgramMatrix_cons]
    exact mul_mem_unitaryGroup ih (knownControlStepMatrix_unitary s)

/-- Compiling the empty control program gives the empty circuit. -/
@[simp] theorem knownControlProgramCircuit_nil :
    knownControlProgramCircuit [] = ([] : Circuit (Bool × Bool)) := rfl

/-- Compiling a control program with head `s` prepends the gate matrix of `s` to the compiled
tail. -/
theorem knownControlProgramCircuit_cons (s : KnownQubitControlStep)
    (gs : List KnownQubitControlStep) :
    knownControlProgramCircuit (s :: gs)
      = Step.gate (knownControlStepMatrix s) :: knownControlProgramCircuit gs := rfl

/-- Executing a compiled control program equals applying its program matrix. -/
theorem run_knownControlProgramCircuit (gs : List KnownQubitControlStep)
    (ψ : QState (Bool × Bool)) :
    Run (1 : Matrix (Bool × Bool) (Bool × Bool) ℂ) (knownControlProgramCircuit gs) ψ
      = ApplyGate (knownControlProgramMatrix gs) ψ := by
  induction gs generalizing ψ with
  | nil =>
    rw [knownControlProgramCircuit_nil, run_nil, knownControlProgramMatrix_nil, applyGate_one]
  | cons s gs ih =>
    rw [knownControlProgramCircuit_cons, run_gate, ih, ← applyGate_mul]
    rfl

/-- Every compiled control program is a unitary circuit. -/
theorem isUnitaryCircuit_knownControlProgramCircuit (gs : List KnownQubitControlStep) :
    IsUnitaryCircuit (knownControlProgramCircuit gs) := by
  induction gs with
  | nil => exact isUnitaryCircuit_nil
  | cons s gs ih =>
    rw [knownControlProgramCircuit_cons, isUnitaryCircuit_gate]
    exact ⟨knownControlStepMatrix_unitary s, ih⟩

/-- A compiled control program uses zero oracle queries. -/
theorem queryCount_knownControlProgramCircuit (gs : List KnownQubitControlStep) :
    QueryCount (knownControlProgramCircuit gs) = 0 := by
  induction gs with
  | nil => rfl
  | cons s gs ih => rw [knownControlProgramCircuit_cons, queryCount_gate, ih]

/-- The gate count of a compiled control program equals its instruction-list length. -/
theorem gateCount_knownControlProgramCircuit (gs : List KnownQubitControlStep) :
    GateCount (knownControlProgramCircuit gs) = gs.length := by
  induction gs with
  | nil => rfl
  | cons s gs ih =>
    rw [knownControlProgramCircuit_cons, gateCount_gate, ih, List.length_cons]

/-- Appending two control programs multiplies their matrices with the later program on the left. -/
theorem knownControlProgramMatrix_append (gs hs : List KnownQubitControlStep) :
    knownControlProgramMatrix (gs ++ hs)
      = knownControlProgramMatrix hs * knownControlProgramMatrix gs := by
  induction gs with
  | nil => simp
  | cons s gs ih =>
    rw [List.cons_append, knownControlProgramMatrix, knownControlProgramMatrix, ih,
      Matrix.mul_assoc]

/-- Taking the adjoint of a control instruction gives the conjugate transpose of its matrix. -/
theorem knownControlStepMatrix_adjoint (s : KnownQubitControlStep) :
    knownControlStepMatrix (knownControlStepAdjoint s) = (knownControlStepMatrix s)ᴴ := by
  cases s with
  | single b p =>
    cases b <;>
      simp only [knownControlStepAdjoint, knownControlStepMatrix, Matrix.conjTranspose_one,
        tensorGate_conjTranspose, knownQubitUnitary_adjoint]
  | cnot =>
    simp only [knownControlStepAdjoint, knownControlStepMatrix]
    rw [show CNOTᴴ = (permMatrix cnotFlip)ᴴ from rfl, permMatrix_conjTranspose cnotFlip_involutive]
    rfl

/-- Reversing and taking instruction adjoints gives the conjugate transpose of the control
program matrix. -/
theorem knownControlProgramMatrix_adjoint_eq (gs : List KnownQubitControlStep) :
    knownControlProgramMatrix (knownControlProgramAdjoint gs)
      = (knownControlProgramMatrix gs)ᴴ := by
  induction gs with
  | nil => simp [knownControlProgramAdjoint, knownControlProgramMatrix]
  | cons s gs ih =>
    have hmap : List.map knownControlStepAdjoint gs.reverse
        = knownControlProgramAdjoint gs := rfl
    rw [knownControlProgramAdjoint, List.reverse_cons, List.map_append, List.map_cons,
      List.map_nil, knownControlProgramMatrix_append, knownControlProgramMatrix_cons,
      knownControlProgramMatrix_nil, Matrix.one_mul, knownControlProgramMatrix_cons, hmap, ih,
      Matrix.conjTranspose_mul, knownControlStepMatrix_adjoint]

/-- Taking the adjoint program preserves the number of control instructions. -/
theorem knownControlProgramAdjoint_length (gs : List KnownQubitControlStep) :
    (knownControlProgramAdjoint gs).length = gs.length := by
  simp [knownControlProgramAdjoint]

/-- Collects exact execution, circuit and matrix unitarity, zero query count, instruction-length
gate count, and adjoint semantics and length for control programs. -/
theorem knownQubitControl_program_semantics_legality_adjoint :
    ∀ (gs : List KnownQubitControlStep) (ψ : QState (Bool × Bool)),
  Run (1 : Matrix (Bool × Bool) (Bool × Bool) ℂ) (knownControlProgramCircuit gs) ψ =
    ApplyGate (knownControlProgramMatrix gs) ψ ∧
  IsUnitaryCircuit (knownControlProgramCircuit gs) ∧
  knownControlProgramMatrix gs ∈ Matrix.unitaryGroup (Bool × Bool) ℂ ∧
  QueryCount (knownControlProgramCircuit gs) = 0 ∧ GateCount (knownControlProgramCircuit gs) = gs.length ∧
  knownControlProgramMatrix (knownControlProgramAdjoint gs) = (knownControlProgramMatrix gs)ᴴ ∧
  (knownControlProgramAdjoint gs).length = gs.length ∧
  (∀ s : KnownQubitControlStep, knownControlStepMatrix s ∈ Matrix.unitaryGroup (Bool × Bool) ℂ) := by
  intro gs ψ
  exact ⟨run_knownControlProgramCircuit gs ψ,
    isUnitaryCircuit_knownControlProgramCircuit gs,
    knownControlProgramMatrix_unitary gs,
    queryCount_knownControlProgramCircuit gs,
    gateCount_knownControlProgramCircuit gs,
    knownControlProgramMatrix_adjoint_eq gs,
    knownControlProgramAdjoint_length gs,
    knownControlStepMatrix_unitary⟩

/-- The controlled-unitary circuit has the displayed six-instruction table, consisting of four
single-qubit gates and two CNOTs, with six gates and zero queries. -/
theorem knownQubitControl_exact_six_gate_table :
    ∀ p : KnownQubitAngles,
  knownQubitControlSteps p = [.single false (knownControlC p), .cnot,
    .single false (knownControlB p), .cnot, .single false (knownControlA p), .single true (knownControlE p)] ∧
  knownQubitControlCircuit p = knownControlProgramCircuit (knownQubitControlSteps p) ∧
  ((knownQubitControlSteps p).filter (fun s => match s with | .single _ _ => true | _ => false)).length = 4 ∧
  ((knownQubitControlSteps p).filter (fun s => match s with | .cnot => true | _ => false)).length = 2 ∧
  GateCount (knownQubitControlCircuit p) = 6 ∧ QueryCount (knownQubitControlCircuit p) = 0 := by
  intro p
  refine ⟨rfl, rfl, ?_, ?_, ?_, ?_⟩ <;> rfl

/-- The matrix of the six control instructions is exactly the controlled gate of the specified
known qubit unitary. -/
theorem knownControlProgramMatrix_steps (p : KnownQubitAngles) :
    knownControlProgramMatrix (knownQubitControlSteps p)
      = ControlledGate (knownQubitUnitary p) := by
  have hABC : (qubitEulerPhase p.alpha * qubitEulerRotation (p.theta / 2))
      * (qubitEulerRotation (-p.theta / 2) * qubitEulerPhase (-(p.alpha + p.beta) / 2))
      * qubitEulerPhase ((p.beta - p.alpha) / 2) = 1 := by
    simp only [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc (qubitEulerRotation (p.theta / 2))
        (qubitEulerRotation (-p.theta / 2))
        (qubitEulerPhase (-(p.alpha + p.beta) / 2) * qubitEulerPhase ((p.beta - p.alpha) / 2)),
      qubitEulerRotation_mul, qubitEulerPhase_mul,
      show p.theta / 2 + -p.theta / 2 = 0 from by ring,
      show -(p.alpha + p.beta) / 2 + (p.beta - p.alpha) / 2 = -p.alpha from by ring,
      qubitEulerRotation_zero, Matrix.one_mul, qubitEulerPhase_mul,
      show p.alpha + -p.alpha = 0 from by ring, qubitEulerPhase_zero]
  have key : Complex.exp ((p.delta : ℂ) * Complex.I)
      • ((qubitEulerPhase p.alpha * qubitEulerRotation (p.theta / 2)) * PauliX
        * (qubitEulerRotation (-p.theta / 2) * qubitEulerPhase (-(p.alpha + p.beta) / 2))
        * PauliX * qubitEulerPhase ((p.beta - p.alpha) / 2))
      = knownQubitUnitary p := by
    have hconjB : PauliX
        * (qubitEulerRotation (-p.theta / 2) * qubitEulerPhase (-(p.alpha + p.beta) / 2)) * PauliX
      = qubitEulerRotation (p.theta / 2) * qubitEulerPhase ((p.alpha + p.beta) / 2) := by
      rw [pauliX_mul_mul_pauliX, pauliX_mul_qubitEulerRotation, pauliX_mul_qubitEulerPhase]
      simp only [neg_div, neg_neg]
    have hreg : (qubitEulerPhase p.alpha * qubitEulerRotation (p.theta / 2)) * PauliX
        * (qubitEulerRotation (-p.theta / 2) * qubitEulerPhase (-(p.alpha + p.beta) / 2))
        * PauliX * qubitEulerPhase ((p.beta - p.alpha) / 2)
      = (qubitEulerPhase p.alpha * qubitEulerRotation (p.theta / 2))
        * (PauliX * (qubitEulerRotation (-p.theta / 2)
            * qubitEulerPhase (-(p.alpha + p.beta) / 2)) * PauliX)
        * qubitEulerPhase ((p.beta - p.alpha) / 2) := by
      rw [Matrix.mul_assoc _ PauliX
          (qubitEulerRotation (-p.theta / 2) * qubitEulerPhase (-(p.alpha + p.beta) / 2)),
        Matrix.mul_assoc _ (PauliX
          * (qubitEulerRotation (-p.theta / 2) * qubitEulerPhase (-(p.alpha + p.beta) / 2))) PauliX]
    rw [hreg, hconjB]
    have hfinal : (qubitEulerPhase p.alpha * qubitEulerRotation (p.theta / 2))
        * (qubitEulerRotation (p.theta / 2) * qubitEulerPhase ((p.alpha + p.beta) / 2))
        * qubitEulerPhase ((p.beta - p.alpha) / 2)
      = qubitEulerPhase p.alpha * qubitEulerRotation p.theta * qubitEulerPhase p.beta := by
      simp only [Matrix.mul_assoc]
      rw [← Matrix.mul_assoc (qubitEulerRotation (p.theta / 2))
          (qubitEulerRotation (p.theta / 2))
          (qubitEulerPhase ((p.alpha + p.beta) / 2) * qubitEulerPhase ((p.beta - p.alpha) / 2)),
        qubitEulerRotation_mul, qubitEulerPhase_mul,
        show (p.alpha + p.beta) / 2 + (p.beta - p.alpha) / 2 = p.beta from by ring,
        show p.theta / 2 + p.theta / 2 = p.theta from by ring]
    rw [hfinal, knownQubitUnitary]
  apply eq_of_forall_applyGate_ket
  rintro ⟨c, y⟩
  rw [← run_knownControlProgramCircuit]
  simp only [knownQubitControlCircuit, knownQubitControlSteps, knownControlProgramCircuit,
    List.map_cons, List.map_nil, knownControlStepMatrix, run_gate, run_nil,
    ← tensorState_ket_ket]
  rw [applyGate_tensorGate, applyGate_one, applyGate_cnot_tensorState_ket,
    applyGate_tensorGate, applyGate_one, applyGate_cnot_tensorState_ket,
    applyGate_tensorGate, applyGate_one, applyGate_tensorGate, applyGate_one]
  rw [← applyGate_mul, ← applyGate_mul, ← applyGate_mul, ← applyGate_mul]
  rw [knownQubitUnitary_controlE p, applyGate_rz_ket, tensorState_smul_left]
  cases c with
  | false =>
    rw [knownQubitUnitary_controlA p, knownQubitUnitary_controlB p,
      knownQubitUnitary_controlC p,
      show (if false = true then PauliX else (1 : Matrix Bool Bool ℂ))
        = (1 : Matrix Bool Bool ℂ) from if_neg (by simp),
      show (if false = true then Complex.exp ((p.delta : ℂ) * Complex.I) else 1) = 1
        from if_neg (by simp)]
    simp only [one_smul, Matrix.mul_one, Matrix.mul_one]
    rw [hABC, applyGate_one,
      applyGate_isControlledGate_ket_false (isControlledGate_controlledGate (knownQubitUnitary p)),
      tensorState_ket_ket]
  | true =>
    rw [knownQubitUnitary_controlA p, knownQubitUnitary_controlB p,
      knownQubitUnitary_controlC p,
      show (if true = true then PauliX else (1 : Matrix Bool Bool ℂ)) = PauliX from if_pos rfl,
      show (if true = true then Complex.exp ((p.delta : ℂ) * Complex.I) else 1)
        = Complex.exp ((p.delta : ℂ) * Complex.I) from if_pos rfl]
    rw [applyGate_isControlledGate_ket_true (isControlledGate_controlledGate (knownQubitUnitary p)),
      ← tensorState_smul_right, ← applyGate_smul, key]

/-- Controlling the identity qubit matrix gives the two-qubit identity. -/
theorem controlledGate_one : ControlledGate (1 : Matrix Bool Bool ℂ) = 1 := by
  ext ⟨c, i⟩ ⟨c', j⟩
  simp only [ControlledGate, BlockDiag, Matrix.of_apply]
  rcases c <;> rcases c' <;> simp [Matrix.one_apply]

/-- The controlled-gate construction preserves multiplication of qubit matrices. -/
theorem controlledGate_mul (U V : Matrix Bool Bool ℂ) :
    ControlledGate U * ControlledGate V = ControlledGate (U * V) := by
  ext ⟨c, i⟩ ⟨c', j⟩
  simp only [ControlledGate, BlockDiag, Matrix.of_apply, Matrix.mul_apply,
    Fintype.sum_prod_type]
  rcases c <;> rcases c' <;> simp [Matrix.one_apply]
  rw [show (U * V) i j = U i true * V true j + U i false * V false j from by
    rw [Matrix.mul_apply, Fintype.sum_bool]]

/-- The adjoint of a controlled gate is the controlled gate of the adjoint matrix. -/
theorem controlledGate_conjTranspose (U : Matrix Bool Bool ℂ) :
    (ControlledGate U)ᴴ = ControlledGate Uᴴ := by
  ext ⟨c, i⟩ ⟨c', j⟩
  simp only [Matrix.conjTranspose_apply, ControlledGate, BlockDiag, Matrix.of_apply]
  rcases c <;> rcases c' <;> simp [Matrix.one_apply, eq_comm]

/-- For a qubit matrix, `ControlledGate` agrees with `controlOracle`. -/
theorem controlledGate_eq_controlOracle (U : Matrix Bool Bool ℂ) :
    ControlledGate U = controlOracle U := by
  ext ⟨c, i⟩ ⟨c', j⟩
  simp only [ControlledGate, BlockDiag, controlOracle, Qatlib.Concepts.BlockEncoding.LCU.select,
    Matrix.of_apply]
  rcases c <;> rcases c' <;> simp

/-- The six-step program matrix is the desired controlled gate, satisfies `IsControlledGate`,
and has the corresponding circuit execution and `controlOracle` interpretation. -/
theorem knownQubitControl_exact_controlled_semantics :
    ∀ (p : KnownQubitAngles) (ψ : QState (Bool × Bool)),
  knownControlProgramMatrix (knownQubitControlSteps p) = ControlledGate (knownQubitUnitary p) ∧
  IsControlledGate (knownControlProgramMatrix (knownQubitControlSteps p)) (knownQubitUnitary p) ∧
  Run (1 : Matrix (Bool × Bool) (Bool × Bool) ℂ) (knownQubitControlCircuit p) ψ =
    ApplyGate (ControlledGate (knownQubitUnitary p)) ψ ∧
  ControlledGate (knownQubitUnitary p) = controlOracle (knownQubitUnitary p) := by
  intro p ψ
  refine ⟨knownControlProgramMatrix_steps p, ?_, ?_, controlledGate_eq_controlOracle _⟩
  · rw [knownControlProgramMatrix_steps]
    exact isControlledGate_controlledGate _
  · rw [show knownQubitControlCircuit p
        = knownControlProgramCircuit (knownQubitControlSteps p) from rfl,
      run_knownControlProgramCircuit, knownControlProgramMatrix_steps]

/-- Every known qubit unitary has an exact controlled implementation as a unitary circuit with
six gates and zero oracle queries, using its chosen Euler angles. See [BarencoEtAl1995]. -/
theorem knownQubitControl_any_known_unitary_six_gate_compilation :
    ∀ (U : Matrix Bool Bool ℂ) (ψ : QState (Bool × Bool)), U ∈ Matrix.unitaryGroup Bool ℂ →
  Run (1 : Matrix (Bool × Bool) (Bool × Bool) ℂ)
    (knownQubitControlCircuit (knownQubitAnglesOfUnitary U)) ψ = ApplyGate (ControlledGate U) ψ ∧
  IsUnitaryCircuit (knownQubitControlCircuit (knownQubitAnglesOfUnitary U)) ∧
  GateCount (knownQubitControlCircuit (knownQubitAnglesOfUnitary U)) = 6 ∧
  QueryCount (knownQubitControlCircuit (knownQubitAnglesOfUnitary U)) = 0 := by
  intro U ψ hU
  have hrec := (knownQubitEuler_explicit_angles_cover_unitaries U hU).1
  refine ⟨?_, isUnitaryCircuit_knownControlProgramCircuit _, ?_, ?_⟩
  · rw [(knownQubitControl_exact_controlled_semantics (knownQubitAnglesOfUnitary U) ψ).2.2.1, hrec]
  · exact (knownQubitControl_exact_six_gate_table (knownQubitAnglesOfUnitary U)).2.2.2.2.1
  · exact (knownQubitControl_exact_six_gate_table (knownQubitAnglesOfUnitary U)).2.2.2.2.2

/-- Lifting the controlled circuit to any finite workspace applies the controlled unitary
tensored with the workspace identity, using six gates and zero queries. -/
theorem knownQubitControl_arbitrary_workspace_semantics :
    ∀ (I : Type) [Fintype I] [DecidableEq I] (p : KnownQubitAngles) (ψ : QState ((Bool × Bool) × I)),
  Run (1 : Matrix ((Bool × Bool) × I) ((Bool × Bool) × I) ℂ)
    (LiftCircuitTo I (knownQubitControlCircuit p)) ψ =
      ApplyGate (TensorGate (ControlledGate (knownQubitUnitary p)) (1 : Matrix I I ℂ)) ψ ∧
  GateCount (LiftCircuitTo I (knownQubitControlCircuit p)) = 6 ∧
  QueryCount (LiftCircuitTo I (knownQubitControlCircuit p)) = 0 := by
  intro I inst₁ inst₂ p ψ
  have hrun : ∀ (gs : List KnownQubitControlStep) (ψ : QState ((Bool × Bool) × I)),
      Run (1 : Matrix ((Bool × Bool) × I) ((Bool × Bool) × I) ℂ)
        (LiftCircuitTo I (knownControlProgramCircuit gs)) ψ
        = ApplyGate (TensorGate (knownControlProgramMatrix gs) (1 : Matrix I I ℂ)) ψ := by
    intro gs ψ
    induction gs generalizing ψ with
    | nil =>
      rw [knownControlProgramCircuit_nil, liftCircuitTo_nil, run_nil,
        knownControlProgramMatrix_nil, tensorGate_one, applyGate_one]
    | cons s gs ih =>
      rw [knownControlProgramCircuit_cons, liftCircuitTo_gate, run_gate, ih,
        ← applyGate_mul, tensorGate_mul, Matrix.one_mul]
      rfl
  refine ⟨?_, ?_, ?_⟩
  · rw [show knownQubitControlCircuit p
        = knownControlProgramCircuit (knownQubitControlSteps p) from rfl,
      hrun, knownControlProgramMatrix_steps]
  · rw [gateCount_liftCircuitTo]
    exact (knownQubitControl_exact_six_gate_table p).2.2.2.2.1
  · rw [queryCount_liftCircuitTo]
    exact (knownQubitControl_exact_six_gate_table p).2.2.2.2.2

/-- The adjoint controlled circuit uses six gates, composing it with the forward circuit gives
the identity with twelve gates, and `k` repetitions control the `k`th power with `6 * k`
gates and zero queries. -/
theorem knownQubitControl_inverse_repeat_real_costs :
    ∀ (p : KnownQubitAngles) (k : ℕ) (ψ : QState (Bool × Bool)),
  Run (1 : Matrix (Bool × Bool) (Bool × Bool) ℂ)
    (knownControlProgramCircuit (knownControlProgramAdjoint (knownQubitControlSteps p))) ψ =
      ApplyGate (ControlledGate (knownQubitUnitary p)ᴴ) ψ ∧
  GateCount (knownControlProgramCircuit (knownControlProgramAdjoint (knownQubitControlSteps p))) = 6 ∧
  Run (1 : Matrix (Bool × Bool) (Bool × Bool) ℂ)
    (knownControlProgramCircuit (knownQubitControlSteps p ++ knownControlProgramAdjoint (knownQubitControlSteps p))) ψ = ψ ∧
  GateCount (knownControlProgramCircuit (knownQubitControlSteps p ++ knownControlProgramAdjoint (knownQubitControlSteps p))) = 12 ∧
  Run (1 : Matrix (Bool × Bool) (Bool × Bool) ℂ) (RepeatCircuit (knownQubitControlCircuit p) k) ψ =
    ApplyGate (ControlledGate ((knownQubitUnitary p) ^ k)) ψ ∧
  GateCount (RepeatCircuit (knownQubitControlCircuit p) k) = 6 * k ∧
  QueryCount (RepeatCircuit (knownQubitControlCircuit p) k) = 0 := by
  intro p k ψ
  have hL : (knownQubitUnitary p)ᴴ * knownQubitUnitary p = 1 := by
    have hh := (Matrix.mem_unitaryGroup_iff').mp (knownQubitUnitary_unitary p)
    rwa [Matrix.star_eq_conjTranspose] at hh
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [run_knownControlProgramCircuit, knownControlProgramMatrix_adjoint_eq,
      knownControlProgramMatrix_steps, controlledGate_conjTranspose]
  · rw [gateCount_knownControlProgramCircuit, knownControlProgramAdjoint_length]
    rfl
  · rw [run_knownControlProgramCircuit, knownControlProgramMatrix_append,
      knownControlProgramMatrix_adjoint_eq, knownControlProgramMatrix_steps,
      controlledGate_conjTranspose, controlledGate_mul, hL, controlledGate_one,
      applyGate_one]
  · rw [gateCount_knownControlProgramCircuit, List.length_append,
      knownControlProgramAdjoint_length]
    rfl
  · rw [show knownQubitControlCircuit p
        = knownControlProgramCircuit (knownQubitControlSteps p) from rfl]
    induction k generalizing ψ with
    | zero =>
      show Run 1 ([] : Circuit (Bool × Bool)) ψ
        = ApplyGate (ControlledGate ((knownQubitUnitary p) ^ 0)) ψ
      rw [run_nil, pow_zero, controlledGate_one, applyGate_one]
    | succ k ih =>
      rw [RepeatCircuit, run_append, run_knownControlProgramCircuit,
        knownControlProgramMatrix_steps, ih, ← applyGate_mul, controlledGate_mul, pow_succ]
  · rw [gateCount_repeatCircuit, (knownQubitControl_exact_six_gate_table p).2.2.2.2.1]
    exact Nat.mul_comm k 6
  · rw [queryCount_repeatCircuit, (knownQubitControl_exact_six_gate_table p).2.2.2.2.2,
    Nat.mul_zero]

end Qatlib.Concepts.MatrixAccess.KnownFrameSynth
