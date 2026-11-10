/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.MatrixAccess.KnownFrameSynth.KnownQubitEuler
import Qatlib.Concepts.QueryComplexity.DegreeMethod.LocalCapability
import Qatlib.Foundations.QueryWordCore.Circuit
import Qatlib.Concepts.LocalMachine.LocalTransport.ControlledQueryCircuit
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

inductive KnownQubitControlStep where
  | single : Bool → KnownQubitAngles → KnownQubitControlStep
  | cnot : KnownQubitControlStep

noncomputable def knownControlA (p : KnownQubitAngles) : KnownQubitAngles :=
    ⟨0, p.alpha, p.theta / 2, 0⟩

noncomputable def knownControlB (p : KnownQubitAngles) : KnownQubitAngles :=
  ⟨0, 0, -p.theta / 2, -(p.alpha + p.beta) / 2⟩

noncomputable def knownControlC (p : KnownQubitAngles) : KnownQubitAngles :=
    ⟨0, (p.beta - p.alpha) / 2, 0, 0⟩

noncomputable def knownControlE (p : KnownQubitAngles) : KnownQubitAngles :=
    ⟨p.delta / 2, -p.delta, 0, 0⟩

noncomputable def knownControlStepMatrix : KnownQubitControlStep →
    Matrix (Bool × Bool) (Bool × Bool) ℂ
  | .single true p => TensorGate (knownQubitUnitary p) 1
  | .single false p => TensorGate 1 (knownQubitUnitary p)
  | .cnot => CNOT

noncomputable def knownControlProgramCircuit (gs : List KnownQubitControlStep) :
    Circuit (Bool × Bool) :=
  gs.map (fun s => Step.gate (knownControlStepMatrix s))

noncomputable def knownControlProgramMatrix : List KnownQubitControlStep →
    Matrix (Bool × Bool) (Bool × Bool) ℂ
  | [] => 1
  | s :: gs => knownControlProgramMatrix gs * knownControlStepMatrix s

@[simp] theorem knownControlProgramMatrix_nil :
    knownControlProgramMatrix [] = 1 := rfl

theorem knownControlProgramMatrix_cons (s : KnownQubitControlStep)
    (gs : List KnownQubitControlStep) :
    knownControlProgramMatrix (s :: gs)
      = knownControlProgramMatrix gs * knownControlStepMatrix s := rfl

def knownControlStepAdjoint : KnownQubitControlStep → KnownQubitControlStep
  | .single b p => .single b (knownQubitAngleAdjoint p)
  | .cnot => .cnot

def knownControlProgramAdjoint (gs : List KnownQubitControlStep) : List KnownQubitControlStep :=
  gs.reverse.map knownControlStepAdjoint

noncomputable def knownQubitControlSteps (p : KnownQubitAngles) : List KnownQubitControlStep :=
  [.single false (knownControlC p), .cnot,
   .single false (knownControlB p), .cnot,
   .single false (knownControlA p), .single true (knownControlE p)]

noncomputable def knownQubitControlCircuit (p : KnownQubitAngles) : Circuit (Bool × Bool) :=
  knownControlProgramCircuit (knownQubitControlSteps p)

theorem knownQubitUnitary_controlA (p : KnownQubitAngles) :
    knownQubitUnitary (knownControlA p)
      = qubitEulerPhase p.alpha * qubitEulerRotation (p.theta / 2) := by
  simp only [knownQubitUnitary, knownControlA, Complex.ofReal_zero, zero_mul,
    Complex.exp_zero, one_smul, qubitEulerPhase_zero, Matrix.mul_one]

theorem knownQubitUnitary_controlB (p : KnownQubitAngles) :
    knownQubitUnitary (knownControlB p)
      = qubitEulerRotation (-p.theta / 2) * qubitEulerPhase (-(p.alpha + p.beta) / 2) := by
  simp only [knownQubitUnitary, knownControlB, Complex.ofReal_zero, zero_mul,
    Complex.exp_zero, one_smul, qubitEulerPhase_zero, Matrix.one_mul]

theorem knownQubitUnitary_controlC (p : KnownQubitAngles) :
    knownQubitUnitary (knownControlC p) = qubitEulerPhase ((p.beta - p.alpha) / 2) := by
  simp only [knownQubitUnitary, knownControlC, Complex.ofReal_zero, zero_mul,
    Complex.exp_zero, one_smul, qubitEulerPhase_zero, qubitEulerRotation_zero,
    Matrix.one_mul, Matrix.mul_one]

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

theorem pauliX_mul_self : PauliX * PauliX = (1 : Matrix Bool Bool ℂ) := by
  rw [show PauliX * PauliX = permMatrix Bool.not * permMatrix Bool.not from rfl,
    permMatrix_mul_self Bool.not_not]

theorem pauliX_mul_mul_pauliX (M N : Matrix Bool Bool ℂ) :
    PauliX * (M * N) * PauliX = (PauliX * M * PauliX) * (PauliX * N * PauliX) := by
  simp only [Matrix.mul_assoc]
  rw [← Matrix.mul_assoc PauliX PauliX (N * PauliX), pauliX_mul_self, Matrix.one_mul]

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

theorem applyGate_rz_ket (t : ℝ) (b : Bool) :
    ApplyGate (Rz t) (Qatlib.Foundations.PureStateMath.Ket b)
      = (if b then Complex.exp ((t : ℂ) * Complex.I) else 1) • Qatlib.Foundations.PureStateMath.Ket b := by
  rw [show Rz t = Matrix.diagonal fun a => if a then Complex.exp ((t : ℂ) * Complex.I) else 1
      from rfl, applyGate_diagonal_ket]

theorem tensorState_smul_left {I J : Type*} [Fintype I] [Fintype J] (k : ℂ)
    (ψ : QState I) (χ : QState J) : TensorState (k • ψ) χ = k • TensorState ψ χ := by
  funext p
  simp only [TensorState, Pi.smul_apply, smul_eq_mul]
  ring

theorem tensorState_smul_right {I J : Type*} [Fintype I] [Fintype J] (k : ℂ)
    (ψ : QState I) (χ : QState J) : TensorState ψ (k • χ) = k • TensorState ψ χ := by
  funext p
  simp only [TensorState, Pi.smul_apply, smul_eq_mul]
  ring

theorem applyGate_smul {I : Type*} [Fintype I] [DecidableEq I] (k : ℂ) (M : Matrix I I ℂ)
    (ψ : QState I) : ApplyGate (k • M) ψ = k • ApplyGate M ψ := by
  rw [ApplyGate, ApplyGate, Matrix.smul_mulVec]

theorem knownControlStepMatrix_unitary (s : KnownQubitControlStep) :
    knownControlStepMatrix s ∈ Matrix.unitaryGroup (Bool × Bool) ℂ := by
  cases s with
  | single b p =>
    cases b with
    | true => exact tensorGate_unitary (knownQubitUnitary_unitary p) (Submonoid.one_mem _)
    | false => exact tensorGate_unitary (Submonoid.one_mem _) (knownQubitUnitary_unitary p)
  | cnot => exact cnot_unitary

theorem knownControlProgramMatrix_unitary (gs : List KnownQubitControlStep) :
    knownControlProgramMatrix gs ∈ Matrix.unitaryGroup (Bool × Bool) ℂ := by
  induction gs with
  | nil => exact Submonoid.one_mem _
  | cons s gs ih =>
    rw [knownControlProgramMatrix_cons]
    exact mul_mem_unitaryGroup ih (knownControlStepMatrix_unitary s)

@[simp] theorem knownControlProgramCircuit_nil :
    knownControlProgramCircuit [] = ([] : Circuit (Bool × Bool)) := rfl

theorem knownControlProgramCircuit_cons (s : KnownQubitControlStep)
    (gs : List KnownQubitControlStep) :
    knownControlProgramCircuit (s :: gs)
      = Step.gate (knownControlStepMatrix s) :: knownControlProgramCircuit gs := rfl

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

theorem isUnitaryCircuit_knownControlProgramCircuit (gs : List KnownQubitControlStep) :
    IsUnitaryCircuit (knownControlProgramCircuit gs) := by
  induction gs with
  | nil => exact isUnitaryCircuit_nil
  | cons s gs ih =>
    rw [knownControlProgramCircuit_cons, isUnitaryCircuit_gate]
    exact ⟨knownControlStepMatrix_unitary s, ih⟩

theorem queryCount_knownControlProgramCircuit (gs : List KnownQubitControlStep) :
    QueryCount (knownControlProgramCircuit gs) = 0 := by
  induction gs with
  | nil => rfl
  | cons s gs ih => rw [knownControlProgramCircuit_cons, queryCount_gate, ih]

theorem gateCount_knownControlProgramCircuit (gs : List KnownQubitControlStep) :
    GateCount (knownControlProgramCircuit gs) = gs.length := by
  induction gs with
  | nil => rfl
  | cons s gs ih =>
    rw [knownControlProgramCircuit_cons, gateCount_gate, ih, List.length_cons]

theorem knownControlProgramMatrix_append (gs hs : List KnownQubitControlStep) :
    knownControlProgramMatrix (gs ++ hs)
      = knownControlProgramMatrix hs * knownControlProgramMatrix gs := by
  induction gs with
  | nil => simp
  | cons s gs ih =>
    rw [List.cons_append, knownControlProgramMatrix, knownControlProgramMatrix, ih,
      Matrix.mul_assoc]

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

theorem knownControlProgramAdjoint_length (gs : List KnownQubitControlStep) :
    (knownControlProgramAdjoint gs).length = gs.length := by
  simp [knownControlProgramAdjoint]

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

theorem controlledGate_one : ControlledGate (1 : Matrix Bool Bool ℂ) = 1 := by
  ext ⟨c, i⟩ ⟨c', j⟩
  simp only [ControlledGate, BlockDiag, Matrix.of_apply]
  rcases c <;> rcases c' <;> simp [Matrix.one_apply]

theorem controlledGate_mul (U V : Matrix Bool Bool ℂ) :
    ControlledGate U * ControlledGate V = ControlledGate (U * V) := by
  ext ⟨c, i⟩ ⟨c', j⟩
  simp only [ControlledGate, BlockDiag, Matrix.of_apply, Matrix.mul_apply,
    Fintype.sum_prod_type]
  rcases c <;> rcases c' <;> simp [Matrix.one_apply]
  rw [show (U * V) i j = U i true * V true j + U i false * V false j from by
    rw [Matrix.mul_apply, Fintype.sum_bool]]

theorem controlledGate_conjTranspose (U : Matrix Bool Bool ℂ) :
    (ControlledGate U)ᴴ = ControlledGate Uᴴ := by
  ext ⟨c, i⟩ ⟨c', j⟩
  simp only [Matrix.conjTranspose_apply, ControlledGate, BlockDiag, Matrix.of_apply]
  rcases c <;> rcases c' <;> simp [Matrix.one_apply, eq_comm]

theorem controlledGate_eq_controlOracle (U : Matrix Bool Bool ℂ) :
    ControlledGate U = controlOracle U := by
  ext ⟨c, i⟩ ⟨c', j⟩
  simp only [ControlledGate, BlockDiag, controlOracle, Qatlib.Concepts.BlockEncoding.LCU.select,
    Matrix.of_apply]
  rcases c <;> rcases c' <;> simp

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
