/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.MatrixAccess.KnownFrameSynth.KnownQubitControl
set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

open Qatlib.Concepts.PhaseGeometry.Phase Qatlib.Concepts.QspSimulation.WordModel

open Qatlib.Concepts.MatrixAccess.KnownFrameSynth

open Qatlib.Foundations.QueryWordCore.Circuit
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.QueryComplexity.DegreeMethod

namespace Qatlib.Concepts.HspRecovery.ReductionCore

open Matrix

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false

noncomputable def knownHadamardAngles : KnownQubitAngles :=
  ⟨Real.pi / 2, -Real.pi, Real.pi / 2, 0⟩

noncomputable def knownRzAngles (t : ℝ) : KnownQubitAngles := ⟨t / 2, -t, 0, 0⟩

noncomputable def knownControlledHadamard : Circuit (Bool × Bool) :=
  knownQubitControlCircuit knownHadamardAngles

noncomputable def knownControlledRz (t : ℝ) : Circuit (Bool × Bool) :=
  knownQubitControlCircuit (knownRzAngles t)

noncomputable def knownOneBitPhaseCircuit (t : ℝ) : Circuit (Bool × Bool) :=
  [Step.gate (TensorGate Hadamard (1 : Matrix Bool Bool ℂ))] ++ knownControlledRz t
    ++ [Step.gate (TensorGate Hadamard (1 : Matrix Bool Bool ℂ))]

noncomputable def knownTwoRotationPhaseCircuit (s t : ℝ) : Circuit (Bool × Bool) :=
  [Step.gate (TensorGate Hadamard (1 : Matrix Bool Bool ℂ))] ++ knownControlledRz s
    ++ knownControlledRz t ++ [Step.gate (TensorGate Hadamard (1 : Matrix Bool Bool ℂ))]

theorem exp_pi_half_mul_I : Complex.exp (((Real.pi / 2 : ℝ) : ℂ) * Complex.I) = Complex.I := by
  simp only [Complex.ofReal_div, Complex.ofReal_ofNat, Complex.exp_pi_div_two_mul_I]

theorem sqrt2_half : ((Real.sqrt 2 / 2 : ℝ) : ℂ) = ((Real.sqrt 2 : ℝ) : ℂ)⁻¹ := by
  rw [Complex.ofReal_div]
  have h : ((Real.sqrt 2 : ℝ) : ℂ) ^ 2 = ((2 : ℝ) : ℂ) := by
    rw [pow_two, ← Complex.ofReal_mul, Real.mul_self_sqrt (by norm_num)]
  field_simp
  exact h

theorem exp_neg_pi_half_mul_I :
    Complex.exp (((((-Real.pi) / 2 : ℝ) : ℂ) * Complex.I)) = -Complex.I := by
  have h : Complex.exp (((((-Real.pi) / 2 : ℝ) : ℂ) * Complex.I))
      = (Complex.exp (((Real.pi / 2 : ℝ) : ℂ) * Complex.I))⁻¹ := by
    rw [← Complex.exp_neg]
    congr 1
    push_cast
    ring
  rw [h, exp_pi_half_mul_I, Complex.inv_I]

theorem exp_tt_pi_half_mul_I :
    Complex.exp ((-((((-Real.pi) / 2 : ℝ) : ℂ)) * Complex.I)) = Complex.I := by
  have h : ((((-Real.pi) / 2 : ℝ) : ℂ)) = -(((Real.pi / 2 : ℝ) : ℂ)) := by
    push_cast
    ring
  rw [h, neg_neg, exp_pi_half_mul_I]

theorem keyI_neg : ∀ c : ℂ, Complex.I * (-Complex.I * c) = c := by
  intro c
  rw [← mul_assoc, mul_neg, Complex.I_mul_I, neg_neg, one_mul]

theorem keyI_pos : ∀ c : ℂ, Complex.I * (Complex.I * c) = -c := by
  intro c
  rw [← mul_assoc, Complex.I_mul_I, neg_one_mul]

theorem knownQubitUnitary_knownHadamardAngles :
    knownQubitUnitary knownHadamardAngles = Hadamard := by
  ext i j
  rcases i <;> rcases j <;>
    simp only [knownQubitUnitary, knownHadamardAngles, qubitEulerPhase_ff,
      qubitEulerPhase_ft, qubitEulerPhase_tf, qubitEulerPhase_tt, qubitEulerRotation_ff,
      qubitEulerRotation_ft, qubitEulerRotation_tf, qubitEulerRotation_tt, Matrix.mul_apply,
      Fintype.sum_bool, PauliZ, Matrix.diagonal_apply, Matrix.smul_apply, Hadamard,
      Matrix.of_apply, if_true, if_false, Complex.ofReal_zero, zero_div, Complex.exp_zero,
      mul_one, zero_mul, neg_zero, mul_zero, zero_add, add_zero]
  · rw [smul_eq_mul, exp_pi_half_mul_I, exp_neg_pi_half_mul_I, keyI_neg,
      show Real.pi / 2 / 2 = Real.pi / 4 from by ring, Real.cos_pi_div_four, sqrt2_half]
    simp
  · rw [smul_eq_mul, exp_pi_half_mul_I, exp_neg_pi_half_mul_I, keyI_neg,
      show Real.pi / 2 / 2 = Real.pi / 4 from by ring, Real.sin_pi_div_four, sqrt2_half]
    simp
  · rw [smul_eq_mul, exp_pi_half_mul_I, exp_tt_pi_half_mul_I, keyI_pos,
      show Real.pi / 2 / 2 = Real.pi / 4 from by ring, Real.sin_pi_div_four, sqrt2_half]
    simp
  · rw [smul_eq_mul, exp_pi_half_mul_I, exp_tt_pi_half_mul_I, keyI_pos,
      show Real.pi / 2 / 2 = Real.pi / 4 from by ring, Real.cos_pi_div_four, sqrt2_half]
    simp

theorem knownQubitUnitary_knownRzAngles (t : ℝ) :
    knownQubitUnitary (knownRzAngles t) = Rz t := by
  ext i j
  rcases i <;> rcases j <;>
    simp only [knownQubitUnitary, knownRzAngles, qubitEulerPhase_ff, qubitEulerPhase_ft,
      qubitEulerPhase_tf, qubitEulerPhase_tt, qubitEulerRotation_zero, qubitEulerPhase_zero,
      Matrix.mul_one, Matrix.one_mul, Rz, Matrix.diagonal_apply, Matrix.smul_apply,
      Matrix.one_apply, if_true, if_false]
  · rw [smul_eq_mul, if_neg (by simp), ← Complex.exp_add,
      show ((t / 2 : ℝ) : ℂ) * Complex.I + ((((-t) / 2 : ℝ) : ℂ) * Complex.I) = 0 from by
        push_cast
        ring,
      Complex.exp_zero]
  · simp
  · simp
  · rw [smul_eq_mul, ← Complex.exp_add]
    congr 1
    push_cast
    ring

theorem knownControlledHadamard_actual_consumer :
    knownQubitUnitary knownHadamardAngles = Hadamard ∧
  knownControlledHadamard = knownQubitControlCircuit knownHadamardAngles ∧
  (∀ ψ : QState Bool,
    Run (1 : Matrix (Bool × Bool) (Bool × Bool) ℂ) knownControlledHadamard (TensorState (Qatlib.Foundations.PureStateMath.Ket false) ψ) =
      TensorState (Qatlib.Foundations.PureStateMath.Ket false) ψ) ∧
  Run (1 : Matrix (Bool × Bool) (Bool × Bool) ℂ) knownControlledHadamard (Qatlib.Foundations.PureStateMath.Ket (true,false)) =
    TensorState (Qatlib.Foundations.PureStateMath.Ket true) Plus ∧
  GateCount knownControlledHadamard = 6 ∧ QueryCount knownControlledHadamard = 0 := by
  refine ⟨knownQubitUnitary_knownHadamardAngles, rfl, ?_, ?_,
    (knownQubitControl_exact_six_gate_table knownHadamardAngles).2.2.2.2.1,
    (knownQubitControl_exact_six_gate_table knownHadamardAngles).2.2.2.2.2⟩
  · intro ψ
    rw [show knownControlledHadamard = knownQubitControlCircuit knownHadamardAngles from rfl,
      (knownQubitControl_exact_controlled_semantics knownHadamardAngles
        (TensorState (Qatlib.Foundations.PureStateMath.Ket false) ψ)).2.2.1, knownQubitUnitary_knownHadamardAngles]
    exact applyGate_isControlledGate_ket_false (isControlledGate_controlledGate Hadamard) ψ
  · rw [show knownControlledHadamard = knownQubitControlCircuit knownHadamardAngles from rfl,
      (knownQubitControl_exact_controlled_semantics knownHadamardAngles
        (Qatlib.Foundations.PureStateMath.Ket (true, false))).2.2.1, knownQubitUnitary_knownHadamardAngles,
      ← tensorState_ket_ket,
      applyGate_isControlledGate_ket_true (isControlledGate_controlledGate Hadamard),
      applyGate_hadamard_ket_false]

theorem applyGate_controlledRz_tensorState_ket_true (t : ℝ) (χ : QState Bool) :
    ApplyGate (ControlledGate (Rz t)) (TensorState χ (Qatlib.Foundations.PureStateMath.Ket true))
      = TensorState (ApplyGate (Rz t) χ) (Qatlib.Foundations.PureStateMath.Ket true) := by
  funext p
  obtain ⟨c, y⟩ := p
  rcases c <;> rcases y <;>
    simp [TensorState, Qatlib.Foundations.PureStateMath.Ket, ControlledGate, BlockDiag, Matrix.of_apply, Rz,
      Matrix.diagonal_apply, ApplyGate, Matrix.mulVec, dotProduct, Matrix.mul_apply,
      Fintype.sum_bool, Fintype.sum_prod_type, Matrix.one_apply, if_true, if_false]

theorem plus_eq : Plus = ((Real.sqrt 2 : ℂ)⁻¹) • (Qatlib.Foundations.PureStateMath.Ket false + Qatlib.Foundations.PureStateMath.Ket true) := by
  funext b
  rcases b <;> simp [Plus, Hadamard, Qatlib.Foundations.PureStateMath.Ket, Pi.smul_apply,
      smul_eq_mul]

theorem measureProb_control_false (χ : QState Bool) :
    MeasureProb (TensorState χ (Qatlib.Foundations.PureStateMath.Ket true)) ({false} ×ˢ (Finset.univ : Finset Bool))
      = ‖χ false‖ ^ 2 := by
  simp [MeasureProb, Finset.sum_product, Fintype.sum_bool, BornProb, TensorState, Qatlib.Foundations.PureStateMath.Ket,
    add_zero, mul_one, zero_mul]

theorem hadamard_rz_plus_apply_false (t : ℝ) :
    (ApplyGate (Hadamard * Rz t) Plus) false
      = (1 + Complex.exp ((t : ℂ) * Complex.I)) / 2 := by
  have hA : ((Real.sqrt 2 : ℂ))⁻¹ * Complex.exp ((t : ℂ) * Complex.I)
        * ((Real.sqrt 2 : ℂ))⁻¹ + ((Real.sqrt 2 : ℂ))⁻¹ * ((Real.sqrt 2 : ℂ))⁻¹
      = (1 + Complex.exp ((t : ℂ) * Complex.I)) / 2 := by
    rw [show ((Real.sqrt 2 : ℂ))⁻¹ * Complex.exp ((t : ℂ) * Complex.I)
          * ((Real.sqrt 2 : ℂ))⁻¹
        = Complex.exp ((t : ℂ) * Complex.I) * (((Real.sqrt 2 : ℂ))⁻¹
            * ((Real.sqrt 2 : ℂ))⁻¹) from by ring,
      inv_sqrt2_mul_self,
      show (1 + Complex.exp ((t : ℂ) * Complex.I)) / 2
        = Complex.exp ((t : ℂ) * Complex.I) * ((2 : ℂ))⁻¹ + ((2 : ℂ))⁻¹ from by
        rw [div_eq_inv_mul]
        ring]
  simp only [ApplyGate, Matrix.mulVec, dotProduct, Matrix.mul_apply, Fintype.sum_bool,
    Plus, Hadamard, Rz, Matrix.diagonal_apply, Matrix.one_apply]
  simpa using! hA

theorem hadamard_rz_plus_apply_true (t : ℝ) :
    (ApplyGate (Hadamard * Rz t) Plus) true
      = (1 - Complex.exp ((t : ℂ) * Complex.I)) / 2 := by
  have hA : -(((Real.sqrt 2 : ℂ))⁻¹ * Complex.exp ((t : ℂ) * Complex.I)
        * ((Real.sqrt 2 : ℂ))⁻¹) + ((Real.sqrt 2 : ℂ))⁻¹ * ((Real.sqrt 2 : ℂ))⁻¹
      = (1 - Complex.exp ((t : ℂ) * Complex.I)) / 2 := by
    rw [show -(((Real.sqrt 2 : ℂ))⁻¹ * Complex.exp ((t : ℂ) * Complex.I)
          * ((Real.sqrt 2 : ℂ))⁻¹)
        = -(Complex.exp ((t : ℂ) * Complex.I) * (((Real.sqrt 2 : ℂ))⁻¹
            * ((Real.sqrt 2 : ℂ))⁻¹)) from by ring,
      inv_sqrt2_mul_self,
      show (1 - Complex.exp ((t : ℂ) * Complex.I)) / 2
        = ((2 : ℂ))⁻¹ - Complex.exp ((t : ℂ) * Complex.I) * ((2 : ℂ))⁻¹ from by
        rw [div_eq_inv_mul]
        ring]
    ring
  simp only [ApplyGate, Matrix.mulVec, dotProduct, Matrix.mul_apply, Fintype.sum_bool,
    Plus, Hadamard, Rz, Matrix.diagonal_apply, Matrix.one_apply]
  simpa using! hA

theorem norm_one_plus_exp_half (t : ℝ) :
    ‖(1 + Complex.exp ((t : ℂ) * Complex.I)) / 2‖ ^ 2 = (1 + Real.cos t) / 2 := by
  have e1 : Complex.normSq ((1 : ℂ) + Complex.exp ((t : ℂ) * Complex.I))
      = 2 + 2 * Real.cos t := by
    rw [Complex.normSq_apply, Complex.add_re, Complex.add_im, Complex.one_re,
      Complex.one_im, Complex.exp_ofReal_mul_I_re, Complex.exp_ofReal_mul_I_im]
    nlinarith [Real.sin_sq_add_cos_sq t]
  rw [show ‖(1 + Complex.exp ((t : ℂ) * Complex.I)) / 2‖ ^ 2
      = Complex.normSq (1 + Complex.exp ((t : ℂ) * Complex.I)) / 4 from by
      rw [norm_div, div_pow, ← Complex.normSq_eq_norm_sq]
      norm_num, e1]
  ring

theorem run_knownOneBitPhaseCircuit (t : ℝ) :
    Run (1 : Matrix (Bool × Bool) (Bool × Bool) ℂ) (knownOneBitPhaseCircuit t) (Qatlib.Foundations.PureStateMath.Ket (false, true))
      = TensorState (ApplyGate (Hadamard * Rz t) Plus) (Qatlib.Foundations.PureStateMath.Ket true) := by
  rw [knownOneBitPhaseCircuit, run_append, run_append, run_gate, run_nil, run_gate, run_nil,
    ← tensorState_ket_ket, applyGate_tensorGate, applyGate_hadamard_ket_false, applyGate_one]
  rw [knownControlledRz,
    (knownQubitControl_exact_controlled_semantics (knownRzAngles t)
      (TensorState Plus (Qatlib.Foundations.PureStateMath.Ket true))).2.2.1,
    knownQubitUnitary_knownRzAngles t, applyGate_controlledRz_tensorState_ket_true]
  rw [applyGate_tensorGate, applyGate_one, applyGate_mul]

theorem knownControlledRz_one_bit_phase_actual_consumer :
    ∀ t : ℝ,
  knownQubitUnitary (knownRzAngles t) = Rz t ∧
  knownControlledRz t = knownQubitControlCircuit (knownRzAngles t) ∧
  Run (1 : Matrix (Bool × Bool) (Bool × Bool) ℂ) (knownControlledRz t) (TensorState Plus (Qatlib.Foundations.PureStateMath.Ket true)) =
    TensorState (ApplyGate (Rz t) Plus) (Qatlib.Foundations.PureStateMath.Ket true) ∧
  MeasureProb (Run (1 : Matrix (Bool × Bool) (Bool × Bool) ℂ) (knownOneBitPhaseCircuit t) (Qatlib.Foundations.PureStateMath.Ket (false,true)))
    ({false} ×ˢ (Finset.univ : Finset Bool)) = (1 + Real.cos t) / 2 ∧
  GateCount (knownOneBitPhaseCircuit t) = 8 ∧ QueryCount (knownOneBitPhaseCircuit t) = 0 := by
  intro t
  refine ⟨knownQubitUnitary_knownRzAngles t, rfl, ?_, ?_, ?_, ?_⟩
  · rw [knownControlledRz,
      (knownQubitControl_exact_controlled_semantics (knownRzAngles t)
        (TensorState Plus (Qatlib.Foundations.PureStateMath.Ket true))).2.2.1,
      knownQubitUnitary_knownRzAngles, applyGate_controlledRz_tensorState_ket_true]
  · rw [run_knownOneBitPhaseCircuit, measureProb_control_false, hadamard_rz_plus_apply_false,
      norm_one_plus_exp_half]
  · rw [knownOneBitPhaseCircuit]
    simp only [gateCount_append, gateCount_gate, gateCount_nil,
      gateCount_knownControlProgramCircuit]
    rfl
  · rw [knownOneBitPhaseCircuit, queryCount_append, queryCount_append, queryCount_gate,
      queryCount_nil, zero_add, add_zero,
      show knownControlledRz t = knownQubitControlCircuit (knownRzAngles t) from rfl,
      show knownQubitControlCircuit (knownRzAngles t)
        = knownControlProgramCircuit (knownQubitControlSteps (knownRzAngles t)) from rfl,
      queryCount_knownControlProgramCircuit]

theorem hadamard_rz_rz_plus_apply_false (s t : ℝ) :
    (ApplyGate (Hadamard * (Rz t * Rz s)) Plus) false
      = (1 + Complex.exp (((t + s : ℝ) : ℂ) * Complex.I)) / 2 := by
  simp only [ApplyGate, Matrix.mulVec, dotProduct, Matrix.mul_apply, Fintype.sum_bool,
    Plus, Hadamard, Rz, Matrix.diagonal_apply, Matrix.one_apply]
  norm_num
  rw [← Complex.exp_add,
    show ((t : ℂ)) * Complex.I + ((s : ℂ)) * Complex.I = ((t + s : ℝ) : ℂ) * Complex.I from by
      push_cast
      ring,
    show ((t + s : ℝ) : ℂ) = ((t : ℂ)) + ((s : ℂ)) from by
      push_cast
      ring]
  have hA : ((Real.sqrt 2 : ℂ))⁻¹ * Complex.exp (((t : ℂ) + (s : ℂ)) * Complex.I)
      * ((Real.sqrt 2 : ℂ))⁻¹ + ((Real.sqrt 2 : ℂ))⁻¹ * ((Real.sqrt 2 : ℂ))⁻¹
      = (1 + Complex.exp (((t : ℂ) + (s : ℂ)) * Complex.I)) / 2 := by
    rw [show ((Real.sqrt 2 : ℂ))⁻¹ * Complex.exp (((t : ℂ) + (s : ℂ)) * Complex.I)
          * ((Real.sqrt 2 : ℂ))⁻¹
        = Complex.exp (((t : ℂ) + (s : ℂ)) * Complex.I) * (((Real.sqrt 2 : ℂ))⁻¹
            * ((Real.sqrt 2 : ℂ))⁻¹) from by ring, inv_sqrt2_mul_self,
      show (1 + Complex.exp (((t : ℂ) + (s : ℂ)) * Complex.I)) / 2
        = Complex.exp (((t : ℂ) + (s : ℂ)) * Complex.I) * ((2 : ℂ))⁻¹ + ((2 : ℂ))⁻¹ from by
        rw [div_eq_inv_mul]
        ring]
  exact hA

theorem hadamard_rz_rz_plus_apply_true (s t : ℝ) :
    (ApplyGate (Hadamard * (Rz t * Rz s)) Plus) true
      = (1 - Complex.exp (((t + s : ℝ) : ℂ) * Complex.I)) / 2 := by
  simp only [ApplyGate, Matrix.mulVec, dotProduct, Matrix.mul_apply, Fintype.sum_bool,
    Plus, Hadamard, Rz, Matrix.diagonal_apply, Matrix.one_apply]
  norm_num
  rw [← Complex.exp_add,
    show ((t : ℂ)) * Complex.I + ((s : ℂ)) * Complex.I = ((t + s : ℝ) : ℂ) * Complex.I from by
      push_cast
      ring,
    show ((t + s : ℝ) : ℂ) = ((t : ℂ)) + ((s : ℂ)) from by
      push_cast
      ring]
  have hA : -(((Real.sqrt 2 : ℂ))⁻¹ * Complex.exp (((t : ℂ) + (s : ℂ)) * Complex.I)
      * ((Real.sqrt 2 : ℂ))⁻¹) + ((Real.sqrt 2 : ℂ))⁻¹ * ((Real.sqrt 2 : ℂ))⁻¹
      = (1 - Complex.exp (((t : ℂ) + (s : ℂ)) * Complex.I)) / 2 := by
    rw [show -(((Real.sqrt 2 : ℂ))⁻¹ * Complex.exp (((t : ℂ) + (s : ℂ)) * Complex.I)
          * ((Real.sqrt 2 : ℂ))⁻¹)
        = -(Complex.exp (((t : ℂ) + (s : ℂ)) * Complex.I) * (((Real.sqrt 2 : ℂ))⁻¹
            * ((Real.sqrt 2 : ℂ))⁻¹)) from by ring, inv_sqrt2_mul_self,
      show (1 - Complex.exp (((t : ℂ) + (s : ℂ)) * Complex.I)) / 2
        = ((2 : ℂ))⁻¹ - Complex.exp (((t : ℂ) + (s : ℂ)) * Complex.I) * ((2 : ℂ))⁻¹ from by
        rw [div_eq_inv_mul]
        ring]
    ring
  exact hA

theorem norm_one_plus_exp_half' (s t : ℝ) :
    ‖(1 + Complex.exp (((t + s : ℝ) : ℂ) * Complex.I)) / 2‖ ^ 2 = (1 + Real.cos (s + t)) / 2 := by
  have e1 : Complex.normSq ((1 : ℂ) + Complex.exp (((t + s : ℝ) : ℂ) * Complex.I))
      = 2 + 2 * Real.cos (t + s) := by
    rw [Complex.normSq_apply, Complex.add_re, Complex.add_im, Complex.one_re,
      Complex.one_im, Complex.exp_ofReal_mul_I_re, Complex.exp_ofReal_mul_I_im]
    nlinarith [Real.sin_sq_add_cos_sq (t + s)]
  rw [norm_div, div_pow, ← Complex.normSq_eq_norm_sq]
  have h2 : ((‖(2 : ℂ)‖) ^ 2) = 4 := by norm_num
  rw [h2, e1]
  ring

theorem run_knownTwoRotationPhaseCircuit (s t : ℝ) :
    Run (1 : Matrix (Bool × Bool) (Bool × Bool) ℂ) (knownTwoRotationPhaseCircuit s t)
      (Qatlib.Foundations.PureStateMath.Ket (false, true))
      = TensorState (ApplyGate (Hadamard * (Rz t * Rz s)) Plus) (Qatlib.Foundations.PureStateMath.Ket true) := by
  rw [knownTwoRotationPhaseCircuit, run_append, run_append, run_append, run_gate, run_nil,
    run_gate, run_nil, ← tensorState_ket_ket, applyGate_tensorGate,
    applyGate_hadamard_ket_false, applyGate_one]
  have hruns : Run (1 : Matrix (Bool × Bool) (Bool × Bool) ℂ)
      (knownQubitControlCircuit (knownRzAngles s)) (TensorState Plus (Qatlib.Foundations.PureStateMath.Ket true))
      = TensorState (ApplyGate (Rz s) Plus) (Qatlib.Foundations.PureStateMath.Ket true) := by
    rw [(knownQubitControl_exact_controlled_semantics (knownRzAngles s)
        (TensorState Plus (Qatlib.Foundations.PureStateMath.Ket true))).2.2.1, knownQubitUnitary_knownRzAngles s,
      applyGate_controlledRz_tensorState_ket_true]
  rw [show knownControlledRz s = knownQubitControlCircuit (knownRzAngles s) from rfl, hruns]
  have hrunt : Run (1 : Matrix (Bool × Bool) (Bool × Bool) ℂ)
      (knownQubitControlCircuit (knownRzAngles t))
      (TensorState (ApplyGate (Rz s) Plus) (Qatlib.Foundations.PureStateMath.Ket true))
      = TensorState (ApplyGate (Rz t) (ApplyGate (Rz s) Plus)) (Qatlib.Foundations.PureStateMath.Ket true) := by
    rw [(knownQubitControl_exact_controlled_semantics (knownRzAngles t)
        (TensorState (ApplyGate (Rz s) Plus) (Qatlib.Foundations.PureStateMath.Ket true))).2.2.1,
      knownQubitUnitary_knownRzAngles t, applyGate_controlledRz_tensorState_ket_true]
  rw [show knownControlledRz t = knownQubitControlCircuit (knownRzAngles t) from rfl, hrunt]
  rw [applyGate_tensorGate, applyGate_one, applyGate_mul, applyGate_mul]

theorem knownControlledRz_two_rotation_phase_actual_consumer :
    ∀ s t : ℝ,
  MeasureProb (Run (1 : Matrix (Bool × Bool) (Bool × Bool) ℂ)
    (knownTwoRotationPhaseCircuit s t) (Qatlib.Foundations.PureStateMath.Ket (false,true)))
      ({false} ×ˢ (Finset.univ : Finset Bool)) = (1 + Real.cos (s + t)) / 2 ∧
  GateCount (knownTwoRotationPhaseCircuit s t) = 14 ∧ QueryCount (knownTwoRotationPhaseCircuit s t) = 0 ∧
  (s + t = Real.pi → Run (1 : Matrix (Bool × Bool) (Bool × Bool) ℂ)
    (knownTwoRotationPhaseCircuit s t) (Qatlib.Foundations.PureStateMath.Ket (false,true)) = Qatlib.Foundations.PureStateMath.Ket (true,true)) := by
  intro s t
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [run_knownTwoRotationPhaseCircuit, measureProb_control_false,
      hadamard_rz_rz_plus_apply_false, norm_one_plus_exp_half']
  · rw [knownTwoRotationPhaseCircuit]
    simp only [gateCount_append, gateCount_gate, gateCount_nil,
      gateCount_knownControlProgramCircuit]
    rfl
  · rw [knownTwoRotationPhaseCircuit, queryCount_append, queryCount_append,
      queryCount_append, queryCount_gate, queryCount_nil, zero_add, add_zero]
    rw [show knownControlledRz s = knownQubitControlCircuit (knownRzAngles s) from rfl,
      show knownQubitControlCircuit (knownRzAngles s)
        = knownControlProgramCircuit (knownQubitControlSteps (knownRzAngles s)) from rfl,
      queryCount_knownControlProgramCircuit,
      show knownControlledRz t = knownQubitControlCircuit (knownRzAngles t) from rfl,
      show knownQubitControlCircuit (knownRzAngles t)
        = knownControlProgramCircuit (knownQubitControlSteps (knownRzAngles t)) from rfl,
      queryCount_knownControlProgramCircuit]
  · intro hst
    have hexp : Complex.exp (((t + s : ℝ) : ℂ) * Complex.I) = -1 := by
      rw [show t + s = s + t from by ring, hst, Complex.exp_pi_mul_I]
    have hket : ApplyGate (Hadamard * (Rz t * Rz s)) Plus = Qatlib.Foundations.PureStateMath.Ket true := by
      funext b
      cases b with
      | false =>
        rw [hadamard_rz_rz_plus_apply_false, hexp]
        simp [Qatlib.Foundations.PureStateMath.Ket]
      | true =>
        rw [hadamard_rz_rz_plus_apply_true, hexp]
        simp [Qatlib.Foundations.PureStateMath.Ket]
    rw [run_knownTwoRotationPhaseCircuit, hket, tensorState_ket_ket]

end Qatlib.Concepts.HspRecovery.ReductionCore
