/-
Copyright (c) 2026 Quantum Atlas Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quantum Atlas Contributors
-/

module

public import Qatlib.Concepts.OperatorAccess.EncodedAccess.FreshPositivePower
public import Qatlib.Concepts.QuditTeleport.TeleportCore.BellReferenceProtocol

@[expose] public section
open Qatlib.Concepts.BlockEncoding Qatlib.Concepts.BlockEncoding.Encoding Qatlib.Concepts.BlockEncoding.EncodingCore Qatlib.Concepts.BlockEncoding.LCU Qatlib.Concepts.BlockEncoding.LinearCombination Qatlib.Concepts.BlockEncoding.Postselection Qatlib.Concepts.BlockEncoding.Postselection.Encoding Qatlib.Foundations.BornMetrics.EventProbability Qatlib.Foundations.InstrumentCore.Measurement Qatlib.Foundations.InstrumentCore.ProjectiveMeasurement Qatlib.Foundations.InstrumentCore.ProjectiveMeasurementLaws Qatlib.Foundations.OperatorErrors.OperatorError Qatlib.Concepts.OperatorErrors.Robustness Qatlib.Concepts.OperatorErrors.Robustness.SignalProcessing Qatlib.Concepts.PhaseGeometry.Phase Qatlib.Foundations.PureStateMath.BornBridge Qatlib.Foundations.PureStateMath Qatlib.Foundations.PureStateMath.Reflection Qatlib.Foundations.QueryWordCore.Circuit
open Qatlib.Concepts.PhaseGeometry.Phase

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Qatlib.Concepts.Execution.WorkspaceCP
open Qatlib.Foundations.QueryWordCore.Circuit
open Qatlib.Concepts.CoherentSim.CoherentOAA Qatlib.Foundations.InstrumentCore.ProjectiveMeasurementLaws Qatlib.Foundations.OperatorErrors.OperatorError
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.BlockEncoding.Postselection

open Qatlib.Concepts.OperatorAccess.EncodedAccess
open Qatlib.Concepts.QuditTeleport.TeleportCore

open Qatlib.Concepts.OperatorAccess.EncodedAccess
namespace Qatlib.Concepts.OperatorAccess.EncodedAccess
open Qatlib.Concepts.QueryWordCore.AdjointCircuits Qatlib.Concepts.PhaseGeometry.Phase
open Matrix
open scoped Classical BigOperators Matrix.Norms.L2Operator ComplexOrder

private noncomputable def positiveBellGate : Matrix (Bool × Bool) (Bool × Bool) ℂ :=
  CNOT * TensorGate Hadamard (1 : Matrix Bool Bool ℂ)

/-- The Bell preparation gate `positiveBellGate` is unitary. -/
private theorem positiveBellGate_unitary : positiveBellGate ∈ Matrix.unitaryGroup (Bool × Bool) ℂ :=
  Submonoid.mul_mem _ cnot_unitary (tensorGate_unitary hadamard_unitary (Submonoid.one_mem _))

/-- The Bell preparation gate sends the all-false basis state to `teleportBellResource`. -/
private theorem positiveBellGate_state :
    positiveBellGate *ᵥ Qatlib.Foundations.PureStateMath.Ket (false,false) = teleportBellResource := by
  have hk : (Qatlib.Foundations.PureStateMath.Ket (false,false) : QState (Bool × Bool)) = TensorState (Qatlib.Foundations.PureStateMath.Ket false) (Qatlib.Foundations.PureStateMath.Ket false) := by
    ext ⟨b,c⟩
    cases b <;> cases c <;> simp [Qatlib.Foundations.PureStateMath.Ket, TensorState]
  rw [positiveBellGate, ← Matrix.mulVec_mulVec, hk]
  change CNOT *ᵥ ApplyGate (TensorGate Hadamard 1)
      (TensorState (Qatlib.Foundations.PureStateMath.Ket false) (Qatlib.Foundations.PureStateMath.Ket false)) = _
  rw [applyGate_tensorGate]
  have hh : ApplyGate Hadamard (Qatlib.Foundations.PureStateMath.Ket false) = Plus := by
    ext b
    simp [ApplyGate, Matrix.mulVec, dotProduct, Qatlib.Foundations.PureStateMath.Ket, Plus,
        hadamard_apply_false]
  rw [hh]
  simp [teleportBellResource, ApplyGate]

/-- The reduced density matrix of the prepared Bell state is half the identity. -/
theorem positiveBell_density : purifiedDensity
    ((CNOT * TensorGate Hadamard (1 : Matrix Bool Bool ℂ)) *ᵥ
      Qatlib.Foundations.PureStateMath.Ket (false,false)) =
    (1/2:ℂ) • (1 : Matrix Bool Bool ℂ) := by
  change purifiedDensity
    (positiveBellGate *ᵥ Qatlib.Foundations.PureStateMath.Ket (false,false)) = _
  rw [positiveBellGate_state]
  ext i j
  cases i <;> cases j <;>
    simp [purifiedDensity, teleportBellResource_apply', sqrt2_inv_sq]

/-- The Bell purification power circuit has three gates per power step and postselection
probability equal to the corresponding power of one quarter. -/
theorem bell_purification_actual_power_consumer : ∀ m : ℕ,
  let U := CNOT * TensorGate Hadamard (1 : Matrix Bool Bool ℂ)
  let gs := [TensorGate U (1 : Matrix Bool Bool ℂ),
    purificationSwap (A := Bool) (I := Bool), TensorGate Uᴴ (1 : Matrix Bool Bool ℂ)]
  let F := encodingFiber (I := Bool) (fun _ : Fin m => (false,false))
  purifiedDensity (U *ᵥ Qatlib.Foundations.PureStateMath.Ket (false,false)) = (1/2:ℂ) • (1 : Matrix Bool Bool ℂ) ∧
  GateCount (freshPowerCircuit m gs) = 3*m ∧
  postselectionProbability (freshPowerMatrix m gs) F F (Qatlib.Foundations.PureStateMath.Ket false) = ((1/4:ℝ)^m)

 := by
  intro m
  let : DecidableEq (Bool × Bool) := instDecidableEqProd
  let U := CNOT * TensorGate Hadamard (1 : Matrix Bool Bool ℂ)
  let gs := [TensorGate U (1 : Matrix Bool Bool ℂ),
    purificationSwap (A := Bool) (I := Bool), TensorGate Uᴴ (1 : Matrix Bool Bool ℂ)]
  have hU : U ∈ Matrix.unitaryGroup (Bool × Bool) ℂ := by
    simpa only [U, positiveBellGate] using positiveBellGate_unitary
  have hgs : ∀ V ∈ gs, V ∈ Matrix.unitaryGroup ((Bool × Bool) × Bool) ℂ := by
    intro V hV
    simp only [gs, List.mem_cons, List.not_mem_nil, or_false] at hV
    rcases hV with rfl | rfl | rfl
    · exact tensorGate_unitary hU (Submonoid.one_mem _)
    · exact permMatrix_unitary (fun _ => rfl)
    · exact tensorGate_unitary (by
        rw [Matrix.mem_unitaryGroup_iff, Matrix.star_eq_conjTranspose,
          Matrix.conjTranspose_conjTranspose]
        simpa only [Matrix.mem_unitaryGroup_iff', Matrix.star_eq_conjTranspose] using hU)
        (Submonoid.one_mem _)
  have hbody : macroListMatrix gs = purificationBody U := by
    simp only [gs, macroListMatrix, List.foldl_cons, List.foldl_nil,
      Matrix.mul_one, purificationBody, purificationWord, evaluate, instructionMatrix,
      tensorGate_conjTranspose, Matrix.conjTranspose_one]
  have hc : compress (encodingFiber (false,false)) (macroListMatrix gs)
      (encodingFiber (false,false)) = (1/2:ℂ) • (1 : Matrix Bool Bool ℂ) := by
    rw [hbody]
    exact (purification_actual_positive_block_and_cost U (false,false) hU).2.2.1.encoded.trans
      positiveBell_density
  have h := fresh_positive_actual_power_word m (false,false) gs
    ((1/2:ℂ) • (1 : Matrix Bool Bool ℂ)) hgs hc
  refine ⟨positiveBell_density, ?_, ?_⟩
  · change GateCount (freshPowerCircuit m gs) = 3*m
    simpa only [gs, List.length_cons, List.length_nil, Nat.reduceAdd, Nat.mul_comm] using h.2.2.2.1
  · change postselectionProbability (freshPowerMatrix m gs)
      (encodingFiber (I := Bool) (fun _ : Fin m => (false,false)))
      (encodingFiber (I := Bool) (fun _ : Fin m => (false,false))) (Qatlib.Foundations.PureStateMath.Ket false) = (1/4:ℝ)^m
    rw [postselectionProbability_eq_norm_sq h.1.left_isometry]
    simp only [postselectionVector, h.1.encoded]
    have hv : (((1/2:ℂ) • (1 : Matrix Bool Bool ℂ))^m) *ᵥ Qatlib.Foundations.PureStateMath.Ket false =
        (1/2:ℂ)^m • Qatlib.Foundations.PureStateMath.Ket false := by
      rw [smul_pow, one_pow, Matrix.smul_mulVec, Matrix.one_mulVec]
    rw [hv]
    change ‖(1/2:ℂ)^m • stateVector
        (Qatlib.Foundations.PureStateMath.Ket false : QState Bool)‖^2 = (1/4:ℝ)^m
    have hn : ‖stateVector (Qatlib.Foundations.PureStateMath.Ket false : QState Bool)‖ = 1 :=
      (normalized_iff_stateVector_norm _).mp (normalized_ket false)
    rw [norm_smul, norm_pow, hn, mul_one, ← pow_mul, Nat.mul_comm m 2, pow_mul]
    norm_num

end Qatlib.Concepts.OperatorAccess.EncodedAccess
