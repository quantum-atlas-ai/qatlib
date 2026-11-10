/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.AmplitudeCore.PreparedReadout.PhysicalHistory.BinaryClockSignalWord
import Qatlib.Concepts.GateVocabulary.LocalReflectionGates
set_option backward.isDefEq.respectTransparency false
set_option warningAsError false

set_option autoImplicit false

namespace Qatlib.Concepts.AmplitudeCore.PreparedReadout.PhysicalHistory.BinaryClockSignalInitialization

open Matrix
open Qatlib.Foundations.QueryWordCore.Circuit
open Qatlib.Concepts.QspSimulation.Achievability.WellFormedAdjointCircuit
open Qatlib.Concepts.CoherentSim.CoherentOAA Qatlib.Foundations.InstrumentCore.ProjectiveMeasurementLaws Qatlib.Foundations.OperatorErrors.OperatorError
open Qatlib.Concepts.CoherentSim.CoherentOAA Qatlib.Foundations.InstrumentCore.ProjectiveMeasurementLaws Qatlib.Foundations.OperatorErrors.OperatorError
open Qatlib.Concepts.LocalMachine.LocalTransport
open Qatlib.Concepts.QsvtCore.QueryLowerBound
open Qatlib.Concepts.QspSimulation.JacobiAnger
open Qatlib.Concepts.BlockEncoding.EncodingCore
open Qatlib.Concepts.Execution.WorkspaceCP
open Qatlib.Concepts.ReferenceError.RefTraceError
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.BlockEncoding.LCU Qatlib.Foundations.PureStateMath.BornBridge Qatlib.Concepts.CopyEvolution.Discriminate
open Qatlib.Concepts.QueryWordCore.AdjointCircuits
open Qatlib.Concepts.CoherentSim.CoherentOAA.SignalProcessing
open Qatlib.Concepts.NativeNumerics.PhaseSynthesis
open Qatlib.Concepts.SignalPrimitive.PhaseFrontend
open Qatlib.Concepts.PhaseGeometry.Phase
open Qatlib.Concepts.BlockEncoding
open Qatlib.Concepts.BlockEncoding.Encoding
open Qatlib.Concepts.BlockEncoding.Postselection.Encoding
open Qatlib.Concepts.OperatorErrors.Robustness.SignalProcessing
open Matrix Qatlib.Concepts.BlockEncoding
open Qatlib.Concepts.BlockEncoding.Encoding
open Qatlib.Concepts.BlockEncoding.Postselection.Encoding
open Qatlib.Concepts.QueryWordCore.AdjointCircuits
open Qatlib.Concepts.CoherentSim.CoherentOAA.SignalProcessing
open Qatlib.Concepts.SignalPrimitive.PhaseFrontend Qatlib.Concepts.PhaseGeometry.Phase
open Qatlib.Concepts.OperatorErrors.Robustness.SignalProcessing
open Qatlib.Concepts.NativeNumerics.PhaseSynthesis
open Qatlib.Concepts.QspSimulation.Achievability
open Qatlib.Concepts.AmplitudeCore.PreparedReadout.PhysicalHistory

open Qatlib.Concepts.GateVocabulary.LocalReflectionGates
open scoped Classical BigOperators

abbrev SimulatorSpace (H : Type) := BinaryClockSignalWord.SimulatorSpace H

private noncomputable abbrev matmul {X Y Z : Type} [Fintype Y]
    (M : Matrix X Y ℂ) (N : Matrix Y Z ℂ) : Matrix X Z ℂ :=
  @HMul.hMul (Matrix X Y ℂ) (Matrix Y Z ℂ) (Matrix X Z ℂ)
    Matrix.instHMulOfFintypeOfMulOfAddCommMonoid M N

noncomputable def baseFrame {H I : Type} (F : Matrix H I ℂ) :
    Matrix (SimulatorSpace H) I ℂ := fun x i =>
  if x.1 = false then
    if x.2.1 = false then
      if x.2.2.1 = false then F x.2.2.2 i else 0
    else 0
  else 0

variable {H : Type} [Fintype H] [DecidableEq H]

noncomputable def gateA (U : Matrix Bool Bool ℂ) :
    Matrix (SimulatorSpace H) (SimulatorSpace H) ℂ :=
  TensorGate U (TensorGate (1 : Matrix Bool Bool ℂ)
    (TensorGate (1 : Matrix Bool Bool ℂ) (1 : Matrix H H ℂ)))

noncomputable def gateB (U : Matrix Bool Bool ℂ) :
    Matrix (SimulatorSpace H) (SimulatorSpace H) ℂ :=
  TensorGate (1 : Matrix Bool Bool ℂ)
    (TensorGate U (TensorGate (1 : Matrix Bool Bool ℂ) (1 : Matrix H H ℂ)))

noncomputable def gateC (U : Matrix Bool Bool ℂ) :
    Matrix (SimulatorSpace H) (SimulatorSpace H) ℂ :=
  TensorGate (1 : Matrix Bool Bool ℂ)
    (TensorGate (1 : Matrix Bool Bool ℂ) (TensorGate U (1 : Matrix H H ℂ)))

noncomputable def word : List (AdjointStep (SimulatorSpace H)) :=
  [.gate (gateC Hadamard), .gate (gateB Hadamard), .gate (gateA PauliX),
    .gate (gateA tGate), .gate (gateA tGate), .gate (gateA PauliX)]

private theorem gateA_unitary (U : Matrix Bool Bool ℂ)
    (hU : U ∈ Matrix.unitaryGroup Bool ℂ) : gateA (H := H) U ∈ Matrix.unitaryGroup _ ℂ :=
  tensorGate_unitary hU (tensorGate_unitary (Submonoid.one_mem _)
    (tensorGate_unitary (Submonoid.one_mem _) (Submonoid.one_mem _)))

private theorem gateB_unitary (U : Matrix Bool Bool ℂ)
    (hU : U ∈ Matrix.unitaryGroup Bool ℂ) : gateB (H := H) U ∈ Matrix.unitaryGroup _ ℂ :=
  tensorGate_unitary (Submonoid.one_mem _)
    (tensorGate_unitary hU (tensorGate_unitary (Submonoid.one_mem _) (Submonoid.one_mem _)))

private theorem gateC_unitary (U : Matrix Bool Bool ℂ)
    (hU : U ∈ Matrix.unitaryGroup Bool ℂ) : gateC (H := H) U ∈ Matrix.unitaryGroup _ ℂ :=
  tensorGate_unitary (Submonoid.one_mem _)
    (tensorGate_unitary (Submonoid.one_mem _) (tensorGate_unitary hU (Submonoid.one_mem _)))

theorem resources : WellFormedAdjointCircuit (word (H := H)) ∧
    (word (H := H)).length = 6 ∧ adjointQueryCount (word (H := H)) = 0 ∧
    adjointGateCount (word (H := H)) = 6 := by
  refine ⟨?_, rfl, rfl, rfl⟩
  simp only [word, WellFormedAdjointCircuit.gate_cons_iff,
    WellFormedAdjointCircuit.nil, and_true]
  exact ⟨gateC_unitary _ hadamard_unitary, gateB_unitary _ hadamard_unitary,
    gateA_unitary _ pauliX_unitary, gateA_unitary _ tGate_mem_unitary,
    gateA_unitary _ tGate_mem_unitary, gateA_unitary _ pauliX_unitary⟩

private theorem t_square : tGate * tGate =
    Matrix.diagonal (fun b : Bool => if b then Complex.I else 1) := by
  unfold tGate Rz
  rw [Matrix.diagonal_mul_diagonal]
  congr 1
  funext b
  cases b
  · simp
  · change Complex.exp (((Real.pi/4 : ℝ) : ℂ)*Complex.I) *
      Complex.exp (((Real.pi/4 : ℝ) : ℂ)*Complex.I) = Complex.I
    rw [← Complex.exp_add,
      show (((Real.pi/4 : ℝ) : ℂ)*Complex.I) +
        (((Real.pi/4 : ℝ) : ℂ)*Complex.I) = (Real.pi : ℂ)/2*Complex.I by
          push_cast
          ring,
      Complex.exp_pi_div_two_mul_I]

theorem phase_matrix : PauliX * (tGate * (tGate * PauliX)) =
    Matrix.diagonal (fun b : Bool => if b then 1 else Complex.I) := by
  rw [← Matrix.mul_assoc tGate tGate PauliX, t_square]
  ext a b
  cases a <;> cases b <;>
    simp [Matrix.mul_apply, PauliX, permMatrix, Matrix.diagonal_apply]

theorem evaluate_matrix (W : Matrix (SimulatorSpace H) (SimulatorSpace H) ℂ) :
    evaluate W word =
      TensorGate (Matrix.diagonal (fun b : Bool => if b then 1 else Complex.I))
        (TensorGate Hadamard (TensorGate Hadamard (1 : Matrix H H ℂ))) := by
  simp only [word, evaluate, instructionMatrix, gateA, gateB, gateC,
    Matrix.mul_one, tensorGate_mul, Matrix.one_mul, phase_matrix]

theorem evaluate_unitary (W : Matrix (SimulatorSpace H) (SimulatorSpace H) ℂ) :
    evaluate W word ∈ Matrix.unitaryGroup (SimulatorSpace H) ℂ := by
  have hi := resources.1.evaluate_unitary
    (U := (1 : Matrix (SimulatorSpace H) (SimulatorSpace H) ℂ)) (Submonoid.one_mem _)
  rw [evaluate_matrix] at hi ⊢
  exact hi

private theorem two_h_phase (b c : Bool) :
    Complex.I * Hadamard b false * Hadamard c false =
      realPartAmplitude b * realPartAmplitude c := by
  simp only [hadamard_apply_false]
  calc
    _ = Complex.I * (((Real.sqrt 2 : ℂ)⁻¹)^2) := by ring
    _ = Complex.I * (2 : ℂ)⁻¹ := by rw [inv_pow, sqrt2_sq]
    _ = _ := by
      apply Complex.ext <;> norm_num [realPartAmplitude, Complex.mul_re, Complex.mul_im]

section Frames

variable {I : Type} [Fintype I]

omit [Fintype I] in

private theorem averageFrame_entry (F : Matrix H I ℂ) (b : Bool) (h : H) (i : I) :
    averageFrame F (b,h) i = realPartAmplitude b * F h i := by
  simp [averageFrame, Matrix.mul_apply, prepareLift, ite_mul]

theorem simulatorFrame_entry (F : Matrix H I ℂ) (a b c : Bool) (h : H) (i : I) :
    BinaryClockSignalWord.simulatorFrame F (a,(b,(c,h))) i =
      if a = false then realPartAmplitude b * (realPartAmplitude c * F h i) else 0 := by
  simp only [BinaryClockSignalWord.simulatorFrame, scaleEightFrame, hamiltonianFrame,
      averageFrame_entry]

theorem intertwining (W : Matrix (SimulatorSpace H) (SimulatorSpace H) ℂ)
    (F : Matrix H I ℂ) : matmul (evaluate W word) (baseFrame F) = BinaryClockSignalWord.simulatorFrame F := by
  rw [evaluate_matrix]
  ext ⟨a,b,c,h⟩ i
  rw [simulatorFrame_entry]
  cases a
  · simpa [matmul, Matrix.mul_apply, Fintype.sum_prod_type, tensorGate_apply,
      baseFrame, Matrix.diagonal_apply, Matrix.one_apply, mul_ite, ite_mul, mul_assoc] using!
      congrArg (fun z : ℂ => z * F h i) (two_h_phase b c)
  · simp [matmul, Matrix.mul_apply, Fintype.sum_prod_type, tensorGate_apply,
      baseFrame, Matrix.diagonal_apply, Matrix.one_apply, mul_ite, ite_mul]

theorem coherent (W : Matrix (SimulatorSpace H) (SimulatorSpace H) ℂ)
    (F : Matrix H I ℂ) (psi : QState I) :
    evaluate W word *ᵥ (baseFrame F *ᵥ psi) = BinaryClockSignalWord.simulatorFrame F *ᵥ psi := by
  calc
    _ = matmul (evaluate W word) (baseFrame F) *ᵥ psi := Matrix.mulVec_mulVec _ _ _
    _ = _ := by rw [intertwining W F]

theorem inverse_intertwining
    (W : Matrix (SimulatorSpace H) (SimulatorSpace H) ℂ) (F : Matrix H I ℂ) :
    matmul (evaluate W (adjointCircuit word)) (BinaryClockSignalWord.simulatorFrame F) = baseFrame F := by
  have hu : (evaluate W word)ᴴ * evaluate W word = 1 := by
    simpa only [Matrix.star_eq_conjTranspose] using!
      Matrix.mem_unitaryGroup_iff'.mp (evaluate_unitary W)
  rw [evaluate_adjointCircuit, ← intertwining W F]
  calc
    _ = matmul ((evaluate W word)ᴴ * evaluate W word) (baseFrame F) :=
      (Matrix.mul_assoc _ _ _).symm
    _ = _ := by simp only [hu, matmul, Matrix.one_mul]

end Frames

theorem inverse_resources : WellFormedAdjointCircuit (adjointCircuit (word (H := H))) ∧
    (adjointCircuit (word (H := H))).length = 6 ∧
    adjointQueryCount (adjointCircuit (word (H := H))) = 0 ∧
    adjointGateCount (adjointCircuit (word (H := H))) = 6 :=
  ⟨resources.1.adjointCircuit, rfl,
    (adjointQueryCount_adjointCircuit _).trans resources.2.2.1,
    (adjointGateCount_adjointCircuit _).trans resources.2.2.2⟩

end Qatlib.Concepts.AmplitudeCore.PreparedReadout.PhysicalHistory.BinaryClockSignalInitialization
