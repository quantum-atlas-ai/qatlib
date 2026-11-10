/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.LchsSimulation.StaticLchs.PreparedAmplitudeAmplification
set_option warningAsError false

set_option autoImplicit false
noncomputable section
namespace Qatlib.Papers.QCounting98.MainResults.Boundary
open Matrix
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.SpectralReadout.PhaseReadout Qatlib.Foundations.InstrumentCore.Measurement
open Qatlib.Concepts.LchsSimulation.StaticLchs Qatlib.Foundations.PureStateMath.Reflection
open Qatlib.Foundations.QueryWordCore.Circuit
open scoped Classical BigOperators

def firstZeroSet : Finset (Bool × Bool) := Finset.univ.filter (fun p => p.1 = false)

def ancillaInput : QState (Bool × Bool) := TensorState (Ket false) Plus

def literalRankOne (phase : ℂ) (psi : QState (Bool × Bool)) : QState (Bool × Bool) :=
  psi - ((1-phase)*Inner (Ket (false,false)) psi) • Ket (false,false)

theorem ancillaInput_normalized : Normalized ancillaInput :=
  normalized_tensorState (normalized_ket false) normalized_plus

theorem firstZero_unitary : preparedMark firstZeroSet ∈ Matrix.unitaryGroup (Bool × Bool) ℂ :=
  (prepared_aa_reflection_and_access 1 (false,false) firstZeroSet
    (Matrix.unitaryGroup (Bool × Bool) ℂ).one_mem).1

theorem firstZero_actual_run :
    Run (1 : Matrix (Bool × Bool) (Bool × Bool) ℂ)
      [Step.gate (preparedMark firstZeroSet)] ancillaInput = -ancillaInput := by
  change ApplyGate (preparedMark firstZeroSet) ancillaInput = -ancillaInput
  unfold ApplyGate preparedMark Projector
  rw [Matrix.sub_mulVec,Matrix.one_mulVec,Matrix.smul_mulVec]
  ext ⟨i,j⟩
  cases i <;> cases j <;> simp [Matrix.mulVec,dotProduct,Fintype.sum_prod_type,
    Matrix.diagonal,firstZeroSet,ancillaInput,TensorState,Ket]
  <;> ring

theorem literalRankOne_on_ancilla :
    literalRankOne (-1) ancillaInput = -TensorState (Ket false) Minus := by
  ext ⟨i,j⟩
  cases i <;> cases j <;>
    simp [literalRankOne,ancillaInput,Qatlib.Foundations.PureStateMath.Inner,dotProduct,Fintype.sum_prod_type,
      TensorState,Ket,Plus,Minus,Hadamard]
  ring

theorem hadamard_plus_actual : ApplyGate Hadamard Plus = Ket false := by
  rw [← applyGate_hadamard_ket_false]
  change Hadamard *ᵥ (Hadamard *ᵥ Ket false) = _
  rw [Matrix.mulVec_mulVec,hadamard_mul_self,Matrix.one_mulVec]

theorem hadamard_minus_actual : ApplyGate Hadamard Minus = Ket true := by
  rw [← applyGate_hadamard_ket_true]
  change Hadamard *ᵥ (Hadamard *ᵥ Ket true) = _
  rw [Matrix.mulVec_mulVec,hadamard_mul_self,Matrix.one_mulVec]

theorem ancillaReadout_unitary :
    TensorGate (1 : Matrix Bool Bool ℂ) Hadamard ∈ Matrix.unitaryGroup (Bool × Bool) ℂ :=
  tensorGate_unitary (Matrix.unitaryGroup Bool ℂ).one_mem hadamard_unitary

theorem firstZero_physical_readout :
    BornProb (ApplyGate (TensorGate (1 : Matrix Bool Bool ℂ) Hadamard)
      (Run (1 : Matrix (Bool × Bool) (Bool × Bool) ℂ)
        [Step.gate (preparedMark firstZeroSet)] ancillaInput)) (false,false) = 1 ∧
    BornProb (ApplyGate (TensorGate (1 : Matrix Bool Bool ℂ) Hadamard)
      (literalRankOne (-1) ancillaInput)) (false,false) = 0 := by
  rw [firstZero_actual_run,literalRankOne_on_ancilla]
  have hneg (psi : QState (Bool × Bool)) :
      ApplyGate (TensorGate (1 : Matrix Bool Bool ℂ) Hadamard) (-psi) =
        -ApplyGate (TensorGate (1 : Matrix Bool Bool ℂ) Hadamard) psi :=
    Matrix.mulVec_neg _ _
  rw [hneg,hneg]
  simp only [ancillaInput,applyGate_tensorGate,hadamard_plus_actual,hadamard_minus_actual]
  simp [ApplyGate,Matrix.one_mulVec,BornProb,TensorState,Ket]

theorem firstZero_literal_counterexample :
    preparedMark firstZeroSet ∈ Matrix.unitaryGroup (Bool × Bool) ℂ ∧
    Normalized ancillaInput ∧
    Run (1 : Matrix (Bool × Bool) (Bool × Bool) ℂ)
      [Step.gate (preparedMark firstZeroSet)] ancillaInput ≠ literalRankOne (-1) ancillaInput := by
  refine ⟨firstZero_unitary,ancillaInput_normalized,?_⟩
  intro h
  have hp := firstZero_physical_readout
  rw [h,hp.2] at hp
  norm_num at hp

end Qatlib.Papers.QCounting98.MainResults.Boundary
