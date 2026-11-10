/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Foundations.QueryWordCore.Circuit
open Qatlib.Foundations.QueryWordCore.Circuit
open Qatlib.Foundations.PureStateMath
open Qatlib
open Qatlib

namespace Qatlib.Concepts.QueryWordCore.QueryMachinery

open Matrix

set_option linter.unusedSectionVars false

variable {I : Type*} [Fintype I] [DecidableEq I]

noncomputable def PhaseOracle (f : I → Bool) : Matrix I I ℂ :=
  Matrix.diagonal fun x => if f x then (-1 : ℂ) else 1

theorem phaseOracle_mul_self (f : I → Bool) : PhaseOracle f * PhaseOracle f = 1 := by
  unfold PhaseOracle
  rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
  congr 1
  funext a
  split_ifs <;> ring

theorem phaseOracle_conjTranspose (f : I → Bool) : (PhaseOracle f)ᴴ = PhaseOracle f := by
  unfold PhaseOracle
  rw [Matrix.diagonal_conjTranspose]
  congr 1
  funext a
  simp only [Pi.star_apply]
  split_ifs <;> simp

theorem phaseOracle_unitary (f : I → Bool) : PhaseOracle f ∈ Matrix.unitaryGroup I ℂ := by
  rw [Matrix.mem_unitaryGroup_iff', Matrix.star_eq_conjTranspose, phaseOracle_conjTranspose f]
  exact phaseOracle_mul_self f

theorem applyGate_phaseOracle (f : I → Bool) (ψ : QState I) (x : I) :
    ApplyGate (PhaseOracle f) ψ x = (if f x then (-1 : ℂ) else 1) * ψ x := by
  unfold ApplyGate PhaseOracle
  rw [Matrix.mulVec_diagonal]

noncomputable def MarkOracle (w₀ : I) : Matrix I I ℂ := PhaseOracle fun x => decide (x = w₀)

theorem markOracle_unitary (w₀ : I) : MarkOracle w₀ ∈ Matrix.unitaryGroup I ℂ :=
  phaseOracle_unitary _

noncomputable def SetOracle (A : Finset I) : Matrix I I ℂ := PhaseOracle fun x => decide (x ∈ A)

theorem setOracle_unitary (A : Finset I) : SetOracle A ∈ Matrix.unitaryGroup I ℂ :=
  phaseOracle_unitary _

theorem markOracle_eq_setOracle (w₀ : I) : MarkOracle w₀ = SetOracle {w₀} := by
  simp [MarkOracle, SetOracle]

def BitFlip (f : I → Bool) (p : I × Bool) : I × Bool := (p.1, p.2 ^^ f p.1)

theorem bitFlip_involutive (f : I → Bool) : Function.Involutive (BitFlip f) := by
  rintro ⟨i, b⟩
  cases hf : f i <;> cases b <;> simp [BitFlip, hf]

noncomputable def BitOracleOn (f : I → Bool) : Matrix (I × Bool) (I × Bool) ℂ :=
  permMatrix (BitFlip f)

theorem bitOracleOn_mul_self (f : I → Bool) : BitOracleOn f * BitOracleOn f = 1 :=
  permMatrix_mul_self (bitFlip_involutive f)

theorem bitOracleOn_unitary (f : I → Bool) : BitOracleOn f ∈ Matrix.unitaryGroup (I × Bool) ℂ :=
  permMatrix_unitary (bitFlip_involutive f)

theorem applyGate_bitOracleOn (f : I → Bool) (ψ : QState (I × Bool)) (p : I × Bool) :
    ApplyGate (BitOracleOn f) ψ p = ψ (BitFlip f p) :=
  applyGate_permMatrix (bitFlip_involutive f) ψ p

theorem applyGate_bitOracleOn_ket (f : I → Bool) (x : I) (b : Bool) :
    ApplyGate (BitOracleOn f) (Ket (x, b)) = Ket (x, b ^^ f x) :=
  applyGate_permMatrix_ket (bitFlip_involutive f) (x, b)

theorem run_query_bitOracleOn_ket (f : I → Bool) (x : I) (b : Bool) :
    Run (BitOracleOn f) [Step.query] (Ket (x, b)) = Ket (x, b ^^ f x) := by
  simp only [run_query, run_nil]
  exact applyGate_bitOracleOn_ket f x b

variable {n : ℕ}

def BitFlipReg (f : Reg n → Bool) (x : Reg (n + 1)) : Reg (n + 1) :=
  (regSuccEquiv n).symm (BitFlip f (regSuccEquiv n x))

theorem bitFlipReg_involutive (f : Reg n → Bool) : Function.Involutive (BitFlipReg f) := by
  intro x
  simp only [BitFlipReg, Equiv.apply_symm_apply]
  rw [bitFlip_involutive f (regSuccEquiv n x), Equiv.symm_apply_apply]

noncomputable def BitOracle (f : Reg n → Bool) : Matrix (Reg (n + 1)) (Reg (n + 1)) ℂ :=
  permMatrix (BitFlipReg f)

theorem bitOracle_unitary (f : Reg n → Bool) :
    BitOracle f ∈ Matrix.unitaryGroup (Reg (n + 1)) ℂ :=
  permMatrix_unitary (bitFlipReg_involutive f)

theorem bitOracle_apply_eq_bitOracleOn (f : Reg n → Bool) (x y : Reg (n + 1)) :
    BitOracle f x y = BitOracleOn f (regSuccEquiv n x) (regSuccEquiv n y) := by
  have heq : x = (regSuccEquiv n).symm (BitFlip f (regSuccEquiv n y)) ↔
      regSuccEquiv n x = BitFlip f (regSuccEquiv n y) :=
    (Equiv.apply_eq_iff_eq_symm_apply _).symm
  simp only [BitOracle, BitOracleOn, permMatrix, Matrix.of_apply, BitFlipReg]
  simp only [heq]

theorem applyGate_bitOracleOn_tensorState_minus (f : I → Bool) (ψ : QState I) :
    ApplyGate (BitOracleOn f) (TensorState ψ Minus) =
      TensorState (ApplyGate (PhaseOracle f) ψ) Minus := by
  funext p
  rw [applyGate_bitOracleOn]
  obtain ⟨i, b⟩ := p
  simp only [TensorState, BitFlip, Minus]
  rw [applyGate_phaseOracle]
  cases f i <;> cases b <;> simp [Hadamard]

theorem run_liftCircuit_bitOracleOn (f : I → Bool) (C : Circuit I) (ψ : QState I) :
    Run (BitOracleOn f) (LiftCircuit C) (TensorState ψ Minus) =
      TensorState (Run (PhaseOracle f) C ψ) Minus := by
  induction C generalizing ψ with
  | nil => rfl
  | cons s C ih =>
    cases s with
    | gate U =>
      simp only [liftCircuit_gate, run_gate]
      rw [applyGate_liftGate]
      exact ih _
    | query =>
      simp only [liftCircuit_query, run_query]
      rw [applyGate_bitOracleOn_tensorState_minus]
      exact ih _

theorem measureProb_run_liftCircuit_bitOracleOn (f : I → Bool) (C : Circuit I) (ψ : QState I)
    (S : Finset I) :
    MeasureProb (Run (BitOracleOn f) (LiftCircuit C) (TensorState ψ Minus)) (S ×ˢ Finset.univ) =
      MeasureProb (Run (PhaseOracle f) C ψ) S := by
  rw [run_liftCircuit_bitOracleOn, measureProb_tensorState_left normalized_minus]

end Qatlib.Concepts.QueryWordCore.QueryMachinery
