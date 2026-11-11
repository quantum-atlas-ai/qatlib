/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Foundations.QueryWordCore.Circuit

/-!
# Boolean phase and bit oracles

This module defines Boolean phase oracles and bit-flip oracles, proves their unitarity, and
identifies their actions on states and basis vectors. Phase kickback with a `Minus` ancilla
relates lifted bit-oracle circuits to phase-oracle execution and preserves the corresponding
measurement probabilities.

The mathematical background is described in [NielsenChuang2010].

## Main statements

* `phaseOracle_unitary` and `bitOracleOn_unitary`: oracle unitarity.
* `run_liftCircuit_bitOracleOn`: phase kickback for a whole circuit.
* `measureProb_run_liftCircuit_bitOracleOn`: preservation of output probabilities.

## References

* [Nielsen and Chuang, 2010][NielsenChuang2010]
-/

open Qatlib.Foundations.QueryWordCore.Circuit
open Qatlib.Foundations.PureStateMath
open Qatlib
open Qatlib

namespace Qatlib.Concepts.QueryWordCore.QueryMachinery

open Matrix

set_option linter.unusedSectionVars false

variable {I : Type*} [Fintype I] [DecidableEq I]

/-- The diagonal Boolean oracle multiplying a basis vector by minus one exactly at inputs where
`f` is true. -/
noncomputable def PhaseOracle (f : I → Bool) : Matrix I I ℂ :=
  Matrix.diagonal fun x => if f x then (-1 : ℂ) else 1

/-- Squaring a Boolean phase oracle gives the identity matrix. -/
theorem phaseOracle_mul_self (f : I → Bool) : PhaseOracle f * PhaseOracle f = 1 := by
  unfold PhaseOracle
  rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
  congr 1
  funext a
  split_ifs <;> ring

/-- A Boolean phase oracle equals its conjugate transpose. -/
theorem phaseOracle_conjTranspose (f : I → Bool) : (PhaseOracle f)ᴴ = PhaseOracle f := by
  unfold PhaseOracle
  rw [Matrix.diagonal_conjTranspose]
  congr 1
  funext a
  simp only [Pi.star_apply]
  split_ifs <;> simp

/-- Every Boolean phase oracle is unitary. -/
theorem phaseOracle_unitary (f : I → Bool) : PhaseOracle f ∈ Matrix.unitaryGroup I ℂ := by
  rw [Matrix.mem_unitaryGroup_iff', Matrix.star_eq_conjTranspose, phaseOracle_conjTranspose f]
  exact phaseOracle_mul_self f

/-- A phase oracle multiplies each state amplitude by the sign determined by the corresponding
Boolean oracle value. -/
theorem applyGate_phaseOracle (f : I → Bool) (ψ : QState I) (x : I) :
    ApplyGate (PhaseOracle f) ψ x = (if f x then (-1 : ℂ) else 1) * ψ x := by
  unfold ApplyGate PhaseOracle
  rw [Matrix.mulVec_diagonal]

/-- The phase oracle marking a single distinguished basis label. -/
noncomputable def MarkOracle (w₀ : I) : Matrix I I ℂ := PhaseOracle fun x => decide (x = w₀)

/-- The single-label marking oracle is unitary. -/
theorem markOracle_unitary (w₀ : I) : MarkOracle w₀ ∈ Matrix.unitaryGroup I ℂ :=
  phaseOracle_unitary _

/-- The phase oracle marking the basis labels in a finite set. -/
noncomputable def SetOracle (A : Finset I) : Matrix I I ℂ := PhaseOracle fun x => decide (x ∈ A)

/-- The finite-set marking oracle is unitary. -/
theorem setOracle_unitary (A : Finset I) : SetOracle A ∈ Matrix.unitaryGroup I ℂ :=
  phaseOracle_unitary _

/-- Marking one label agrees with the set oracle for its singleton set. -/
theorem markOracle_eq_setOracle (w₀ : I) : MarkOracle w₀ = SetOracle {w₀} := by
  simp [MarkOracle, SetOracle]

/-- The basis permutation that XORs the oracle value into an answer bit while preserving the
input label. -/
def BitFlip (f : I → Bool) (p : I × Bool) : I × Bool := (p.1, p.2 ^^ f p.1)

/-- Applying the Boolean answer-bit flip twice restores the original basis label. -/
theorem bitFlip_involutive (f : I → Bool) : Function.Involutive (BitFlip f) := by
  rintro ⟨i, b⟩
  cases hf : f i <;> cases b <;> simp [BitFlip, hf]

/-- The permutation matrix implementing the Boolean oracle's answer-bit flip on `I × Bool`. -/
noncomputable def BitOracleOn (f : I → Bool) : Matrix (I × Bool) (I × Bool) ℂ :=
  permMatrix (BitFlip f)

/-- Squaring the bit-oracle matrix gives the identity. -/
theorem bitOracleOn_mul_self (f : I → Bool) : BitOracleOn f * BitOracleOn f = 1 :=
  permMatrix_mul_self (bitFlip_involutive f)

/-- The Boolean bit oracle on `I × Bool` is unitary. -/
theorem bitOracleOn_unitary (f : I → Bool) : BitOracleOn f ∈ Matrix.unitaryGroup (I × Bool) ℂ :=
  permMatrix_unitary (bitFlip_involutive f)

/-- Applying the bit oracle to a state composes its amplitudes with `BitFlip`. -/
theorem applyGate_bitOracleOn (f : I → Bool) (ψ : QState (I × Bool)) (p : I × Bool) :
    ApplyGate (BitOracleOn f) ψ p = ψ (BitFlip f p) :=
  applyGate_permMatrix (bitFlip_involutive f) ψ p

/-- A bit oracle maps `Ket (x, b)` to `Ket (x, b ^^ f x)`. -/
theorem applyGate_bitOracleOn_ket (f : I → Bool) (x : I) (b : Bool) :
    ApplyGate (BitOracleOn f) (Ket (x, b)) = Ket (x, b ^^ f x) :=
  applyGate_permMatrix_ket (bitFlip_involutive f) (x, b)

/-- Executing one bit-oracle query on a basis state XORs the oracle answer into its answer bit. -/
theorem run_query_bitOracleOn_ket (f : I → Bool) (x : I) (b : Bool) :
    Run (BitOracleOn f) [Step.query] (Ket (x, b)) = Ket (x, b ^^ f x) := by
  simp only [run_query, run_nil]
  exact applyGate_bitOracleOn_ket f x b

variable {n : ℕ}

/-- The Boolean oracle's answer-bit permutation transported to an `(n + 1)`-qubit register. -/
def BitFlipReg (f : Reg n → Bool) (x : Reg (n + 1)) : Reg (n + 1) :=
  (regSuccEquiv n).symm (BitFlip f (regSuccEquiv n x))

/-- The register-level answer-bit permutation is involutive. -/
theorem bitFlipReg_involutive (f : Reg n → Bool) : Function.Involutive (BitFlipReg f) := by
  intro x
  simp only [BitFlipReg, Equiv.apply_symm_apply]
  rw [bitFlip_involutive f (regSuccEquiv n x), Equiv.symm_apply_apply]

/-- The Boolean bit-oracle permutation matrix on an `(n + 1)`-qubit register. -/
noncomputable def BitOracle (f : Reg n → Bool) : Matrix (Reg (n + 1)) (Reg (n + 1)) ℂ :=
  permMatrix (BitFlipReg f)

/-- The register-level Boolean bit oracle is unitary. -/
theorem bitOracle_unitary (f : Reg n → Bool) :
    BitOracle f ∈ Matrix.unitaryGroup (Reg (n + 1)) ℂ :=
  permMatrix_unitary (bitFlipReg_involutive f)

/-- Entries of the register-level bit oracle agree with `BitOracleOn` after the register-product
equivalence. -/
theorem bitOracle_apply_eq_bitOracleOn (f : Reg n → Bool) (x y : Reg (n + 1)) :
    BitOracle f x y = BitOracleOn f (regSuccEquiv n x) (regSuccEquiv n y) := by
  have heq : x = (regSuccEquiv n).symm (BitFlip f (regSuccEquiv n y)) ↔
      regSuccEquiv n x = BitFlip f (regSuccEquiv n y) :=
    (Equiv.apply_eq_iff_eq_symm_apply _).symm
  simp only [BitOracle, BitOracleOn, permMatrix, Matrix.of_apply, BitFlipReg]
  simp only [heq]

/-- A bit query with a `Minus` answer ancilla applies the phase oracle to the data state and
preserves the ancilla. -/
theorem applyGate_bitOracleOn_tensorState_minus (f : I → Bool) (ψ : QState I) :
    ApplyGate (BitOracleOn f) (TensorState ψ Minus) =
      TensorState (ApplyGate (PhaseOracle f) ψ) Minus := by
  funext p
  rw [applyGate_bitOracleOn]
  obtain ⟨i, b⟩ := p
  simp only [TensorState, BitFlip, Minus]
  rw [applyGate_phaseOracle]
  cases f i <;> cases b <;> simp [Hadamard]

/-- Running a lifted circuit with a bit oracle and `Minus` ancilla reproduces the original
phase-oracle circuit tensored with that ancilla. -/
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

/-- The lifted bit-oracle circuit with `Minus` ancilla has the same data-register measurement
probabilities as the phase-oracle circuit. -/
theorem measureProb_run_liftCircuit_bitOracleOn (f : I → Bool) (C : Circuit I) (ψ : QState I)
    (S : Finset I) :
    MeasureProb (Run (BitOracleOn f) (LiftCircuit C) (TensorState ψ Minus)) (S ×ˢ Finset.univ) =
      MeasureProb (Run (PhaseOracle f) C ψ) S := by
  rw [run_liftCircuit_bitOracleOn, measureProb_tensorState_left normalized_minus]

end Qatlib.Concepts.QueryWordCore.QueryMachinery
