/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.LchsSimulation.StaticLchs.PreparedAmplitudeAmplification

/-!
# A boundary for first-register zero reflections

`ancillaInput` is a normalized two-qubit state supported on a zero first register.
`firstZero_physical_readout` distinguishes reflection on that entire subspace from the rank-one
transformation `literalRankOne` by a subsequent Hadamard measurement. The mathematical context
is [BrassardHoyerTapp1998Counting].

## Main statements

* `firstZero_physical_readout`: After a Hadamard on the second qubit, the first-register
  reflection yields outcome `(false, false)` with probability one, whereas the rank-one
  transformation yields probability zero.
* `firstZero_literal_counterexample`: The first-register reflection is unitary and acts on a
  normalized input differently from the rank-one transformation.

## References

* [Brassard et al., 1998][BrassardHoyerTapp1998Counting]
-/

set_option autoImplicit false
noncomputable section
namespace Qatlib.Papers.QCounting98.MainResults.Boundary
open Matrix
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.SpectralReadout.PhaseReadout Qatlib.Foundations.InstrumentCore.Measurement
open Qatlib.Concepts.LchsSimulation.StaticLchs Qatlib.Foundations.PureStateMath.Reflection
open Qatlib.Foundations.QueryWordCore.Circuit
open scoped Classical BigOperators

/-- The set of two-qubit basis indices whose first Boolean coordinate is false. -/
def firstZeroSet : Finset (Bool × Bool) := Finset.univ.filter (fun p => p.1 = false)

/-- The tensor product of the false computational basis state and the plus state. -/
def ancillaInput : QState (Bool × Bool) := TensorState (Ket false) Plus

/-- The rank-one phase transformation supported on the basis state `(false, false)`. -/
def literalRankOne (phase : ℂ) (psi : QState (Bool × Bool)) : QState (Bool × Bool) :=
  psi - ((1-phase)*Inner (Ket (false,false)) psi) • Ket (false,false)

/-- The state `ancillaInput` is normalized. -/
theorem ancillaInput_normalized : Normalized ancillaInput :=
  normalized_tensorState (normalized_ket false) normalized_plus

/-- The sign reflection on `firstZeroSet` is unitary. -/
theorem firstZero_unitary : preparedMark firstZeroSet ∈ Matrix.unitaryGroup (Bool × Bool) ℂ :=
  (prepared_aa_reflection_and_access 1 (false,false) firstZeroSet
    (Matrix.unitaryGroup (Bool × Bool) ℂ).one_mem).1

/-- Applying the reflection on `firstZeroSet` to `ancillaInput` negates the state. -/
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

/-- The rank-one sign transformation sends `ancillaInput` to minus the tensor product of the
false state and the minus state. -/
theorem literalRankOne_on_ancilla :
    literalRankOne (-1) ancillaInput = -TensorState (Ket false) Minus := by
  ext ⟨i,j⟩
  cases i <;> cases j <;>
    simp [literalRankOne,ancillaInput,Qatlib.Foundations.PureStateMath.Inner,dotProduct,Fintype.sum_prod_type,
      TensorState,Ket,Plus,Minus,Hadamard]
  ring

/-- Applying the Hadamard gate to the plus state yields the false basis state. -/
theorem hadamard_plus_actual : ApplyGate Hadamard Plus = Ket false := by
  rw [← applyGate_hadamard_ket_false]
  change Hadamard *ᵥ (Hadamard *ᵥ Ket false) = _
  rw [Matrix.mulVec_mulVec,hadamard_mul_self,Matrix.one_mulVec]

/-- Applying the Hadamard gate to the minus state yields the true basis state. -/
theorem hadamard_minus_actual : ApplyGate Hadamard Minus = Ket true := by
  rw [← applyGate_hadamard_ket_true]
  change Hadamard *ᵥ (Hadamard *ᵥ Ket true) = _
  rw [Matrix.mulVec_mulVec,hadamard_mul_self,Matrix.one_mulVec]

/-- The identity on the first qubit tensored with the Hadamard on the second qubit is unitary. -/
theorem ancillaReadout_unitary :
    TensorGate (1 : Matrix Bool Bool ℂ) Hadamard ∈ Matrix.unitaryGroup (Bool × Bool) ℂ :=
  tensorGate_unitary (Matrix.unitaryGroup Bool ℂ).one_mem hadamard_unitary

/-- After a Hadamard on the second qubit, the first-register reflection yields outcome `(false,
false)` with probability one, whereas the rank-one transformation yields probability zero. -/
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

/-- The first-register reflection is unitary and acts on a normalized input differently from the
rank-one transformation. See [BrassardHoyerTapp1998Counting]. -/
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
