/-
Copyright (c) 2026 Quantum Atlas Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quantum Atlas Contributors
-/

module

public import Qatlib.Concepts.QsvtCore.LinearSystems.ReciprocalApproximation

@[expose] public section
set_option backward.isDefEq.respectTransparency false
open Qatlib.Concepts.BlockEncoding Qatlib.Concepts.BlockEncoding.Encoding Qatlib.Foundations.InstrumentCore.Measurement Qatlib.Foundations.InstrumentCore.ProjectiveMeasurement Qatlib.Concepts.OperatorErrors.Robustness Qatlib.Concepts.OperatorErrors.Robustness.SignalProcessing Qatlib.Concepts.PhaseGeometry.Phase Qatlib.Foundations.PureStateMath Qatlib.Foundations.PureStateMath.Reflection

set_option autoImplicit false
noncomputable section
namespace Qatlib.Concepts.NonNormalSpec.ResolventWord.NeumannProgram
open Matrix Polynomial
open scoped BigOperators Matrix.Norms.L2Operator

variable {I : Type} [Fintype I] [DecidableEq I]

def leftDefectNeumann (S : Matrix I I ℂ) (b : ℕ) : Matrix I I ℂ :=
  Sᴴ * ∑ k ∈ Finset.range b, (1 - S * Sᴴ) ^ k

/-- Powers of the right defect intertwine with the adjoint of `S` to give powers of the left
defect. -/
private theorem defect_intertwine (S : Matrix I I ℂ) (k : ℕ) :
    (1 - Sᴴ * S) ^ k * Sᴴ = Sᴴ * (1 - S * Sᴴ) ^ k := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [pow_succ', Matrix.mul_assoc, ih, ← Matrix.mul_assoc]
    have h : (1 - Sᴴ * S) * Sᴴ = Sᴴ * (1 - S * Sᴴ) := by noncomm_ring
    rw [h, Matrix.mul_assoc, ← pow_succ']

/-- The left-defect Neumann polynomial equals `reciprocalMatrixApprox`. -/
theorem leftDefectNeumann_eq_reciprocalMatrixApprox (S : Matrix I I ℂ) (b : ℕ) :
    Qatlib.Concepts.NonNormalSpec.ResolventWord.NeumannProgram.leftDefectNeumann S b = Qatlib.Concepts.QsvtCore.LinearSystems.reciprocalMatrixApprox S b := by
  have he : aeval (Sᴴ * S) ((Qatlib.Concepts.QsvtCore.LinearSystems.reciprocalFactor b).map Complex.ofRealHom) =
      ∑ k ∈ Finset.range b, (1 - Sᴴ * S) ^ k := by
    simp [Qatlib.Concepts.QsvtCore.LinearSystems.reciprocalFactor, Polynomial.map_sum, Polynomial.map_pow,
      Polynomial.map_sub, Polynomial.map_one, Polynomial.map_X]
  rw [Qatlib.Concepts.QsvtCore.LinearSystems.reciprocalMatrixApprox, he, Matrix.conjTranspose_mul,
    Matrix.conjTranspose_sum]
  simp only [Matrix.conjTranspose_pow, Matrix.conjTranspose_sub,
    Matrix.conjTranspose_one, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose]
  rw [Finset.sum_mul]
  simp only [defect_intertwine]
  unfold Qatlib.Concepts.NonNormalSpec.ResolventWord.NeumannProgram.leftDefectNeumann
  rw [Finset.mul_sum]

end Qatlib.Concepts.NonNormalSpec.ResolventWord.NeumannProgram
