/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.CoherentSim.CoherentOAA.Pseudoinverse
import Qatlib.Concepts.LocalMachine.LocalTransport.LeastSquaresOutputSpec
set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false
open Qatlib.Concepts.CoherentSim.CoherentOAA
open Qatlib.Foundations.InstrumentCore.ProjectiveMeasurementLaws
open Qatlib.Concepts.LocalMachine.LocalTransport
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.BlockEncoding.Postselection
namespace Qatlib.Concepts.QlsReadoutSpec.RectDilation
open Matrix
open scoped Matrix.Norms.L2Operator

noncomputable def hermitianDilation {O I : Type} [Fintype O] [Fintype I]
    (A : Matrix O I ℂ) : Matrix (O ⊕ I) (O ⊕ I) ℂ :=
  Matrix.of fun p q =>
    match p, q with
    | Sum.inl o, Sum.inl o' => 0
    | Sum.inl o, Sum.inr i => A o i
    | Sum.inr i, Sum.inl o => star (A o i)
    | Sum.inr i, Sum.inr i' => 0

noncomputable def dilationInput {O I : Type} [Fintype O] [Fintype I]
    (b : QState O) : QState (O ⊕ I) :=
  fun p =>
    match p with
    | Sum.inl o => b o
    | Sum.inr _ => 0

structure DilationReduction (O I : Type) where

  A : Matrix O I ℂ

  b : QState O

noncomputable def DilationReduction.ReducesAt {O I : Type} [Fintype O] [DecidableEq O]
    [Fintype I] [DecidableEq I] (R : DilationReduction O I) : Prop :=
  (hermitianDilation R.A).IsHermitian ∧
    leastSquaresVector R.A R.b = fun i =>
      (matrixPseudoinverse (hermitianDilation R.A) *ᵥ dilationInput R.b) (Sum.inr i)

theorem hermitianDilation_eq_fromBlocks {O I : Type} [Fintype O] [Fintype I]
    (A : Matrix O I ℂ) :
    hermitianDilation A =
      Matrix.fromBlocks (0 : Matrix O O ℂ) A Aᴴ 0 := by
  ext p q
  rcases p with o | i <;> rcases q with o' | i'
  · simp [hermitianDilation, Matrix.fromBlocks]
  · simp [hermitianDilation, Matrix.fromBlocks]
  · simp [hermitianDilation, Matrix.fromBlocks]
  · simp [hermitianDilation, Matrix.fromBlocks]

theorem hermitianDilation_isHermitian {O I : Type} [Fintype O] [Fintype I]
    (A : Matrix O I ℂ) : (hermitianDilation A).IsHermitian := by
  show (hermitianDilation A)ᴴ = hermitianDilation A
  rw [hermitianDilation_eq_fromBlocks, Matrix.fromBlocks_conjTranspose]
  simp

theorem hermitianDilation_pseudoinverse {O I : Type} [Fintype O] [DecidableEq O]
    [Fintype I] [DecidableEq I] (A : Matrix O I ℂ) :
    matrixPseudoinverse (hermitianDilation A) =
      Matrix.fromBlocks 0 (matrixPseudoinverse A)ᴴ (matrixPseudoinverse A) 0 := by
  set P := matrixPseudoinverse A
  set B : Matrix (O ⊕ I) (O ⊕ I) ℂ := Matrix.fromBlocks 0 Pᴴ P 0
  have hMP1 : A * P * A = A := mul_matrixPseudoinverse_mul A
  have hMP2 : P * A * P = P := matrixPseudoinverse_mul_self A
  have hMP3 : (A * P)ᴴ = A * P := mul_matrixPseudoinverse_adjoint A
  have hMP4 : (P * A)ᴴ = P * A := matrixPseudoinverse_mul_adjoint A
  have hDB : hermitianDilation A * B =
      Matrix.fromBlocks (A * P : Matrix O O ℂ) 0 0 (P * A) := by
    rw [hermitianDilation_eq_fromBlocks, Matrix.fromBlocks_multiply]
    refine Matrix.fromBlocks_inj.mpr ⟨?_, ?_, ?_, ?_⟩
    · simp
    · simp
    · simp
    · rw [← Matrix.conjTranspose_mul, hMP4, zero_mul, add_zero]
  have hBD : B * hermitianDilation A =
      Matrix.fromBlocks (A * P : Matrix O O ℂ) 0 0 (P * A) := by
    rw [hermitianDilation_eq_fromBlocks, Matrix.fromBlocks_multiply]
    refine Matrix.fromBlocks_inj.mpr ⟨?_, ?_, ?_, ?_⟩
    · rw [← Matrix.conjTranspose_mul, hMP3, zero_mul, zero_add]
    · simp
    · simp
    · simp
  have hPAA : P * A * Aᴴ = Aᴴ := by
    have h2 : Aᴴ * Pᴴ = P * A := by rw [← Matrix.conjTranspose_mul, hMP4]
    calc P * A * Aᴴ = (Aᴴ * Pᴴ) * Aᴴ := by rw [← h2]
      _ = Aᴴ * (Pᴴ * Aᴴ) := Matrix.mul_assoc Aᴴ Pᴴ Aᴴ
      _ = (A * P * A)ᴴ := by rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul]
      _ = Aᴴ := by rw [hMP1]
  have hAPP : A * P * Pᴴ = Pᴴ := by
    have h2 : Pᴴ * Aᴴ = A * P := by rw [← Matrix.conjTranspose_mul, hMP3]
    calc A * P * Pᴴ = (Pᴴ * Aᴴ) * Pᴴ := by rw [← h2]
      _ = Pᴴ * (Aᴴ * Pᴴ) := Matrix.mul_assoc Pᴴ Aᴴ Pᴴ
      _ = (P * A * P)ᴴ := by rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul]
      _ = Pᴴ := by rw [hMP2]
  have hDBD : hermitianDilation A * B * hermitianDilation A = hermitianDilation A := by
    rw [hDB, hermitianDilation_eq_fromBlocks, Matrix.fromBlocks_multiply]
    refine Matrix.fromBlocks_inj.mpr ⟨?_, ?_, ?_, ?_⟩
    · simp
    · simpa using hMP1
    · simpa using hPAA
    · simp
  have hBDB : B * hermitianDilation A * B = B := by
    rw [hBD, Matrix.fromBlocks_multiply]
    refine Matrix.fromBlocks_inj.mpr ⟨?_, ?_, ?_, ?_⟩
    · simp
    · simpa using hAPP
    · simpa using hMP2
    · simp
  have hDBadj : (hermitianDilation A * B)ᴴ = hermitianDilation A * B := by
    rw [hDB, Matrix.fromBlocks_conjTranspose]
    refine Matrix.fromBlocks_inj.mpr ⟨?_, ?_, ?_, ?_⟩
    · rw [hMP3]
    · simp
    · simp
    · rw [hMP4]
  have hBDadj : (B * hermitianDilation A)ᴴ = B * hermitianDilation A := by
    rw [hBD, Matrix.fromBlocks_conjTranspose]
    refine Matrix.fromBlocks_inj.mpr ⟨?_, ?_, ?_, ?_⟩
    · rw [hMP3]
    · simp
    · simp
    · rw [hMP4]
  have hBuniq : B = matrixPseudoinverse (hermitianDilation A) :=
    matrixPseudoinverse_unique (hermitianDilation A) B hDBD hBDB hDBadj hBDadj
  exact hBuniq.symm

theorem rectangular_dilation_reduction :
    ∀ (O I : Type) [Fintype O] [DecidableEq O] [Fintype I] [DecidableEq I]
      (A : Matrix O I ℂ) (b : QState O),
      ∃ R : DilationReduction O I, R.A = A ∧ R.b = b ∧ R.ReducesAt := by
  intro O I _ _ _ _ A b
  refine ⟨⟨A,b⟩,rfl,rfl,?_⟩
  change (hermitianDilation A).IsHermitian ∧ leastSquaresVector A b =
    fun i => (matrixPseudoinverse (hermitianDilation A) *ᵥ dilationInput b) (Sum.inr i)
  refine ⟨hermitianDilation_isHermitian A,?_⟩
  rw [hermitianDilation_pseudoinverse]
  funext i
  simp [Function.comp_def,dilationInput,Matrix.fromBlocks_mulVec,leastSquaresVector]

theorem rectangular_dilation_solution {O I : Type} [Fintype O] [DecidableEq O]
    [Fintype I] [DecidableEq I] (A : Matrix O I ℂ) (b : QState O) :
    (hermitianDilation A).IsHermitian ∧
    matrixPseudoinverse (hermitianDilation A) *ᵥ dilationInput b =
      Sum.elim (0 : QState O) (leastSquaresVector A b) ∧
    IsEuclideanLeastSquares A b (leastSquaresVector A b) ∧
    (∀ y : QState I, IsEuclideanLeastSquares A b y →
      ‖stateVector y‖ = ‖stateVector (leastSquaresVector A b)‖ → y = leastSquaresVector A b) ∧
    (leastSquaresOverlap A b = 0 ↔ leastSquaresVector A b = 0) ∧
    ‖stateVector b‖^2 = (leastSquaresOverlap A b)^2 +
      ‖stateVector (A *ᵥ leastSquaresVector A b - b)‖^2 := by
  refine ⟨hermitianDilation_isHermitian A,?_,
    (leastSquares_minimum_residual_and_norm A b).1,
    (leastSquares_minimum_residual_and_norm A b).2,
    (leastSquares_overlap_and_zero A b).2.1,
    (leastSquares_overlap_and_zero A b).2.2.2⟩
  rw [hermitianDilation_pseudoinverse]
  ext i
  cases i <;> simp [Function.comp_def,dilationInput,Matrix.fromBlocks_mulVec,leastSquaresVector]
  change ((matrixPseudoinverse A)ᴴ *ᵥ (0 : QState I)) _ = 0
  rw [Matrix.mulVec_zero]
  rfl

end Qatlib.Concepts.QlsReadoutSpec.RectDilation
