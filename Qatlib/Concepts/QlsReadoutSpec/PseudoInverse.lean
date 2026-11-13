/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.HhlAlgorithms.UniformHHL.OffGridHHLConsumers
import Qatlib.Concepts.LocalMachine.LocalTransport.LeastSquaresOutputSpec

/-!
# Spectral pseudoinverses for Hermitian systems

This module expresses the pseudoinverse of a unitarily diagonalized real-spectrum matrix by
reciprocating its eigenvalues, with zero eigenvalues remaining zero. The matrix-pseudoinverse
product is the spectral support operator, and applying the pseudoinverse yields a Euclidean
least-squares solution. Related mathematical background is given in [Bhatia1997].

## Main statements

* `spectralSupport`: Operator selecting the nonzero spectral modes.
* `singular_hermitian_pseudoinverse_and_least_squares`: Spectral pseudoinverse, support, and
  least-squares identities.

## References

* [Bhatia, 1997][Bhatia1997]
-/

open Qatlib.Concepts.CoherentSim.CoherentOAA.SignalProcessing
open Qatlib.Concepts.PhaseGeometry.Phase
open Qatlib.Concepts.OperatorErrors.Robustness.SignalProcessing

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Qatlib.Foundations.PureStateMath

open Qatlib.Concepts.CoherentSim.CoherentOAA Qatlib.Foundations.InstrumentCore.ProjectiveMeasurementLaws Qatlib.Foundations.OperatorErrors.OperatorError
open Qatlib.Concepts.LocalMachine.LocalTransport
open Qatlib.Concepts.HhlAlgorithms.SinEnvProgram

namespace Qatlib.Concepts.QlsReadoutSpec.PseudoInverse
open Qatlib.Concepts.QueryWordCore.AdjointCircuits
open Qatlib.Concepts.CoherentSim.CoherentOAA.SignalProcessing Qatlib.Concepts.PhaseGeometry.Phase
open Qatlib.Concepts.OperatorErrors.Robustness.SignalProcessing Matrix
open scoped Classical BigOperators Matrix.Norms.L2Operator ENNReal

/-- The spectral operator obtained by conjugating the diagonal indicator of nonzero eigenvalues
by `V`. -/
noncomputable def spectralSupport {D : ℕ} (eig : Fin D → ℝ) (V : Operator D) : Operator D :=
  V * Matrix.diagonal (fun i => if eig i = 0 then 0 else 1) * Vᴴ

/-- Products of two diagonal matrices conjugated by the same unitary equal the conjugation of
their pointwise diagonal product. -/
theorem singular_conj_diagonal_mul {D : ℕ} (w z : Fin D → ℂ) (V : Operator D)
    (hV : V ∈ Matrix.unitaryGroup (Fin D) ℂ) :
    (V*Matrix.diagonal w*Vᴴ)*(V*Matrix.diagonal z*Vᴴ) =
      V*Matrix.diagonal (fun i => w i*z i)*Vᴴ := by
  have hv : Vᴴ*V=1 := by
    simpa only [Matrix.mem_unitaryGroup_iff', Matrix.star_eq_conjTranspose] using! hV
  have ha : (V*Matrix.diagonal w*Vᴴ)*(V*Matrix.diagonal z*Vᴴ) =
      V*(Matrix.diagonal w*((Vᴴ*V)*Matrix.diagonal z))*Vᴴ := by noncomm_ring
  rw [ha, hv, Matrix.one_mul, Matrix.diagonal_mul_diagonal]

/-- The real-spectrum matrix and its reciprocal-eigenvalue candidate inverse multiply in either
order to the spectral support operator. -/
theorem singular_hermitian_support_products (D : ℕ) (eig : Fin D → ℝ) (V : Operator D)
    (hV : V ∈ Matrix.unitaryGroup (Fin D) ℂ) :
    continuousHHLMatrix eig V * (V*Matrix.diagonal (fun i => (eig i:ℂ)⁻¹)*Vᴴ) = spectralSupport eig V ∧
    (V*Matrix.diagonal (fun i => (eig i:ℂ)⁻¹)*Vᴴ) * continuousHHLMatrix eig V = spectralSupport eig V := by
  have he (i : Fin D) : (eig i:ℂ)*(eig i:ℂ)⁻¹ = if eig i=0 then 0 else 1 := by
    by_cases h : eig i=0
    · simp [h]
    · simp only [if_neg h]
      exact mul_inv_cancel₀ (Complex.ofReal_ne_zero.mpr h)
  constructor
  · rw [continuousHHLMatrix, singular_conj_diagonal_mul _ _ V hV]
    simp only [he, spectralSupport]
  · rw [continuousHHLMatrix, singular_conj_diagonal_mul _ _ V hV]
    simp only [mul_comm, he, spectralSupport]

/-- The pseudoinverse of a unitarily diagonalized real-spectrum matrix is obtained by
reciprocating its eigenvalues, and its product with the matrix is the spectral support
operator. Applying this pseudoinverse to any right-hand side gives a Euclidean least-squares
solution. -/
theorem singular_hermitian_pseudoinverse_and_least_squares : ∀ (D : ℕ) (eig : Fin D → ℝ) (V : Operator D),
  V ∈ Matrix.unitaryGroup (Fin D) ℂ →
  matrixPseudoinverse (continuousHHLMatrix eig V) =
    V * Matrix.diagonal (fun i => ((eig i : ℂ)⁻¹)) * Vᴴ ∧
  continuousHHLMatrix eig V * matrixPseudoinverse (continuousHHLMatrix eig V) = spectralSupport eig V ∧
  (∀ b : QState (Fin D), IsEuclideanLeastSquares (continuousHHLMatrix eig V) b
    (matrixPseudoinverse (continuousHHLMatrix eig V) *ᵥ b))
 := by
  intro D eig V hV
  let R : Operator D := V*Matrix.diagonal (fun i => (eig i:ℂ)⁻¹)*Vᴴ
  obtain ⟨har,hra⟩ := singular_hermitian_support_products D eig V hV
  have hpA : spectralSupport eig V * continuousHHLMatrix eig V = continuousHHLMatrix eig V := by
    rw [spectralSupport, continuousHHLMatrix, singular_conj_diagonal_mul _ _ V hV]
    apply congrArg (fun w : Fin D → ℂ => V*Matrix.diagonal w*Vᴴ)
    funext i
    by_cases he : eig i=0 <;> simp [he]
  have hpR : spectralSupport eig V * R = R := by
    dsimp only [R]
    rw [spectralSupport, singular_conj_diagonal_mul _ _ V hV]
    apply congrArg (fun w : Fin D → ℂ => V*Matrix.diagonal w*Vᴴ)
    funext i
    by_cases he : eig i=0 <;> simp [he]
  have hstar : (spectralSupport eig V)ᴴ = spectralSupport eig V := by
    simp only [spectralSupport, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose,
      Matrix.diagonal_conjTranspose, Matrix.mul_assoc]
    apply congrArg (fun w : Fin D → ℂ => V*(Matrix.diagonal w*Vᴴ))
    funext i
    by_cases he : eig i=0 <;> simp [he]
  have hinv : matrixPseudoinverse (continuousHHLMatrix eig V) = R :=
    (matrixPseudoinverse_unique _ R
      (by rw [har]; exact hpA) (by rw [hra]; exact hpR)
      (by rw [har]; exact hstar) (by rw [hra]; exact hstar)).symm
  refine ⟨hinv, ?_, ?_⟩
  · rw [hinv]
    exact har
  · intro b
    exact (leastSquares_minimum_residual_and_norm (continuousHHLMatrix eig V) b).1

end Qatlib.Concepts.QlsReadoutSpec.PseudoInverse
