/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.EntangleTrans99.MainResults.Unitary.SchmidtUnitary

/-!
# Reduced spectra and local unitary conjugation

This module proves unitary conjugacy of Hermitian matrices with equal eigenvalue functions and
applies this to reduced matrices of normalized bipartite pure states with equal Schmidt spectra.
These results support the local-unitary spectral analysis in [Nielsen1999].

It also relates a unitary on the first subsystem to conjugation of its reduced matrix and proves
that `schmidtRotated` preserves the Schmidt spectrum while making the reduced matrix diagonal.

## Main statements

* `exists_unitary_conj_of_eigenvalues_eq`: constructs a unitary conjugation from equality of
  spectra.
* `reducedHermitian_apply_tensorLeft`: describes the reduced matrix after a local unitary.
* `reducedHermitian_schmidtRotated`: identifies the diagonal reduced matrix in Schmidt
  coordinates.

## References

* [Nielsen, 1999][Nielsen1999]
-/

set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false

noncomputable section

namespace Qatlib.Papers.EntangleTrans99.MainResults.Unitary

open Qatlib.Concepts.FiniteLocc.LOCCProgram
open Qatlib.Foundations.PureStateMath
open Qatlib.Foundations.PureStateMath.Reflection
open Qatlib.Concepts.Entanglement.Separability.EntanglementLOCC
open Qatlib.Concepts.Entanglement.Separability.EntanglementLOCCDefs
open Qatlib.Concepts.UnbiasedBases.ThreeBasis
open Qatlib.Concepts.QuantumEntropy.EntropyCalculus
open Qatlib.Foundations.PureStateMath.BornBridge

variable {D E : ℕ}

/-- Hermitian matrices with equal indexed eigenvalue functions are conjugate by a unitary matrix
[Nielsen1999]. -/
theorem exists_unitary_conj_of_eigenvalues_eq {d : ℕ} (A B : HermitianMat (Fin d) ℂ)
    (h : A.H.eigenvalues = B.H.eigenvalues) :
    ∃ U : Matrix.unitaryGroup (Fin d) ℂ,
      A = B.conj (U : Matrix (Fin d) (Fin d) ℂ) := by
  classical
  let UA : Matrix.unitaryGroup (Fin d) ℂ := A.H.eigenvectorUnitary
  let UB : Matrix.unitaryGroup (Fin d) ℂ := B.H.eigenvectorUnitary
  have hA : A = (HermitianMat.diagonal ℂ A.H.eigenvalues).conj
      (UA : Matrix (Fin d) (Fin d) ℂ) := by
    simpa [UA] using HermitianMat.eq_conj_diagonal A
  have hB : B = (HermitianMat.diagonal ℂ B.H.eigenvalues).conj
      (UB : Matrix (Fin d) (Fin d) ℂ) := by
    simpa [UB] using HermitianMat.eq_conj_diagonal B
  have hg : (UA * UB⁻¹ : Matrix.unitaryGroup (Fin d) ℂ) * UB = UA := by
    rw [mul_assoc, inv_mul_cancel, mul_one]
  have hcalc : ((UA * UB⁻¹ : Matrix.unitaryGroup (Fin d) ℂ) :
        Matrix (Fin d) (Fin d) ℂ) * (UB : Matrix (Fin d) (Fin d) ℂ) =
      (UA : Matrix (Fin d) (Fin d) ℂ) := by
    rw [← Submonoid.coe_mul, hg]
  refine ⟨UA * UB⁻¹, ?_⟩
  calc
    A = (HermitianMat.diagonal ℂ A.H.eigenvalues).conj
          (UA : Matrix (Fin d) (Fin d) ℂ) := hA
    _ = (HermitianMat.diagonal ℂ B.H.eigenvalues).conj
          (UA : Matrix (Fin d) (Fin d) ℂ) := by simp only [h]
    _ = ((HermitianMat.diagonal ℂ B.H.eigenvalues).conj
          (UB : Matrix (Fin d) (Fin d) ℂ)).conj
          ((UA * UB⁻¹ : Matrix.unitaryGroup (Fin d) ℂ) :
            Matrix (Fin d) (Fin d) ℂ) := by
        simp only [HermitianMat.conj_conj, hcalc]
    _ = B.conj ((UA * UB⁻¹ : Matrix.unitaryGroup (Fin d) ℂ) :
          Matrix (Fin d) (Fin d) ℂ) := by
        exact congrArg (fun X : HermitianMat (Fin d) ℂ =>
          X.conj ((UA * UB⁻¹ : Matrix.unitaryGroup (Fin d) ℂ) :
            Matrix (Fin d) (Fin d) ℂ)) hB.symm

/-- Normalized bipartite pure states with equal Schmidt spectra have unitarily conjugate reduced
Hermitian matrices on the first subsystem [Nielsen1999]. -/
theorem reducedHermitian_unitary_conj_of_spectrum_eq
    (ψ : QState (Fin D × Fin E)) (hψ : Normalized ψ)
    (φ : QState (Fin D × Fin E)) (hφ : Normalized φ)
    (h : schmidtSpectrum ψ hψ = schmidtSpectrum φ hφ) :
    ∃ U : Matrix.unitaryGroup (Fin D) ℂ,
      reducedHermitian ψ hψ = (reducedHermitian φ hφ).conj (U : Matrix (Fin D) (Fin D) ℂ) :=
  exists_unitary_conj_of_eigenvalues_eq (reducedHermitian ψ hψ) (reducedHermitian φ hφ) h

/-- Applying a unitary to the first subsystem conjugates its reduced Hermitian matrix by that
unitary [Nielsen1999]. -/
theorem reducedHermitian_apply_tensorLeft (ψ : QState (Fin D × Fin E)) (hψ : Normalized ψ)
    (U : Matrix (Fin D) (Fin D) ℂ) (_hU : U ∈ Matrix.unitaryGroup (Fin D) ℂ)
    (hψ' : Normalized (ApplyGate (TensorGate U (1 : Operator E)) ψ)) :
    reducedHermitian (ApplyGate (TensorGate U (1 : Operator E)) ψ) hψ'
      = (reducedHermitian ψ hψ).conj U := by
  ext1
  show (state (reducedDensity (ApplyGate (TensorGate U (1 : Operator E)) ψ) hψ')).m
      = ((reducedHermitian ψ hψ).conj U).mat
  rw [state_m, reducedDensity_val, HermitianMat.conj_apply_mat]
  have hred : (reducedHermitian ψ hψ).mat = PartialTrace (outerProduct ψ) := by
    show (state (reducedDensity ψ hψ)).m = _
    rw [state_m, reducedDensity_val]
  rw [hred]
  exact partialTrace_outerProduct_apply_tensorLeft D E U ψ

/-- If the reduced Hermitian matrix of `ψ` is the unitary conjugate of that of `φ`, it equals
the reduced Hermitian matrix obtained by applying that unitary to the first subsystem of `φ`
[Nielsen1999]. -/
theorem reducedHermitian_eq_of_unitary_conj
    (ψ : QState (Fin D × Fin E)) (hψ : Normalized ψ)
    (φ : QState (Fin D × Fin E)) (hφ : Normalized φ)
    (U : Matrix.unitaryGroup (Fin D) ℂ)
    (hU : reducedHermitian ψ hψ = (reducedHermitian φ hφ).conj (U : Matrix (Fin D) (Fin D) ℂ))
    (hφ' : Normalized
      (ApplyGate (TensorGate (U : Matrix (Fin D) (Fin D) ℂ) (1 : Operator E)) φ)) :
    reducedHermitian ψ hψ
      = reducedHermitian (ApplyGate (TensorGate (U : Matrix (Fin D) (Fin D) ℂ)
          (1 : Operator E)) φ) hφ' := by
  rw [hU, reducedHermitian_apply_tensorLeft φ hφ (U : Matrix (Fin D) (Fin D) ℂ) U.property hφ']

/-- The normalized state `schmidtRotated ψ hψ` has the same Schmidt spectrum as `ψ`
[Nielsen1999]. -/
theorem schmidtSpectrum_schmidtRotated (ψ : QState (Fin D × Fin E)) (hψ : Normalized ψ) :
    schmidtSpectrum (schmidtRotated ψ hψ) (schmidtRotated_normalized ψ hψ)
      = schmidtSpectrum ψ hψ :=
  schmidtSpectrum_apply_tensorLeft ψ hψ (schmidtUnitary ψ hψ).val.conjTranspose
    (schmidtUnitary_conjTranspose_mem ψ hψ) (schmidtRotated_normalized ψ hψ)

/-- The reduced Hermitian matrix of `schmidtRotated ψ hψ` is diagonal with diagonal entries
given by the Schmidt spectrum of `ψ` [Nielsen1999]. -/
theorem reducedHermitian_schmidtRotated (ψ : QState (Fin D × Fin E)) (hψ : Normalized ψ) :
    reducedHermitian (schmidtRotated ψ hψ) (schmidtRotated_normalized ψ hψ)
      = HermitianMat.diagonal ℂ (schmidtSpectrum ψ hψ) := by
  apply HermitianMat.ext
  rw [show (reducedHermitian (schmidtRotated ψ hψ) (schmidtRotated_normalized ψ hψ)).mat
        = PartialTrace (outerProduct (schmidtRotated ψ hψ)) from by
        show (state (reducedDensity (schmidtRotated ψ hψ)
            (schmidtRotated_normalized ψ hψ))).m = _
        rw [state_m, reducedDensity_val]]
  rw [partialTrace_outerProduct_schmidtRotated, HermitianMat.diagonal_mat]
  rfl

end Qatlib.Papers.EntangleTrans99.MainResults.Unitary
