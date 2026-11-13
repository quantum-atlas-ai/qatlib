/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.SpectralSketch.SketchSpectral.SvtGramTransferStat

/-!
# Functional calculus transfer between Gram matrices

This module proves the functional-calculus identity specified by `SvtGramTransfer`, transporting
a function of the row Gram matrix through a rectangular matrix to a weighted function of its
column Gram matrix. The identity is used in the matrix-arithmetic framework of [ChiaEtAl2022].

The auxiliary theorem `hermitianFunction_eigenvector` identifies the action of an arbitrary
spectral function on a Hermitian eigenvector.

## Main statements

* `hermitianFunction_eigenvector`: spectral functions apply the scalar function to eigenvalues.
* `svtGramTransfer_proof`: the adjoint Gram-transfer identity for arbitrary scalar functions.

## References

* [Chia et al., 2022][ChiaEtAl2022]
* [Bhatia, 1997][Bhatia1997]
-/

open Qatlib.Concepts.PhaseGeometry.Phase
open Qatlib.Concepts.OperatorErrors.Robustness.SignalProcessing

open Qatlib.Concepts.SpectralSketch.SpectrumPerturb
open Qatlib.Concepts.WalkSearch.Spectral

namespace Qatlib.Concepts.SpectralSketch.SketchSpectral

open Matrix Qatlib.Concepts.PhaseGeometry.Phase
open Qatlib.Concepts.OperatorErrors.Robustness.SignalProcessing

/-- If `v` is an eigenvector of a Hermitian matrix with real eigenvalue `lam`, applying
`hermitianFunction` with scalar function `f` sends `v` to `f lam • v`. -/
theorem hermitianFunction_eigenvector {I : Type} [Fintype I] [DecidableEq I]
    (A : Matrix I I ℂ) (hA : A.IsHermitian) (f : ℝ → ℂ) (lam : ℝ) (v : I → ℂ)
    (hv : A *ᵥ v = (lam : ℂ) • v) :
    hermitianFunction A hA f *ᵥ v = f lam • v := by
  let b := orderedHermitianBasis hA
  let V : Matrix I (Fin (Fintype.card I)) ℂ := basisColumns b
  let u := Vᴴ *ᵥ v
  have hVA : Vᴴ * A = Matrix.diagonal (fun j => (orderedHermitianValues hA j : ℂ)) * Vᴴ := by
    calc
      _ = Vᴴ * spectralDiagonal b (fun j => (orderedHermitianValues hA j : ℂ)) :=
        congrArg (fun M : Matrix I I ℂ => Vᴴ * M) (orderedHermitian_diagonal hA)
      _ = _ := basis_adjoint_mul_spectralDiagonal b _
  have hu := congrArg (fun w : I → ℂ => Vᴴ *ᵥ w) hv

  rw [Matrix.mulVec_mulVec, hVA, ← Matrix.mulVec_mulVec, Matrix.mulVec_smul] at hu
  have hcoord (j : Fin (Fintype.card I)) :
      (orderedHermitianValues hA j : ℂ) * u j = (lam : ℂ) * u j := by
    simpa only [Matrix.mulVec_diagonal, Pi.smul_apply, smul_eq_mul] using! congrFun hu j
  have hdiag : Matrix.diagonal (fun j => f (orderedHermitianValues hA j)) *ᵥ u = f lam • u := by
    ext j
    rw [Matrix.mulVec_diagonal]
    change f (orderedHermitianValues hA j) * u j = f lam * u j
    by_cases he : orderedHermitianValues hA j = lam
    · rw [he]
    · have hmul : ((orderedHermitianValues hA j : ℂ) - (lam : ℂ)) * u j = 0 := by
        linear_combination hcoord j
      have hne : (orderedHermitianValues hA j : ℂ) - (lam : ℂ) ≠ 0 := by
        apply sub_ne_zero.mpr
        exact_mod_cast he
      have hz := (mul_eq_zero.mp hmul).resolve_left hne
      rw [hz, mul_zero, mul_zero]
  change (V * Matrix.diagonal (fun j => f (orderedHermitianValues hA j)) * Vᴴ) *ᵥ v = _
  rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hdiag,
    Matrix.mulVec_smul, Matrix.mulVec_mulVec, basisColumns_mul_adjoint, Matrix.one_mulVec]

/-- Establish `SvtGramTransfer`, the identity transporting functional calculus between the row
and column Gram matrices through the rectangular matrix and its adjoint. -/
theorem svtGramTransfer_proof : SvtGramTransfer := by
  intro K C _ _ _ _ R g
  let A : Matrix C C ℂ := Rᴴ * R
  let B : Matrix K K ℂ := R * Rᴴ
  let hA : A.IsHermitian := Matrix.isHermitian_conjTranspose_mul_self R
  let hB : B.IsHermitian := Matrix.isHermitian_mul_conjTranspose_self R
  let b := orderedHermitianBasis hA
  let V : Matrix C (Fin (Fintype.card C)) ℂ := basisColumns b
  have hVV : V * Vᴴ = 1 := basisColumns_mul_adjoint b
  have hEig (i : Fin (Fintype.card C)) :
      A *ᵥ (fun c => V c i) = (orderedHermitianValues hA i : ℂ) • (fun c => V c i) := by
    have h := congrArg (fun x : EuclideanSpace ℂ C => x.ofLp) (orderedHermitianBasis_action hA i)
    exact h
  have hR (i : Fin (Fintype.card C)) :
      B *ᵥ (R *ᵥ (fun c => V c i)) =
        (orderedHermitianValues hA i : ℂ) • (R *ᵥ (fun c => V c i)) := by
    calc
      _ = R *ᵥ (A *ᵥ (fun c => V c i)) := by
        simp only [Matrix.mulVec_mulVec, Matrix.mul_assoc, A, B]
      _ = _ := by rw [hEig i, Matrix.mulVec_smul]
  have hsame : (Rᴴ * hermitianFunction B hB g * R) * V =
      hermitianFunction A hA (fun x => g x * x) * V := by
    ext c i
    change ((Rᴴ * hermitianFunction B hB g * R) *ᵥ (fun c => V c i)) c =
      (hermitianFunction A hA (fun x => g x * x) *ᵥ (fun c => V c i)) c
    rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec,
      hermitianFunction_eigenvector B hB g _ _ (hR i), Matrix.mulVec_smul,
      Matrix.mulVec_mulVec, hEig i,
      hermitianFunction_eigenvector A hA (fun x => g x * x) _ _ (hEig i), smul_smul]
  change Rᴴ * hermitianFunction B hB g * R = hermitianFunction A hA (fun x => g x * x)
  calc
    _ = ((Rᴴ * hermitianFunction B hB g * R) * V) * Vᴴ := by
      simp only [Matrix.mul_assoc, hVV, Matrix.mul_one]
    _ = (hermitianFunction A hA (fun x => g x * x) * V) * Vᴴ := by rw [hsame]
    _ = _ := by simp only [Matrix.mul_assoc, hVV, Matrix.mul_one]

end Qatlib.Concepts.SpectralSketch.SketchSpectral
