/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Concepts.GibbsSource.SpectralGeom.ParentSuperoperator
public import Qatlib.Concepts.GibbsSource.FormAlgebra.ParentGap

@[expose] public section


/-!
# Actual CKG eigenvalues consume source-form gap bounds

The complete D²-by-D² parent matrix retains every physical source mode.
Its nonzero eigenvectors are orthogonal to the actual Gibbs square root.
An already supplied `FormGapAtLeast` bound therefore bounds each actual
positive eigenvalue, including Mathlib's full Hermitian eigenvalue list.
The final comparison consumer is explicitly conditional: this module does
not produce a uniform comparison constant or a uniform positive gap.
-/

open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.QuantumGibbs.FormAlgebra
open Qatlib.Concepts.GibbsSource.FormAlgebra
open Qatlib.Concepts.GibbsSource.CkgBounds
open Matrix
open scoped BigOperators MatrixOrder ComplexOrder

namespace Qatlib.Concepts.GibbsSource.SpectralGeom

variable {D : ℕ}

/-- A nonzero eigenspace of a self-adjoint source map is orthogonal to its kernel. -/
theorem hsInner_kernel_eigenvector_eq_zero
    (L : Operator D →ₗ[ℂ] Operator D) (hL : SourceSelfAdjoint L)
    (W X : Operator D) (hW : L W = 0)
    {lam : ℂ} (hlam : lam ≠ 0) (hX : L X = lam • X) :
    hsInner W X = 0 := by
  have h := hL W X
  rw [hW, hX, hsInner_zero_left, hsInner_smul_right] at h
  exact (mul_eq_zero.mp h.symm).resolve_left hlam

/-- Source Unvector ne zero for the stated finite source data. -/
theorem sourceUnvector_ne_zero {x : (Fin D × Fin D) → ℂ} (hx : x ≠ 0) :
    sourceUnvector x ≠ 0 := by
  intro h
  apply hx
  have h' := congrArg sourceVector h
  simpa only [sourceVector_unvector, sourceVector, Matrix.zero_apply, Pi.zero_apply] using! h'

/-- An eigenvector of the complete matrix is the same eigenoperator of the actual map. -/
theorem sourceUnvector_eigenvector
    (L : Operator D →ₗ[ℂ] Operator D) (x : (Fin D × Fin D) → ℂ)
    (lam : ℂ) (hx : sourceSuperMatrix L *ᵥ x = lam • x) :
    L (sourceUnvector x) = lam • sourceUnvector x := by
  have h := sourceSuperMatrix_mulVec L (sourceUnvector x)
  rw [sourceVector_unvector, hx] at h
  ext i j
  exact (congrFun h (i, j)).symm

/-- Source form bounds control actual eigenvalues after the Gibbs direction is removed. -/
theorem eigenvalue_ge_source_formGap
    (L : Operator D →ₗ[ℂ] Operator D) (hL : SourceSelfAdjoint L)
    (E : Operator D → ℝ) (hE : ∀ X, E X = (hsInner X (L X)).re)
    (W : Operator D) (hW : L W = 0) (r lam : ℝ)
    (hgap : FormGapAtLeast E W r) (hlam : lam ≠ 0)
    (X : Operator D) (hX : X ≠ 0) (heig : L X = (lam : ℂ) • X) :
    r ≤ lam := by
  have horth := hsInner_kernel_eigenvector_eq_zero L hL W X hW
    (by exact_mod_cast hlam : (lam : ℂ) ≠ 0) heig
  have hvar : hsVar W X = (hsInner X X).re := by
    simp [hsVar, horth]
  have h := hgap X
  rw [hvar, hE X, heig, hsInner_smul_right, ofReal_mul_re] at h
  by_contra hnot
  have hlt : lam < r := lt_of_not_ge hnot
  have hprod := mul_lt_mul_of_pos_right hlt (hsInner_self_pos hX)
  exact (not_lt_of_ge h) hprod

/-- The genuine Hermitian eigenvalue list of the full source supermatrix. -/
noncomputable def sourceEigenvalues
    (L : Operator D →ₗ[ℂ] Operator D) (hL : SourceSelfAdjoint L) :
    (Fin D × Fin D) → ℝ :=
  (sourceSuperMatrix_isHermitian L hL).eigenvalues

/-- Mathlib's complete orthonormal eigenbasis, reshaped without projection. -/
noncomputable def sourceEigenoperator
    (L : Operator D →ₗ[ℂ] Operator D) (hL : SourceSelfAdjoint L)
    (i : Fin D × Fin D) : Operator D :=
  sourceUnvector (⇑((sourceSuperMatrix_isHermitian L hL).eigenvectorBasis i))

/-- Source Eigenoperator ne zero for the stated finite source data. -/
theorem sourceEigenoperator_ne_zero
    (L : Operator D →ₗ[ℂ] Operator D) (hL : SourceSelfAdjoint L)
    (i : Fin D × Fin D) : sourceEigenoperator L hL i ≠ 0 := by
  apply sourceUnvector_ne_zero
  exact (WithLp.ofLp_eq_zero 2).ne.2
    ((sourceSuperMatrix_isHermitian L hL).eigenvectorBasis.orthonormal.ne_zero i)

/-- Source Eigenoperator apply for the stated finite source data. -/
theorem sourceEigenoperator_apply
    (L : Operator D →ₗ[ℂ] Operator D) (hL : SourceSelfAdjoint L)
    (i : Fin D × Fin D) :
    L (sourceEigenoperator L hL i) =
      (sourceEigenvalues L hL i : ℂ) • sourceEigenoperator L hL i := by
  apply sourceUnvector_eigenvector
  have h := (sourceSuperMatrix_isHermitian L hL).mulVec_eigenvectorBasis i
  ext a
  simpa only [sourceEigenvalues, Pi.smul_apply, Complex.real_smul, smul_eq_mul] using congrFun h a


end Qatlib.Concepts.GibbsSource.SpectralGeom
