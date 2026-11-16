/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Concepts.GibbsSource.CkgBounds.CKGWeight
public import Mathlib.Analysis.Matrix.Spectrum

@[expose] public section


/-!
# Complete CKG parents as Hermitian positive semidefinite matrices

The matrix below represents the existing complete linear map on all D²
matrix units. Both source normalizations are inherited without alteration.
No compression, discarded spectral mode, or extra kernel premise is used.
-/

open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.QuantumGibbs.FormAlgebra
open Qatlib.Concepts.GibbsSource.FormAlgebra
open Qatlib.Concepts.GibbsSource.CkgBounds
open Matrix
open scoped BigOperators MatrixOrder ComplexOrder

namespace Qatlib.Concepts.GibbsSource.SpectralGeom

variable {D : ℕ}

/-- Self-adjointness for the actual source Hilbert--Schmidt inner product. -/
def SourceSelfAdjoint (L : Operator D →ₗ[ℂ] Operator D) : Prop :=
  ∀ X Y, hsInner (L X) Y = hsInner X (L Y)

/-- Hs Inner parent Factor Adj left for the stated finite source data. -/
theorem hsInner_parentFactorAdj_left {ρ : Operator D}
    (hR : (fourthRoot ρ)ᴴ = fourthRoot ρ) (A X Y : Operator D) :
    hsInner (parentFactorAdj ρ A X) Y = hsInner X (parentFactor ρ A Y) := by
  calc
    _ = star (hsInner Y (parentFactorAdj ρ A X)) := hsInner_conj_swap _ _
    _ = star (hsInner (parentFactor ρ A Y) X) :=
      congrArg star (hsInner_parentFactor_adjoint hR A Y X).symm
    _ = _ := (hsInner_conj_swap X (parentFactor ρ A Y)).symm

/-- Symmetric real source coefficients give an actual self-adjoint linear map. -/
theorem sourceSelfAdjoint_parentGramFamOp {ι : Type*} [Fintype ι]
    {ρ : Operator D} (hR : (fourthRoot ρ)ᴴ = fourthRoot ρ)
    (w : ι → ι → ℝ) (hw : ∀ a b, w a b = w b a) (A : ι → Operator D) :
    SourceSelfAdjoint (parentGramFamOp w ρ A) := by
  intro X Y
  simp only [parentGramFamOp_apply, hsInner_sum_left, hsInner_sum_right,
    hsInner_smul_left, hsInner_smul_right,
    hsInner_parentFactorAdj_left hR, ← hsInner_parentFactor_adjoint hR]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro b _
  rw [hw b a]
  simp

/-- All matrix entries in one vector; no spectral projection is performed. -/
def sourceVector (X : Operator D) : (Fin D × Fin D) → ℂ := fun a => X a.1 a.2

def sourceUnvector (x : (Fin D × Fin D) → ℂ) : Operator D := fun i j => x (i, j)

/-- Reshaping the full vectorization restores every matrix entry. -/
@[simp] theorem sourceUnvector_vector (X : Operator D) :
    sourceUnvector (sourceVector X) = X := rfl

/-- Vectorizing a reshaped coordinate vector restores every coordinate. -/
@[simp] theorem sourceVector_unvector (x : (Fin D × Fin D) → ℂ) :
    sourceVector (sourceUnvector x) = x := by ext a; cases a; rfl

/-- Source Vector hs Inner for the stated finite source data. -/
theorem sourceVector_hsInner (X Y : Operator D) :
    star (sourceVector X) ⬝ᵥ sourceVector Y = hsInner X Y := by
  rw [hsInner_eq_sum]
  simp only [dotProduct, sourceVector, Pi.star_apply, Fintype.sum_prod_type]

/-- Hs Inner mat Unit left for the stated finite source data. -/
theorem hsInner_matUnit_left (i j : Fin D) (Y : Operator D) :
    hsInner (matUnit i j 1) Y = Y i j := by
  rw [hsInner_eq_sum]
  simp [matUnit_apply, apply_ite, ite_and]

/-- Hs Inner mat Unit right for the stated finite source data. -/
theorem hsInner_matUnit_right (i j : Fin D) (X : Operator D) :
    hsInner X (matUnit i j 1) = star (X i j) := by
  rw [hsInner_conj_swap X (matUnit i j 1), hsInner_matUnit_left]

/-- Matrix of the existing parent map in the complete orthonormal matrix-unit basis. -/
noncomputable def sourceSuperMatrix (L : Operator D →ₗ[ℂ] Operator D) :
    Matrix (Fin D × Fin D) (Fin D × Fin D) ℂ :=
  fun a b => L (matUnit b.1 b.2 1) a.1 a.2

/-- Source Super Matrix mul Vec for the stated finite source data. -/
theorem sourceSuperMatrix_mulVec (L : Operator D →ₗ[ℂ] Operator D)
    (X : Operator D) :
    sourceSuperMatrix L *ᵥ sourceVector X = sourceVector (L X) := by
  classical
  have hsum : X = ∑ b : Fin D × Fin D, X b.1 b.2 • matUnit b.1 b.2 1 := by
    ext i j
    simp only [Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul,
      matUnit_apply, Fintype.sum_prod_type]
    simp [ite_and]
  ext a
  conv_rhs => rw [hsum]
  simp only [sourceSuperMatrix, Matrix.mulVec, dotProduct, sourceVector,
    map_sum, map_smul, Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul]
  apply Finset.sum_congr rfl
  intro b _
  ring

/-- Source Super Matrix quadratic for the stated finite source data. -/
theorem sourceSuperMatrix_quadratic (L : Operator D →ₗ[ℂ] Operator D)
    (x : (Fin D × Fin D) → ℂ) :
    star x ⬝ᵥ (sourceSuperMatrix L *ᵥ x) =
      hsInner (sourceUnvector x) (L (sourceUnvector x)) := by
  have h := sourceSuperMatrix_mulVec L (sourceUnvector x)
  rw [sourceVector_unvector] at h
  rw [h, ← sourceVector_hsInner, sourceVector_unvector]

/-- Source Super Matrix is Hermitian for the stated finite source data. -/
theorem sourceSuperMatrix_isHermitian (L : Operator D →ₗ[ℂ] Operator D)
    (hL : SourceSelfAdjoint L) : (sourceSuperMatrix L).IsHermitian := by
  ext a b
  change star (L (matUnit a.1 a.2 1) b.1 b.2) = L (matUnit b.1 b.2 1) a.1 a.2
  simpa only [hsInner_matUnit_left, hsInner_matUnit_right] using
    hL (matUnit a.1 a.2 1) (matUnit b.1 b.2 1)

/-- Source Super Matrix pos Semidef for the stated finite source data. -/
theorem sourceSuperMatrix_posSemidef (L : Operator D →ₗ[ℂ] Operator D)
    (hL : SourceSelfAdjoint L) (hnonneg : ∀ X, 0 ≤ (hsInner X (L X)).re) :
    (sourceSuperMatrix L).PosSemidef := by
  have hh := sourceSuperMatrix_isHermitian L hL
  apply Matrix.PosSemidef.of_dotProduct_mulVec_nonneg hh
  intro x
  apply Complex.le_def.mpr
  refine ⟨?_, ?_⟩
  · rw [sourceSuperMatrix_quadratic]
    exact hnonneg _
  · exact (hh.im_star_dotProduct_mulVec_self x).symm


end Qatlib.Concepts.GibbsSource.SpectralGeom
