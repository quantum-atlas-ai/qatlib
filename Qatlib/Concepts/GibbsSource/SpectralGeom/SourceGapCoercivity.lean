/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Concepts.GibbsSource.SpectralGeom.SourcePositiveGap

@[expose] public section


/-!
# Full spectral coercivity and the source form gap

Parseval is applied to the complete Mathlib eigenbasis of the actual source
matrix.  Zero-eigenvalue coefficients vanish on the stated kernel's
orthogonal complement.  Thus the minimum positive spectrum itself supplies
a form-gap bound whenever the kernel is the stated single direction.
-/

open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.QuantumGibbs.FormAlgebra
open Qatlib.Concepts.GibbsSource.FormAlgebra
open Qatlib.Concepts.GibbsSource.CkgBounds
open Matrix
open scoped BigOperators

namespace Qatlib.Concepts.GibbsSource.SpectralGeom

variable {D : ℕ}

def sourceEuclideanVector (X : Operator D) : EuclideanSpace ℂ (Fin D × Fin D) :=
  WithLp.toLp 2 (sourceVector X)

/-- Source Euclidean Vector inner for the stated finite source data. -/
theorem sourceEuclideanVector_inner (X Y : Operator D) :
    inner ℂ (sourceEuclideanVector X) (sourceEuclideanVector Y) = hsInner X Y := by
  rw [EuclideanSpace.inner_eq_star_dotProduct, dotProduct_comm]
  exact sourceVector_hsInner X Y

/-- Source Euclidean Vector eigenoperator for the stated finite source data. -/
theorem sourceEuclideanVector_eigenoperator
    (L : Operator D →ₗ[ℂ] Operator D) (hL : SourceSelfAdjoint L)
    (i : Fin D × Fin D) :
    sourceEuclideanVector (sourceEigenoperator L hL i) =
      (sourceSuperMatrix_isHermitian L hL).eigenvectorBasis i := by
  unfold sourceEuclideanVector sourceEigenoperator
  rw [sourceVector_unvector]

/-- Parseval on every D² eigenoperator, without removing or compressing modes. -/
theorem source_hsInner_eq_sum_eigenoperators
    (L : Operator D →ₗ[ℂ] Operator D) (hL : SourceSelfAdjoint L)
    (X Y : Operator D) :
    hsInner X Y = ∑ i, hsInner X (sourceEigenoperator L hL i) *
      hsInner (sourceEigenoperator L hL i) Y := by
  classical
  let b := (sourceSuperMatrix_isHermitian L hL).eigenvectorBasis
  calc
    hsInner X Y = inner ℂ (sourceEuclideanVector X) (sourceEuclideanVector Y) :=
      (sourceEuclideanVector_inner X Y).symm
    _ = ∑ i, inner ℂ (sourceEuclideanVector X) (b i) *
        inner ℂ (b i) (sourceEuclideanVector Y) :=
      (b.sum_inner_mul_inner _ _).symm
    _ = _ := by
      apply Finset.sum_congr rfl
      intro i _
      rw [show b i = sourceEuclideanVector (sourceEigenoperator L hL i) from
        (sourceEuclideanVector_eigenoperator L hL i).symm]
      rw [sourceEuclideanVector_inner, sourceEuclideanVector_inner]

/-- Source hs Norm Sq eq sum coefficients for the stated finite source data. -/
theorem source_hsNormSq_eq_sum_coefficients
    (L : Operator D →ₗ[ℂ] Operator D) (hL : SourceSelfAdjoint L) (X : Operator D) :
    (hsInner X X).re = ∑ i, Complex.normSq (hsInner (sourceEigenoperator L hL i) X) := by
  classical
  calc
    (hsInner X X).re = (∑ i, hsInner X (sourceEigenoperator L hL i) *
        hsInner (sourceEigenoperator L hL i) X).re :=
      congrArg Complex.re (source_hsInner_eq_sum_eigenoperators L hL X X)
    _ = ∑ i, (hsInner X (sourceEigenoperator L hL i) *
        hsInner (sourceEigenoperator L hL i) X).re := map_sum complexReAddMonoidHom _ _
    _ = _ := by
      apply Finset.sum_congr rfl
      intro i _
      rw [hsInner_conj_swap X (sourceEigenoperator L hL i)]
      exact re_star_mul_self _

/-- Source energy eq sum eigenvalues for the stated finite source data. -/
theorem source_energy_eq_sum_eigenvalues
    (L : Operator D →ₗ[ℂ] Operator D) (hL : SourceSelfAdjoint L) (X : Operator D) :
    (hsInner X (L X)).re = ∑ i, sourceEigenvalues L hL i *
      Complex.normSq (hsInner (sourceEigenoperator L hL i) X) := by
  classical
  calc
    (hsInner X (L X)).re = (∑ i, hsInner X (sourceEigenoperator L hL i) *
        hsInner (sourceEigenoperator L hL i) (L X)).re :=
      congrArg Complex.re (source_hsInner_eq_sum_eigenoperators L hL X (L X))
    _ = ∑ i, (hsInner X (sourceEigenoperator L hL i) *
        hsInner (sourceEigenoperator L hL i) (L X)).re := map_sum complexReAddMonoidHom _ _
    _ = _ := by
      apply Finset.sum_congr rfl
      intro i _
      have hc : hsInner (sourceEigenoperator L hL i) (L X) =
          (sourceEigenvalues L hL i : ℂ) * hsInner (sourceEigenoperator L hL i) X := by
        rw [← hL (sourceEigenoperator L hL i) X, sourceEigenoperator_apply,
          hsInner_smul_left]
        simp
      rw [hc, hsInner_conj_swap X (sourceEigenoperator L hL i)]
      have halg (z : ℂ) (r : ℝ) : star z * ((r : ℂ) * z) =
          (r : ℂ) * (star z * z) := by ring
      rw [halg, star_mul_self_eq, ofReal_mul_re, Complex.ofReal_re]

/-- On the full kernel complement the actual minimum positive spectrum is coercive. -/
theorem sourcePositiveGap_coercive_on_kernel_orthogonal
    (L : Operator D →ₗ[ℂ] Operator D) (hL : SourceSelfAdjoint L)
    (hE : ∀ X, 0 ≤ (hsInner X (L X)).re) (W : Operator D)
    (hker : ∀ X, L X = 0 → ∃ c : ℂ, X = c • W)
    (X : Operator D) (hX : hsInner W X = 0) :
    sourcePositiveGap L hL * (hsInner X X).re ≤ (hsInner X (L X)).re := by
  classical
  rw [source_hsNormSq_eq_sum_coefficients L hL X, source_energy_eq_sum_eigenvalues L hL X,
    Finset.mul_sum]
  apply Finset.sum_le_sum
  intro i _
  by_cases hi : 0 < sourceEigenvalues L hL i
  · exact mul_le_mul_of_nonneg_right (sourcePositiveGap_le_eigenvalue L hL i hi)
      (Complex.normSq_nonneg _)
  · have hi0 : sourceEigenvalues L hL i = 0 :=
      le_antisymm (le_of_not_gt hi) (sourceEigenvalues_nonneg L hL hE i)
    have hz : L (sourceEigenoperator L hL i) = 0 := by
      rw [sourceEigenoperator_apply, hi0, Complex.ofReal_zero, zero_smul]
    obtain ⟨c, hc⟩ := hker (sourceEigenoperator L hL i) hz
    have hcoeff : hsInner (sourceEigenoperator L hL i) X = 0 := by
      rw [hc, hsInner_smul_left, hX, mul_zero]
    simp [hi0, hcoeff]

/-- The minimum positive spectrum supplies the full source `FormGapAtLeast` predicate. -/
theorem sourcePositiveGap_formGap
    (L : Operator D →ₗ[ℂ] Operator D) (hL : SourceSelfAdjoint L)
    (hE : ∀ X, 0 ≤ (hsInner X (L X)).re) (W : Operator D) (hW : L W = 0)
    (hker : ∀ X, L X = 0 → ∃ c : ℂ, X = c • W) :
    FormGapAtLeast (fun X => (hsInner X (L X)).re) W (sourcePositiveGap L hL) := by
  intro X
  by_cases hW0 : W = 0
  · have horth : hsInner W X = 0 := by simp [hW0, hsInner]
    have h := sourcePositiveGap_coercive_on_kernel_orthogonal L hL hE W hker X horth
    simpa [hsVar, hW0, hsInner] using h
  · let c : ℂ := hsInner W X / hsInner W W
    let Y := X - c • W
    have hWW : hsInner W W ≠ 0 := by
      intro hz
      have hp := hsInner_self_pos hW0
      rw [hz] at hp
      exact (lt_irrefl 0) hp
    have horth : hsInner W Y = 0 := by
      dsimp only [Y]
      rw [hsInner_sub_right, hsInner_smul_right]
      dsimp only [c]
      rw [div_mul_cancel₀ _ hWW, sub_self]
    have hcoerc := sourcePositiveGap_coercive_on_kernel_orthogonal L hL hE W hker Y horth
    have hvar := hsInner_sub_normSq_ge X W (hsInner_self_pos hW0) c
    have hWX : hsInner W (L X) = 0 := by
      rw [← hL W X, hW]
      simp [hsInner]
    have henergy : (hsInner Y (L Y)).re = (hsInner X (L X)).re := by
      simp only [Y, map_sub, map_smul, hW, smul_zero, sub_zero,
        hsInner_sub_left, hsInner_smul_left, hWX, mul_zero]
    calc
      sourcePositiveGap L hL * hsVar W X ≤
          sourcePositiveGap L hL * (hsInner Y Y).re :=
        mul_le_mul_of_nonneg_left hvar (sourcePositiveGap_nonneg L hL)
      _ ≤ (hsInner Y (L Y)).re := hcoerc
      _ = (hsInner X (L X)).re := henergy

end Qatlib.Concepts.GibbsSource.SpectralGeom
