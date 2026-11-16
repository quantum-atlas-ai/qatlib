/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Concepts.GibbsSource.SpectralGeom.PhysicalCkgSpectralGap

@[expose] public section


/-!
# The least positive eigenvalue of the complete source parent

The finite set below is taken from Mathlib's actual Hermitian eigenvalue list
of the complete source matrix.  The empty-positive-spectrum convention is
explicitly zero, including zero-dimensional and zero-operator cases.
Nonempty positive spectrum gives a strictly positive, attained minimum.
These finite-dimensional facts do not assert a size-uniform lower bound.
-/

open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.QuantumGibbs.FormAlgebra
open Qatlib.Concepts.GibbsSource.FormAlgebra
open Matrix
open scoped BigOperators

namespace Qatlib.Concepts.GibbsSource.SpectralGeom

variable {D : ℕ}

/-- Every actual strictly positive eigenvalue, with multiplicities discarded. -/
noncomputable def sourcePositiveSpectrum
    (L : Operator D →ₗ[ℂ] Operator D) (hL : SourceSelfAdjoint L) : Finset ℝ := by
  classical
  exact (Finset.univ.image (sourceEigenvalues L hL)).filter (fun r => 0 < r)

/-- Mem source Positive Spectrum for the stated finite source data. -/
theorem mem_sourcePositiveSpectrum
    (L : Operator D →ₗ[ℂ] Operator D) (hL : SourceSelfAdjoint L) (r : ℝ) :
    r ∈ sourcePositiveSpectrum L hL ↔
      0 < r ∧ ∃ i : Fin D × Fin D, sourceEigenvalues L hL i = r := by
  classical
  unfold sourcePositiveSpectrum
  constructor
  · intro h
    obtain ⟨him, hp⟩ := Finset.mem_filter.mp h
    obtain ⟨i, _, hi⟩ := Finset.mem_image.mp him
    exact ⟨hp, i, hi⟩
  · rintro ⟨hp, i, hi⟩
    exact Finset.mem_filter.mpr ⟨Finset.mem_image.mpr ⟨i, Finset.mem_univ i, hi⟩, hp⟩

/-- Source Positive Spectrum nonempty iff for the stated finite source data. -/
theorem sourcePositiveSpectrum_nonempty_iff
    (L : Operator D →ₗ[ℂ] Operator D) (hL : SourceSelfAdjoint L) :
    (sourcePositiveSpectrum L hL).Nonempty ↔
      ∃ i : Fin D × Fin D, 0 < sourceEigenvalues L hL i := by
  constructor
  · rintro ⟨r, hr⟩
    obtain ⟨hp, i, hi⟩ := (mem_sourcePositiveSpectrum L hL r).mp hr
    exact ⟨i, by simpa only [hi] using hp⟩
  · rintro ⟨i, hi⟩
    exact ⟨sourceEigenvalues L hL i,
      (mem_sourcePositiveSpectrum L hL _).mpr ⟨hi, i, rfl⟩⟩

/-- Minimum positive eigenvalue; it is zero when the positive spectrum is empty. -/
noncomputable def sourcePositiveGap
    (L : Operator D →ₗ[ℂ] Operator D) (hL : SourceSelfAdjoint L) : ℝ := by
  classical
  exact if h : (sourcePositiveSpectrum L hL).Nonempty then
    (sourcePositiveSpectrum L hL).min' h else 0

/-- Source Positive Gap eq zero of empty for the stated finite source data. -/
theorem sourcePositiveGap_eq_zero_of_empty
    (L : Operator D →ₗ[ℂ] Operator D) (hL : SourceSelfAdjoint L)
    (h : ¬ (sourcePositiveSpectrum L hL).Nonempty) : sourcePositiveGap L hL = 0 := by
  classical
  simp [sourcePositiveGap, h]

/-- Source Positive Gap mem for the stated finite source data. -/
theorem sourcePositiveGap_mem
    (L : Operator D →ₗ[ℂ] Operator D) (hL : SourceSelfAdjoint L)
    (h : (sourcePositiveSpectrum L hL).Nonempty) :
    sourcePositiveGap L hL ∈ sourcePositiveSpectrum L hL := by
  classical
  rw [sourcePositiveGap, dite_eq_left h]
  exact Finset.min'_mem _ h

/-- Source Positive Gap pos for the stated finite source data. -/
theorem sourcePositiveGap_pos
    (L : Operator D →ₗ[ℂ] Operator D) (hL : SourceSelfAdjoint L)
    (h : (sourcePositiveSpectrum L hL).Nonempty) : 0 < sourcePositiveGap L hL :=
  ((mem_sourcePositiveSpectrum L hL _).mp (sourcePositiveGap_mem L hL h)).1

/-- Source Positive Gap nonneg for the stated finite source data. -/
theorem sourcePositiveGap_nonneg
    (L : Operator D →ₗ[ℂ] Operator D) (hL : SourceSelfAdjoint L) :
    0 ≤ sourcePositiveGap L hL := by
  classical
  by_cases h : (sourcePositiveSpectrum L hL).Nonempty
  · exact (sourcePositiveGap_pos L hL h).le
  · rw [sourcePositiveGap_eq_zero_of_empty L hL h]

/-- Source Positive Gap pos iff for the stated finite source data. -/
theorem sourcePositiveGap_pos_iff
    (L : Operator D →ₗ[ℂ] Operator D) (hL : SourceSelfAdjoint L) :
    0 < sourcePositiveGap L hL ↔ (sourcePositiveSpectrum L hL).Nonempty := by
  classical
  constructor
  · intro hp
    by_contra h
    rw [sourcePositiveGap_eq_zero_of_empty L hL h] at hp
    exact (lt_irrefl 0) hp
  · exact sourcePositiveGap_pos L hL

/-- Source Positive Gap attained for the stated finite source data. -/
theorem sourcePositiveGap_attained
    (L : Operator D →ₗ[ℂ] Operator D) (hL : SourceSelfAdjoint L)
    (h : (sourcePositiveSpectrum L hL).Nonempty) :
    ∃ i : Fin D × Fin D, 0 < sourceEigenvalues L hL i ∧
      sourceEigenvalues L hL i = sourcePositiveGap L hL := by
  obtain ⟨hp, i, hi⟩ :=
    (mem_sourcePositiveSpectrum L hL _).mp (sourcePositiveGap_mem L hL h)
  exact ⟨i, by simpa only [hi] using hp, hi⟩

/-- Source Positive Gap le eigenvalue for the stated finite source data. -/
theorem sourcePositiveGap_le_eigenvalue
    (L : Operator D →ₗ[ℂ] Operator D) (hL : SourceSelfAdjoint L)
    (i : Fin D × Fin D) (hi : 0 < sourceEigenvalues L hL i) :
    sourcePositiveGap L hL ≤ sourceEigenvalues L hL i := by
  classical
  have hmem : sourceEigenvalues L hL i ∈ sourcePositiveSpectrum L hL :=
    (mem_sourcePositiveSpectrum L hL _).mpr ⟨hi, i, rfl⟩
  have hne : (sourcePositiveSpectrum L hL).Nonempty := ⟨_, hmem⟩
  rw [sourcePositiveGap, dite_eq_left hne]
  exact Finset.min'_le _ _ hmem

/-- A bound for all genuine positive eigenvalues bounds their attained minimum. -/
theorem le_sourcePositiveGap
    (L : Operator D →ₗ[ℂ] Operator D) (hL : SourceSelfAdjoint L)
    (h : (sourcePositiveSpectrum L hL).Nonempty) (r : ℝ)
    (hb : ∀ i, 0 < sourceEigenvalues L hL i → r ≤ sourceEigenvalues L hL i) :
    r ≤ sourcePositiveGap L hL := by
  obtain ⟨i, hi, heq⟩ := sourcePositiveGap_attained L hL h
  rw [← heq]
  exact hb i hi

/-- Source Super Matrix eq zero iff for the stated finite source data. -/
theorem sourceSuperMatrix_eq_zero_iff (L : Operator D →ₗ[ℂ] Operator D) :
    sourceSuperMatrix L = 0 ↔ L = 0 := by
  constructor
  · intro h
    apply LinearMap.ext
    intro X
    have hv := sourceSuperMatrix_mulVec L X
    rw [h, Matrix.zero_mulVec] at hv
    ext i j
    exact (congrFun hv (i, j)).symm
  · rintro rfl
    ext a b
    rfl

/-- Nonnegative source energy makes every actual eigenvalue nonnegative. -/
theorem sourceEigenvalues_nonneg
    (L : Operator D →ₗ[ℂ] Operator D) (hL : SourceSelfAdjoint L)
    (hE : ∀ X, 0 ≤ (hsInner X (L X)).re) (i : Fin D × Fin D) :
    0 ≤ sourceEigenvalues L hL i := by
  have h := hE (sourceEigenoperator L hL i)
  rw [sourceEigenoperator_apply, hsInner_smul_right, ofReal_mul_re] at h
  have hp := hsInner_self_pos (sourceEigenoperator_ne_zero L hL i)
  nlinarith

/-- A nonzero, nonnegative complete parent has an actual positive eigenvalue. -/
theorem sourcePositiveSpectrum_nonempty_of_nonneg_ne_zero
    (L : Operator D →ₗ[ℂ] Operator D) (hL : SourceSelfAdjoint L)
    (hE : ∀ X, 0 ≤ (hsInner X (L X)).re) (hL0 : L ≠ 0) :
    (sourcePositiveSpectrum L hL).Nonempty := by
  apply (sourcePositiveSpectrum_nonempty_iff L hL).mpr
  by_contra h
  have hz : sourceEigenvalues L hL = 0 := by
    funext i
    apply le_antisymm
    · exact le_of_not_gt (fun hi => h ⟨i, hi⟩)
    · exact sourceEigenvalues_nonneg L hL hE i
  have hmat : sourceSuperMatrix L = 0 :=
    (sourceSuperMatrix_isHermitian L hL).eigenvalues_eq_zero_iff.mp hz
  exact hL0 ((sourceSuperMatrix_eq_zero_iff L).mp hmat)

/-- Source Positive Spectrum nonempty of positive energy for the stated finite source data. -/
theorem sourcePositiveSpectrum_nonempty_of_positive_energy
    (L : Operator D →ₗ[ℂ] Operator D) (hL : SourceSelfAdjoint L)
    (hE : ∀ X, 0 ≤ (hsInner X (L X)).re)
    (X : Operator D) (hX : 0 < (hsInner X (L X)).re) :
    (sourcePositiveSpectrum L hL).Nonempty := by
  apply sourcePositiveSpectrum_nonempty_of_nonneg_ne_zero L hL hE
  intro hzero
  rw [hzero] at hX
  simp only [LinearMap.zero_apply, hsInner, Matrix.mul_zero, Matrix.trace_zero,
    Complex.zero_re] at hX
  exact (lt_irrefl 0) hX

end Qatlib.Concepts.GibbsSource.SpectralGeom
