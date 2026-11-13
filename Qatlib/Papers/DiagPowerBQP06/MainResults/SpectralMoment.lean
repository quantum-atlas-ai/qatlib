/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Analysis.Matrix.Spectrum
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Tactic

/-!
# Diagonal powers as spectral moments

This module expands a diagonal entry of a power of a real symmetric matrix in an orthonormal
eigenbasis. The squared entries of the eigenvector row are nonnegative and sum to one, giving a
finite probability-weighted spectral moment.

These constructions accompany the results of [JanzingWocjan2006a].

## Main statements

* `hermitian_pow_diagonal_eq`: expands a diagonal power entry as a weighted eigenvalue moment.
* `spectral_moment_probability_form`: packages the moment identity and probability-weight
  conditions.

## References

* [Janzing and Wocjan, 2006][JanzingWocjan2006a]
-/

set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false
noncomputable section

open Matrix

namespace Qatlib.Papers.DiagPowerBQP06.MainResults.SpectralMoment

variable {I : Type*} [Fintype I] [DecidableEq I]

/-- A diagonal entry of a natural power of a real symmetric matrix is the sum of the eigenvalue
powers weighted by squared entries of the corresponding eigenvector row. See
[JanzingWocjan2006a]. -/
theorem hermitian_pow_diagonal_eq
    (A : Matrix I I ℝ) (hA : A.IsHermitian) (m : ℕ) (j : I) :
    (A ^ m) j j = ∑ k, (hA.eigenvectorUnitary j k) ^ 2 * (hA.eigenvalues k) ^ m := by
  classical
  set U : Matrix I I ℝ := (hA.eigenvectorUnitary : Matrix I I ℝ) with hUdef
  set D : Matrix I I ℝ := diagonal (fun k => hA.eigenvalues k) with hDdef
  have hUU : U * star U = 1 := by
    have h := Unitary.mul_star_self_of_mem (hA.eigenvectorUnitary).2
    simpa [hUdef] using h
  have hU'U : star U * U = 1 := by
    have h := Unitary.star_mul_self_of_mem (hA.eigenvectorUnitary).2
    simpa [hUdef] using h
  have hA' : A = U * D * star U := by
    have h := hA.spectral_theorem
    rw [Unitary.conjStarAlgAut_apply] at h
    simpa [hUdef, hDdef] using h

  have hpow : ∀ m : ℕ, A ^ m = U * D ^ m * star U := by
    intro m
    induction m with
    | zero => simp [hUU]
    | succ n ih =>
        rw [pow_succ, ih, hA']
        have hstep : (U * D ^ n * star U) * (U * D * star U) =
            U * (D ^ n * D) * star U := by
          calc (U * D ^ n * star U) * (U * D * star U)
              = U * D ^ n * (star U * U) * D * star U := by noncomm_ring
            _ = U * D ^ n * 1 * D * star U := by rw [hU'U]
            _ = U * (D ^ n * D) * star U := by noncomm_ring
        rw [hstep, ← pow_succ]
  rw [hpow m]

  have hDpow : D ^ m = diagonal (fun a => (hA.eigenvalues a) ^ m) := by
    rw [hDdef]; simpa using! Matrix.diagonal_pow (fun k => hA.eigenvalues k) m

  have hUsj : ∀ a, star U a j = U j a := by
    intro a
    rw [Matrix.star_eq_conjTranspose, Matrix.conjTranspose_apply, star_trivial]

  have hinner : ∀ a, (U * D ^ m) j a = U j a * (hA.eigenvalues a) ^ m := by
    intro a
    rw [Matrix.mul_apply, hDpow]
    calc ∑ b, U j b * (diagonal (fun k => (hA.eigenvalues k) ^ m)) b a
        = U j a * (diagonal (fun k => (hA.eigenvalues k) ^ m)) a a :=
          Finset.sum_eq_single a
            (fun b _ hba => by rw [Matrix.diagonal_apply_ne _ hba, mul_zero])
            (fun ha => absurd (Finset.mem_univ a) ha)
      _ = U j a * (hA.eigenvalues a) ^ m := by rw [Matrix.diagonal_apply_eq]
  rw [Matrix.mul_apply]
  calc ∑ a, (U * D ^ m) j a * star U a j
      = ∑ a, (U j a * (hA.eigenvalues a) ^ m) * U j a := by
          apply Finset.sum_congr rfl; intro a _; rw [hinner a, hUsj a]
    _ = ∑ a, (U j a) ^ 2 * (hA.eigenvalues a) ^ m := by
          apply Finset.sum_congr rfl; intro a _; ring

/-- Each squared entry of a real eigenvector row is nonnegative. -/
theorem eigenvector_row_weights_nonneg
    (A : Matrix I I ℝ) (hA : A.IsHermitian) (j k : I) :
    0 ≤ (hA.eigenvectorUnitary j k) ^ 2 := sq_nonneg _

/-- The squared entries of each row of the orthonormal eigenvector matrix sum to one. -/
theorem eigenvector_row_weights_sum_one
    (A : Matrix I I ℝ) (hA : A.IsHermitian) (j : I) :
    ∑ k, (hA.eigenvectorUnitary j k) ^ 2 = 1 := by
  classical
  set U : Matrix I I ℝ := (hA.eigenvectorUnitary : Matrix I I ℝ) with hUdef
  have hUU : U * star U = 1 := by
    have h := Unitary.mul_star_self_of_mem (hA.eigenvectorUnitary).2
    simpa [hUdef] using h
  have hentry := congrFun (congrFun hUU j) j
  rw [Matrix.mul_apply] at hentry
  have hUsj : ∀ a, star U a j = U j a := by
    intro a
    rw [Matrix.star_eq_conjTranspose, Matrix.conjTranspose_apply, star_trivial]
  simp only [hUsj, Matrix.one_apply_eq] at hentry
  simpa [hUdef, pow_two] using hentry

/-- The diagonal power entry equals the eigenvalue moment with squared eigenvector-row weights,
and these weights are nonnegative and sum to one. See [JanzingWocjan2006a]. -/
theorem spectral_moment_probability_form
    (A : Matrix I I ℝ) (hA : A.IsHermitian) (m : ℕ) (j : I) :
    (A ^ m) j j = ∑ k, (hA.eigenvectorUnitary j k) ^ 2 * (hA.eigenvalues k) ^ m ∧
      (∀ k, 0 ≤ (hA.eigenvectorUnitary j k) ^ 2) ∧
      ∑ k, (hA.eigenvectorUnitary j k) ^ 2 = 1 :=
  ⟨hermitian_pow_diagonal_eq A hA m j,
   fun k => eigenvector_row_weights_nonneg A hA j k,
   eigenvector_row_weights_sum_one A hA j⟩

end Qatlib.Papers.DiagPowerBQP06.MainResults.SpectralMoment
