/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.AdaptiveTest26.MainResults.SourceModel

set_option backward.isDefEq.respectTransparency false

/-!
# Hilbert-Schmidt Decomposition of Spectral Blocks

This module proves Lemma 3.7: in the eigenbasis of an operator `σ = U diag(d) U†`
given by a unitary matrix `U`, the squared Hilbert-Schmidt norm of the spectral block
`Π_S (ρ - σ) Π_R` equals `∑_{i ∈ S} ∑_{j ∈ R} |⟨σ_i|ρ|σ_j⟩ - δ_{ij} d_i|^2`.

## Main statements

* `trace_conjTranspose_mul_re`: `Re tr(A† A) = ∑_{i, j} |A_{ij}|^2`.
* `hsNormSq_eq_sum_normSq`: entrywise sum-of-squares formula for `hsNormSq`.
* `spectral_block_hs_decomposition`: Lemma 3.7 eigenbasis formula for `hsNormSq (Π_S (ρ - σ) Π_R)`.

## References

* [Seyfried et al., 2026][SeyfriedSenTomamichel2026], Lemma 3.7, Eq. (19), p. 12.
-/

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.AdaptiveTest26.MainResults.Preliminaries

open Qatlib.Papers.AdaptiveTest26.MainResults
open Qatlib.Foundations.PureStateMath
open Matrix MeasureTheory
open scoped BigOperators ComplexOrder MatrixOrder ENNReal Matrix.Norms.L2Operator

/-- The real part of `tr(A† A)` equals the sum of the squared moduli of all entries of `A`. -/
lemma trace_conjTranspose_mul_re {D : ℕ} (A : Operator D) :
    (Matrix.trace (A.conjTranspose * A)).re = ∑ i, ∑ j, Complex.normSq (A i j) := by
  rw [Matrix.trace]
  simp only [Matrix.diag_apply, Matrix.mul_apply, Matrix.conjTranspose_apply, Complex.re_sum,
    Complex.mul_re, Complex.star_def, Complex.conj_re, Complex.conj_im, Complex.normSq_apply]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring

/-- Squared Hilbert-Schmidt norm as the sum of the squared moduli of all matrix entries. -/
lemma hsNormSq_eq_sum_normSq {D : ℕ} (A : Operator D) :
    hsNormSq A = ∑ i, ∑ j, Complex.normSq (A i j) := by
  unfold hsNormSq SchattenTwo
  rw [Real.sq_sqrt]
  · exact trace_conjTranspose_mul_re A
  · rw [trace_conjTranspose_mul_re]
    exact Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => Complex.normSq_nonneg _

private lemma hsNormSq_unitary_conj {D : ℕ} (U X : Operator D)
    (hU : U.conjTranspose * U = 1) :
    hsNormSq (U * X * U.conjTranspose) = hsNormSq X := by
  have htrace : Matrix.trace ((U * X * U.conjTranspose).conjTranspose *
      (U * X * U.conjTranspose)) = Matrix.trace (X.conjTranspose * X) := by
    calc
      _ = Matrix.trace (U * (X.conjTranspose * X) * U.conjTranspose) := by
        congr 1
        simp only [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose,
          Matrix.mul_assoc]
        rw [← Matrix.mul_assoc U.conjTranspose U, hU, Matrix.one_mul]
      _ = _ := by rw [Matrix.trace_mul_cycle, hU, Matrix.one_mul]
  unfold hsNormSq SchattenTwo
  rw [htrace]

/-- **Lemma 3.7**: for a unitary `U` diagonalizing `σ = U diag(d) U†` with real eigenvalues `d`
and any operator `ρ`, the squared Hilbert-Schmidt norm of `Π_S (ρ - σ) Π_R` equals
`∑_{i ∈ S} ∑_{j ∈ R} |⟨σ_i|ρ|σ_j⟩ - δ_{ij} d_i|^2`. -/
theorem spectral_block_hs_decomposition {D : ℕ} (U : Operator D)
    (hU : U.conjTranspose * U = 1) (d : Fin D → ℝ) (ρ : Operator D)
    (S R : Finset (Fin D)) :
    hsNormSq (spectralProj U S *
        (ρ - U * Matrix.diagonal (fun i => (d i : ℂ)) * U.conjTranspose) * spectralProj U R)
      = ∑ i ∈ S, ∑ j ∈ R,
          Complex.normSq (eigenEntry U ρ i j - if i = j then (d i : ℂ) else 0) := by
  have hU' : U * U.conjTranspose = 1 := mul_eq_one_comm.mp hU
  let P_S : Operator D := Matrix.diagonal (fun i => if i ∈ S then (1 : ℂ) else 0)
  let P_R : Operator D := Matrix.diagonal (fun j => if j ∈ R then (1 : ℂ) else 0)
  let M : Operator D := U.conjTranspose * ρ * U - Matrix.diagonal (fun i => (d i : ℂ))
  have hρ : ρ - U * Matrix.diagonal (fun i => (d i : ℂ)) * U.conjTranspose =
      U * M * U.conjTranspose := by
    symm
    dsimp [M]
    rw [Matrix.mul_sub, Matrix.sub_mul]
    simp only [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc U U.conjTranspose]
    simp only [hU', Matrix.one_mul, Matrix.mul_one]
  have hblock : spectralProj U S *
      (ρ - U * Matrix.diagonal (fun i => (d i : ℂ)) * U.conjTranspose) * spectralProj U R =
      U * (P_S * M * P_R) * U.conjTranspose := by
    rw [hρ]
    change (U * P_S * U.conjTranspose) * (U * M * U.conjTranspose) *
      (U * P_R * U.conjTranspose) = _
    simp only [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc U.conjTranspose U, hU, Matrix.one_mul,
      ← Matrix.mul_assoc U.conjTranspose U, hU, Matrix.one_mul]
  have hentry (i j : Fin D) : (P_S * M * P_R) i j =
      if i ∈ S then (if j ∈ R then M i j else 0) else 0 := by
    dsimp [P_S, P_R]
    rw [Matrix.mul_diagonal, Matrix.diagonal_mul]
    by_cases hi : i ∈ S <;> by_cases hj : j ∈ R <;> simp [hi, hj]
  rw [hblock, hsNormSq_unitary_conj U _ hU, hsNormSq_eq_sum_normSq]
  rw [← Finset.sum_subset (Finset.subset_univ S)]
  · refine Finset.sum_congr rfl fun i hi => ?_
    rw [← Finset.sum_subset (Finset.subset_univ R)]
    · refine Finset.sum_congr rfl fun j hj => ?_
      simp only [hentry, hi, hj, ite_true]
      simp [M, Matrix.sub_apply, Matrix.diagonal_apply, eigenEntry]
    · intro j _ hj
      simp [hentry, hj]
  · intro i _ hi
    simp [hentry, hi]

end Qatlib.Papers.AdaptiveTest26.MainResults.Preliminaries
