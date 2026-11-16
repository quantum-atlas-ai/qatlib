/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Papers.AdaptiveTest26.MainResults.SourceModel

@[expose] public section


set_option backward.isDefEq.respectTransparency false

/-!
# Lemma 3.7 — Hilbert–Schmidt decomposition of spectral blocks

Fixed source: arXiv:2609.08733v1, Lemma 3.7, p.12, eq. (19).

In the eigenbasis `{|σ_i⟩}` of a state `σ = U diag(σ_i) U†`, the squared Hilbert–Schmidt norm of a
spectral block `Π_S(ρ − σ)Π_R` equals `Σ_{i∈S, j∈R} |⟨σ_i|ρ|σ_j⟩ − δ_ij σ_i|^2`.
-/

namespace Qatlib.Papers.AdaptiveTest26.MainResults.Preliminaries
open Qatlib.Papers.AdaptiveTest26.MainResults

open Qatlib.Papers.AdaptiveTest26.MainResults Qatlib.Papers.AdaptiveTest26.MainResults Qatlib.Papers.AdaptiveTest26.MainResults
open Qatlib.Papers.AdaptiveTest26.MainResults
open Qatlib.Foundations.PureStateMath
open Matrix MeasureTheory
open scoped BigOperators ComplexOrder MatrixOrder ENNReal Matrix.Norms.L2Operator

set_option autoImplicit false
noncomputable section


/-
/-- The real part of `tr(A†A)` is the sum of the squared moduli of all entries
(Definition 3.2(ii), p.12). -/
lemma trace_conjTranspose_mul_re {D : ℕ} (A : Operator D) :
    (Matrix.trace (A.conjTranspose * A)).re = ∑ i, ∑ j, Complex.normSq (A i j) := by
  rw [Matrix.trace]
  simp only [Matrix.diag_apply, Matrix.mul_apply, Matrix.conjTranspose_apply, Complex.re_sum,
    Complex.mul_re, Complex.star_def, Complex.conj_re, Complex.conj_im, Complex.normSq_apply]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring

/-- Squared Hilbert–Schmidt norm as the sum of the squared moduli of the entries. -/
lemma hsNormSq_eq_sum_normSq {D : ℕ} (A : Operator D) :
    hsNormSq A = ∑ i, ∑ j, Complex.normSq (A i j) := by
  unfold hsNormSq SchattenTwo
  rw [Real.sq_sqrt]
  · exact trace_conjTranspose_mul_re A
  · -- `tr(A†A)` is a sum of real squares, hence nonnegative.
    rw [trace_conjTranspose_mul_re]
    exact Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => Complex.normSq_nonneg _
 -/

/-- Unitary conjugation preserves the squared Hilbert--Schmidt norm. -/
lemma hsNormSq_unitary_conj {D : ℕ} (U A : Operator D)
    (hU : U.conjTranspose * U = 1) :
    hsNormSq (U * A * U.conjTranspose) = hsNormSq A := by
  have htrace : Matrix.trace
      ((U * A * U.conjTranspose).conjTranspose * (U * A * U.conjTranspose)) =
      Matrix.trace (A.conjTranspose * A) := by
    simp only [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose]
    calc
      Matrix.trace ((U * (A.conjTranspose * U.conjTranspose)) *
          (U * A * U.conjTranspose)) =
          Matrix.trace (U * (A.conjTranspose * A) * U.conjTranspose) := by
        congr 1
        simp only [Matrix.mul_assoc]
        rw [← Matrix.mul_assoc U.conjTranspose U, hU, Matrix.one_mul]
      _ = Matrix.trace (A.conjTranspose * A) := by
        rw [Matrix.trace_mul_cycle, hU, Matrix.one_mul]
  unfold hsNormSq SchattenTwo
  rw [htrace]

/-
/-- **Lemma 3.7** (arXiv:2609.08733v1, p.12, eq. (19)): for a unitary `U` diagonalizing `σ` as
`σ = U diag(σ_i) U†` with real eigenvalues `σ_i`, and any `ρ`,
`‖Π_S(ρ − σ)Π_R‖_2^2 = Σ_{i∈S} Σ_{j∈R} |⟨σ_i|ρ|σ_j⟩ − δ_ij σ_i|^2`. -/
theorem spectral_block_hs_decomposition {D : ℕ} (U : Operator D)
    (hU : U.conjTranspose * U = 1) (d : Fin D → ℝ) (ρ : Operator D)
    (S R : Finset (Fin D)) :
    hsNormSq (spectralProj U S *
        (ρ - U * Matrix.diagonal (fun i => (d i : ℂ)) * U.conjTranspose) * spectralProj U R)
      = ∑ i ∈ S, ∑ j ∈ R,
          Complex.normSq (eigenEntry U ρ i j - if i = j then (d i : ℂ) else 0) := by
  classical
  have hU' : U * U.conjTranspose = 1 := mul_eq_one_comm.mp hU
  let X := U.conjTranspose * ρ * U - Matrix.diagonal (fun i => (d i : ℂ))
  have hrho : U * (U.conjTranspose * ρ * U) * U.conjTranspose = ρ := by
    calc
      _ = (U * U.conjTranspose) * ρ * (U * U.conjTranspose) := by
        simp only [Matrix.mul_assoc]
      _ = ρ := by rw [hU', Matrix.one_mul, Matrix.mul_one]
  have hx : ρ - U * Matrix.diagonal (fun i => (d i : ℂ)) * U.conjTranspose =
      U * X * U.conjTranspose := by
    dsimp [X]
    rw [Matrix.mul_sub, Matrix.sub_mul, hrho]
  rw [hx]
  have hblock : spectralProj U S * (U * X * U.conjTranspose) * spectralProj U R =
      U * (Matrix.diagonal (fun i => if i ∈ S then (1 : ℂ) else 0) * X *
        Matrix.diagonal (fun i => if i ∈ R then (1 : ℂ) else 0)) * U.conjTranspose := by
    unfold spectralProj
    simp only [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc U.conjTranspose U, hU, Matrix.one_mul,
      ← Matrix.mul_assoc U.conjTranspose U, hU, Matrix.one_mul]
  rw [hblock, hsNormSq_unitary_conj U _ hU, hsNormSq_eq_sum_normSq]
  have hentry (i j : Fin D) :
      Complex.normSq ((Matrix.diagonal (fun a => if a ∈ S then (1 : ℂ) else 0) *
        X * Matrix.diagonal (fun a => if a ∈ R then (1 : ℂ) else 0)) i j) =
        if i ∈ S then if j ∈ R then
          Complex.normSq (eigenEntry U ρ i j - if i = j then (d i : ℂ) else 0)
        else 0 else 0 := by
    by_cases hi : i ∈ S <;> by_cases hj : j ∈ R <;>
      simp [Matrix.diagonal_mul, Matrix.mul_diagonal, hi, hj, X, eigenEntry,
        Matrix.diagonal_apply]
  simp_rw [hentry]
  simp only [Finset.sum_ite_irrel, Finset.sum_const_zero]
  simp only [← Finset.sum_filter, Finset.filter_mem_eq_inter, Finset.univ_inter]
 -/

end

end Qatlib.Papers.AdaptiveTest26.MainResults.Preliminaries
