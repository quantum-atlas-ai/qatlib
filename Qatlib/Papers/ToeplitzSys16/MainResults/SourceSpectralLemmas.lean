/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.ToeplitzSys16.MainResults.ToeplitzCirculantModel
import Mathlib.Analysis.Complex.Polynomial.Basic

set_option backward.isDefEq.respectTransparency false

/-!
# Frobenius-Spectral Identities, Schur's Inequality, and Normality Characterization

This module formalizes Appendix A (Lemmas 1 and 2, Equations (A1)--(A2)) of Wan, Yu,
Pan, Gao, and Wen for `n × n` complex matrices, relating the Frobenius norm to trace
and singular values and establishing Schur's eigenvalue inequality
`∑ |λ_k(A)|^2 ≤ ∑ λ_k(A† A)` together with equality if and only if `A` is normal
(`A A† = A† A`).

## Main statements

* `lemma1_frobenius_entrywise`, `lemma1_frobenius_trace`, `lemma1_frobenius_singular`: Lemma 1, Eq. (A1).
* `lemma2_eigenvalue_inequality`: Lemma 2, Eq. (A2), Schur's inequality `∑ |λ_k(A)|^2 ≤ ∑ λ_k(A† A)`.
* `lemma2_equality_iff_normal`: Lemma 2, Eq. (A2), equality holds if and only if `A * Aᴴ = Aᴴ * A`.

## References

* [Wan et al., 2018][WanEtAl2016Toeplitz], Appendix A, Lemmas 1 and 2, p. 7.
-/

set_option autoImplicit false
noncomputable section

open Matrix Real
open scoped Classical BigOperators

namespace Qatlib.Papers.ToeplitzSys16.MainResults

open Qatlib.Concepts.SpectralSketch.SpectrumPerturb
open Qatlib.Concepts.RandCompile.ChannelBudget

/- ## Lemma 1, eq. (A1): three equal forms of the Frobenius norm -/

/-- Lemma 1, first equality of (A1) (p.7): `‖A‖_F = (∑ₖ∑ⱼ |a_{kj}|²)^{1/2}`.
The right-hand side is literally the definition of `spectralFrobenius`. -/
theorem lemma1_frobenius_entrywise (n : ℕ) (A : Matrix (Fin n) (Fin n) ℂ) :
    spectralFrobenius A = Real.sqrt (∑ k : Fin n, ∑ j : Fin n, Complex.normSq (A k j)) :=
  rfl

/-- Lemma 1, trace equality of (A1) (p.7): `‖A‖_F = [tr(A* A)]^{1/2}`.
Bridged from `spectralFrobenius_sq_trace`
(`Qatlib.Concepts.SpectralSketch.SpectrumPerturb.spectralFrobenius_sq_trace`). -/
theorem lemma1_frobenius_trace (n : ℕ) (A : Matrix (Fin n) (Fin n) ℂ) :
    spectralFrobenius A = Real.sqrt ((Matrix.trace (Aᴴ * A)).re) := by
  rw [← spectralFrobenius_sq_trace]
  exact (Real.sqrt_sq (spectralFrobenius_nonneg A)).symm

/-- Lemma 1, spectral equality of (A1) (p.7): `‖A‖_F = [∑ₖ λₖ(A* A)]^{1/2}`, the `λₖ(A* A)`
realised as the squared singular values of `A`.  Bridged from
`spectralFrobenius_sq_singular`
(`Qatlib.Concepts.SpectralSketch.SpectrumPerturb.spectralFrobenius_sq_singular`). -/
theorem lemma1_frobenius_singular (n : ℕ) (A : Matrix (Fin n) (Fin n) ℂ) :
    spectralFrobenius A
      = Real.sqrt (∑ i : Fin (Fintype.card (Fin n)),
          (matrixSingularValues A (i : ℕ)) ^ 2) := by
  rw [show (∑ i : Fin (Fintype.card (Fin n)), (matrixSingularValues A (i : ℕ)) ^ 2)
        = spectralFrobenius A ^ 2 from (spectralFrobenius_sq_singular A).symm]
  exact (Real.sqrt_sq (spectralFrobenius_nonneg A)).symm

/- ## Lemma 2, eq. (A2): Schur inequality -/

open Qatlib.Concepts.WalkSearch.Spectral

private def frobSq {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ) : ℝ :=
  ∑ i, ∑ j, Complex.normSq (A i j)

private lemma frobSq_eq_sq {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ) :
    frobSq A = spectralFrobenius A ^ 2 := (spectralFrobenius_sq A).symm

private lemma gram_sum_eq_frobSq {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ) :
    (∑ i : Fin n, (Matrix.isHermitian_conjTranspose_mul_self A).eigenvalues i) =
      frobSq A := by
  rw [frobSq_eq_sq, spectralFrobenius_sq_trace,
    (Matrix.isHermitian_conjTranspose_mul_self A).trace_eq_sum_eigenvalues]
  simp only [Complex.re_sum, RCLike.ofReal_eq_complex_ofReal, Complex.ofReal_re]

private lemma unitary_deflation (m : ℕ) (A : Matrix (Fin (m + 1)) (Fin (m + 1)) ℂ) :
    ∃ (μ : ℂ) (U : Matrix (Fin (m + 1)) (Fin (m + 1)) ℂ),
      Uᴴ * U = 1 ∧ U * Uᴴ = 1 ∧
      (Uᴴ * A * U) 0 0 = μ ∧ ∀ i : Fin m, (Uᴴ * A * U) i.succ 0 = 0 := by
  obtain ⟨μ, hμ⟩ := IsAlgClosed.exists_root A.charpoly (by
    rw [Polynomial.degree_eq_natDegree A.charpoly_monic.ne_zero,
      Matrix.charpoly_natDegree_eq_dim, Fintype.card_fin]
    exact_mod_cast Nat.succ_ne_zero m)
  have hdet : (Matrix.scalar (Fin (m + 1)) μ - A).det = 0 := by
    rw [← Matrix.eval_charpoly]
    exact hμ
  obtain ⟨v, hv, hAv⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr hdet
  have heigen : A *ᵥ v = μ • v := by
    have h : μ • v - A *ᵥ v = 0 := by
      funext j
      simpa only [Pi.sub_apply, Matrix.sub_mulVec, Matrix.scalar_apply,
        Matrix.mulVec_diagonal, Pi.smul_apply, smul_eq_mul, Pi.zero_apply] using congrFun hAv j
    exact (sub_eq_zero.mp h).symm
  let x : EuclideanSpace ℂ (Fin (m + 1)) := WithLp.toLp 2 v
  have hx : x ≠ 0 := by simpa only [x, ne_eq, WithLp.toLp_eq_zero] using hv
  have hxA : A.toEuclideanLin x = μ • x := by
    apply WithLp.ofLp_injective
    exact heigen
  let u : EuclideanSpace ℂ (Fin (m + 1)) := (‖x‖⁻¹ : ℂ) • x
  have hu : ‖u‖ = 1 := by
    simp only [u, norm_smul, norm_inv, Complex.norm_real, norm_norm,
      inv_mul_cancel₀ (norm_ne_zero_iff.mpr hx)]
  have huA : A.toEuclideanLin u = μ • u := by
    simp only [u, map_smul, hxA, smul_smul, mul_comm]
  have hon : Orthonormal ℂ
      (({0} : Set (Fin (m + 1))).domRestrict (fun _ => u)) :=
    orthonormal_subsingleton_iff.mpr (fun _ => hu)
  obtain ⟨b, hb⟩ := hon.exists_orthonormalBasis_extension_of_card_eq (by simp)
  have hb0 : b 0 = u := hb 0 (Set.mem_singleton 0)
  let U := basisColumns b
  have hcol (i : Fin (m + 1)) : (A * U) i 0 = μ * U i 0 := by
    have h := congrArg (fun y : EuclideanSpace ℂ (Fin (m + 1)) => y i) huA
    simpa only [← hb0, Matrix.toLpLin_apply, LinearMap.coe_mk, AddHom.coe_mk,
      WithLp.ofLp_toLp, WithLp.ofLp_smul, Pi.smul_apply, smul_eq_mul, U, Matrix.mul_apply,
      basisColumns_apply, Matrix.mulVec, dotProduct] using h
  have hentry (r : Fin (m + 1)) : (Uᴴ * A * U) r 0 = μ * (Uᴴ * U) r 0 := by
    rw [Matrix.mul_assoc, Matrix.mul_apply, Matrix.mul_apply, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    rw [hcol]
    ring
  have hU : Uᴴ * U = 1 := basisColumns_adjoint_mul b
  refine ⟨μ, U, hU, basisColumns_mul_adjoint b, ?_, ?_⟩
  · rw [hentry, hU, Matrix.one_apply_eq, mul_one]
  · intro i
    rw [hentry, hU, Matrix.one_apply_ne (Fin.succ_ne_zero i), mul_zero]

private lemma conjugate_charpoly {n : ℕ} (A U : Matrix (Fin n) (Fin n) ℂ)
    (hU : U * Uᴴ = 1) : (Uᴴ * A * U).charpoly = A.charpoly := by
  rw [Matrix.charpoly_mul_comm, ← Matrix.mul_assoc, hU, Matrix.one_mul]

private lemma conjugate_frobSq {n : ℕ} (A U : Matrix (Fin n) (Fin n) ℂ)
    (hU : U * Uᴴ = 1) : frobSq (Uᴴ * A * U) = frobSq A := by
  rw [frobSq_eq_sq, frobSq_eq_sq, spectralFrobenius_right _ _ hU,
    spectralFrobenius_left _ _ (by simpa only [Matrix.conjTranspose_conjTranspose] using hU)]

private lemma conjugate_normal {n : ℕ} (A U : Matrix (Fin n) (Fin n) ℂ)
    (hU' : U * Uᴴ = 1) :
    (Uᴴ * A * U) * (Uᴴ * A * U)ᴴ = (Uᴴ * A * U)ᴴ * (Uᴴ * A * U) ↔
      A * Aᴴ = Aᴴ * A := by
  have hprod (B C : Matrix (Fin n) (Fin n) ℂ) :
      (Uᴴ * B * U) * (Uᴴ * C * U) = Uᴴ * (B * C) * U := by
    simp only [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc U Uᴴ, hU', Matrix.one_mul]
  have hinv (B : Matrix (Fin n) (Fin n) ℂ) : U * (Uᴴ * B * U) * Uᴴ = B := by
    simp only [← Matrix.mul_assoc]
    rw [hU', Matrix.one_mul, Matrix.mul_assoc, hU', Matrix.mul_one]
  have hadj : (Uᴴ * A * U)ᴴ = Uᴴ * Aᴴ * U := by
    simp only [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, Matrix.mul_assoc]
  rw [hadj, hprod, hprod]
  constructor
  · intro h
    have h' := congrArg (fun B => U * B * Uᴴ) h
    simpa only [hinv] using h'
  · intro h
    exact congrArg (fun B => Uᴴ * B * U) h

private lemma deflated_charpoly {m : ℕ} (T : Matrix (Fin (m + 1)) (Fin (m + 1)) ℂ)
    (hcol : ∀ i : Fin m, T i.succ 0 = 0) :
    T.charpoly = (Polynomial.X - Polynomial.C (T 0 0)) *
      (T.submatrix Fin.succ Fin.succ).charpoly := by
  have hminor : T.charmatrix.submatrix (0 : Fin (m + 1)).succAbove Fin.succ =
      (T.submatrix Fin.succ Fin.succ).charmatrix := by
    ext i j : 2
    simp only [Matrix.submatrix_apply, Fin.succAbove_zero]
    by_cases hij : i = j
    · subst j
      simp only [Matrix.charmatrix_apply_eq, Matrix.submatrix_apply]
    · rw [Matrix.charmatrix_apply_ne _ _ _ (fun h => hij (Fin.succ_inj.mp h)),
        Matrix.charmatrix_apply_ne _ _ _ hij, Matrix.submatrix_apply]
  rw [Matrix.charpoly, Matrix.det_succ_column_zero, Fin.sum_univ_succ, hminor]
  simp only [Fin.val_zero, pow_zero, one_mul, Matrix.charmatrix_apply_eq,
    Matrix.charmatrix_apply_ne _ _ _ (Fin.succ_ne_zero _), hcol,
    Polynomial.C_0, neg_zero, mul_zero, zero_mul, Finset.sum_const_zero, add_zero]
  rfl

private lemma deflated_roots {m : ℕ} (T : Matrix (Fin (m + 1)) (Fin (m + 1)) ℂ)
    (hcol : ∀ i : Fin m, T i.succ 0 = 0) :
    (T.charpoly.roots.map Complex.normSq).sum = Complex.normSq (T 0 0) +
      ((T.submatrix Fin.succ Fin.succ).charpoly.roots.map Complex.normSq).sum := by
  rw [deflated_charpoly T hcol,
    Polynomial.roots_mul (mul_ne_zero (Polynomial.X_sub_C_ne_zero _)
      (Matrix.charpoly_monic _).ne_zero), Polynomial.roots_X_sub_C]
  simp only [Multiset.map_add, Multiset.map_singleton, Multiset.sum_add,
    Multiset.sum_singleton]

private lemma deflated_frobSq {m : ℕ} (T : Matrix (Fin (m + 1)) (Fin (m + 1)) ℂ)
    (hcol : ∀ i : Fin m, T i.succ 0 = 0) :
    frobSq T = Complex.normSq (T 0 0) + (∑ j : Fin m, Complex.normSq (T 0 j.succ)) +
      frobSq (T.submatrix Fin.succ Fin.succ) := by
  simp only [frobSq, Fin.sum_univ_succ, hcol, Complex.normSq_zero, zero_add,
    Matrix.submatrix_apply]

private lemma normal_deflated_row {m : ℕ}
    (T : Matrix (Fin (m + 1)) (Fin (m + 1)) ℂ)
    (hcol : ∀ i : Fin m, T i.succ 0 = 0) (hT : T * Tᴴ = Tᴴ * T) :
    (∑ j : Fin m, Complex.normSq (T 0 j.succ)) = 0 := by
  have h : (∑ j, Complex.normSq (T 0 j)) = ∑ j, Complex.normSq (T j 0) := by
    apply Complex.ofReal_injective
    simp only [Complex.ofReal_sum, Complex.normSq_eq_conj_mul_self]
    simpa only [Matrix.mul_apply, Matrix.conjTranspose_apply, Complex.star_def, mul_comm]
      using congrArg (fun M : Matrix (Fin (m + 1)) (Fin (m + 1)) ℂ => M 0 0) hT
  simpa only [Fin.sum_univ_succ, hcol, Complex.normSq_zero, Finset.sum_const_zero,
    add_zero, add_eq_left] using h

private lemma zero_row_of_sum {m : ℕ}
    (T : Matrix (Fin (m + 1)) (Fin (m + 1)) ℂ)
    (h : (∑ j : Fin m, Complex.normSq (T 0 j.succ)) = 0) :
    ∀ j : Fin m, T 0 j.succ = 0 := by
  intro j
  exact Complex.normSq_eq_zero.mp
    ((Finset.sum_eq_zero_iff_of_nonneg (fun i _ => Complex.normSq_nonneg (T 0 i.succ))).mp
      h j (Finset.mem_univ _))

private lemma block_normal_iff {m : ℕ}
    (T : Matrix (Fin (m + 1)) (Fin (m + 1)) ℂ)
    (hcol : ∀ i : Fin m, T i.succ 0 = 0) (hrow : ∀ j : Fin m, T 0 j.succ = 0) :
    T * Tᴴ = Tᴴ * T ↔
      (T.submatrix Fin.succ Fin.succ) * (T.submatrix Fin.succ Fin.succ)ᴴ =
        (T.submatrix Fin.succ Fin.succ)ᴴ * (T.submatrix Fin.succ Fin.succ) := by
  constructor
  · intro h
    ext i j
    simpa only [Matrix.mul_apply, Matrix.conjTranspose_apply, Fin.sum_univ_succ,
      hcol, hrow, star_zero, zero_mul, mul_zero, zero_add, Matrix.submatrix_apply]
      using congrArg (fun M : Matrix (Fin (m + 1)) (Fin (m + 1)) ℂ => M i.succ j.succ) h
  · intro h
    ext i j
    refine Fin.cases ?_ (fun i => ?_) i
    · refine Fin.cases ?_ (fun j => ?_) j
      · simp [Matrix.mul_apply, Matrix.conjTranspose_apply, Fin.sum_univ_succ, hcol, hrow,
          mul_comm]
      · simp [Matrix.mul_apply, Matrix.conjTranspose_apply, Fin.sum_univ_succ, hcol, hrow]
    · refine Fin.cases ?_ (fun j => ?_) j
      · simp [Matrix.mul_apply, Matrix.conjTranspose_apply, Fin.sum_univ_succ, hcol, hrow]
      · simpa only [Matrix.mul_apply, Matrix.conjTranspose_apply, Fin.sum_univ_succ,
          hcol, hrow, star_zero, zero_mul, mul_zero, zero_add, Matrix.submatrix_apply]
          using congrArg (fun M : Matrix (Fin m) (Fin m) ℂ => M i j) h

private lemma schur_induction (n : ℕ) (A : Matrix (Fin n) (Fin n) ℂ) :
    (A.charpoly.roots.map Complex.normSq).sum ≤ frobSq A ∧
      (frobSq A = (A.charpoly.roots.map Complex.normSq).sum ↔ A * Aᴴ = Aᴴ * A) := by
  induction n with
  | zero =>
      simp only [Matrix.charpoly_isEmpty, Polynomial.roots_one, Multiset.empty_eq_zero,
        Multiset.map_zero, Multiset.sum_zero, frobSq, Fin.sum_univ_zero, le_refl, true_and,
        true_iff]
      ext i
      exact i.elim0
  | succ m ih =>
      obtain ⟨_, U, _, hU, _, hcol⟩ := unitary_deflation m A
      let T := Uᴴ * A * U
      let B := T.submatrix Fin.succ Fin.succ
      have hchar : T.charpoly = A.charpoly := conjugate_charpoly A U hU
      have hfrob : frobSq T = frobSq A := conjugate_frobSq A U hU
      have hnormal : T * Tᴴ = Tᴴ * T ↔ A * Aᴴ = Aᴴ * A := conjugate_normal A U hU
      have hroots := deflated_roots T hcol
      have hsplit := deflated_frobSq T hcol
      have hnonneg : 0 ≤ ∑ j : Fin m, Complex.normSq (T 0 j.succ) :=
        Finset.sum_nonneg (fun j _ => Complex.normSq_nonneg _)
      obtain ⟨hB, hBeq⟩ := ih B
      rw [← hchar, ← hfrob, ← hnormal]
      constructor
      · rw [hroots, hsplit]
        linarith
      · constructor
        · intro heq
          have hsum : (∑ j : Fin m, Complex.normSq (T 0 j.succ)) = 0 := by
            rw [hsplit, hroots] at heq
            linarith
          have hrow := zero_row_of_sum T hsum
          apply (block_normal_iff T hcol hrow).mpr
          apply hBeq.mp
          rw [hsplit, hroots, hsum] at heq
          linarith
        · intro hT
          have hsum := normal_deflated_row T hcol hT
          have hrow := zero_row_of_sum T hsum
          have hBnormal := (block_normal_iff T hcol hrow).mp hT
          rw [hsplit, hroots, hsum, hBeq.mpr hBnormal, add_zero]

/-- Lemma 2, inequality (A2) (p.7): `∑ₖ λₖ(A* A) ≥ ∑ₖ λₖ²`, i.e. the sum of the eigenvalues of the
Hermitian Gram matrix `Aᴴ A` dominates the sum of the squared moduli of the eigenvalues of `A`
(Schur's inequality `∑ σₖ² ≥ ∑ |λₖ|²`).

The elementary induction extends a unit eigenvector to an orthonormal basis and deflates its
first column. The remaining first-row squared norms give the nonnegative defect at each step. -/
theorem lemma2_eigenvalue_inequality (n : ℕ) (A : Matrix (Fin n) (Fin n) ℂ) :
    ((A.charpoly).roots.map (fun z => Complex.normSq z)).sum
      ≤ ∑ i : Fin n, (Matrix.isHermitian_conjTranspose_mul_self A).eigenvalues i := by
  rw [gram_sum_eq_frobSq]
  exact (schur_induction n A).1

/-- Lemma 2, equality case of (A2) (p.7): equality in Schur's inequality holds **iff** `A` is
normal (`A Aᴴ = Aᴴ A`).

In the same induction, equality forces the deflated first row to vanish. Conversely, the `(0, 0)`
entry of normality forces that row to vanish, reducing both conditions to the smaller block. -/
theorem lemma2_equality_iff_normal (n : ℕ) (A : Matrix (Fin n) (Fin n) ℂ) :
    ((∑ i : Fin n, (Matrix.isHermitian_conjTranspose_mul_self A).eigenvalues i)
        = ((A.charpoly).roots.map (fun z => Complex.normSq z)).sum)
      ↔ A * Aᴴ = Aᴴ * A := by
  rw [gram_sum_eq_frobSq]
  exact (schur_induction n A).2

end Qatlib.Papers.ToeplitzSys16.MainResults
