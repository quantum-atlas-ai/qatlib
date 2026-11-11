/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Analysis.InnerProductSpace.PiL2
import Qatlib.Papers.FreeFermion24.MainResults.SourceModel

set_option backward.isDefEq.respectTransparency false

/-!
# Prop5SpectralNorm — Proposition 5 (Gershgorin / spectral-norm bound)

Fixed arXiv:2409.04550, main text p. 6:

> **Proposition 5.** Let `h` denote an `s = O(1)`-sparse Hermitian `N × N` matrix with
> `|h_{ij}| ≤ 1` for all `i,j`.  The spectral norm `‖h‖/s ≤ 1` by the Gershgorin circle
> lemma (every eigenvalue of `h` lies within at least one of the `N` discs
> `D_i = {z ∈ ℂ : |z − h_{ii}| ≤ ∑_{j≠i}|h_{ij}|}`).

The proof below follows the paper's route: a `Gershgorin`-type row-sum bound gives
`‖h‖ ≤ s`.  We prove it directly through the Rayleigh quotient, which is the
operator-norm form of the same eigenvalue bound: every Rayleigh quotient is bounded
by the row and column sums of entry moduli, hence by `s`.

No sorry, no extra hypothesis beyond the paper's `s`-sparsity (row support ≤ `s`) and
entry bound `|h_{ij}| ≤ 1`.
-/

set_option autoImplicit false
noncomputable section

open Matrix
open scoped Matrix.Norms.L2Operator BigOperators

open Qatlib.Papers.FreeFermion24.MainResults.Model

namespace Qatlib.Papers.FreeFermion24.MainResults.Prop5SpectralNorm

/-- Row-sum bound: an `s`-sparse row with entries of modulus at most one has
`ℓ¹` row sum at most `s`.  This is the Gershgorin radius in finite form. -/
theorem row_sum_le {N s : ℕ} {A : Matrix (Fin N) (Fin N) ℂ}
    (hsupp : ∀ i, rowSupport A i ≤ s) (hentry : ∀ i j, ‖A i j‖ ≤ 1) (i : Fin N) :
    ∑ j, ‖A i j‖ ≤ (s : ℝ) := by
  have h1 : ∑ j, ‖A i j‖ ≤ ∑ j, (if A i j = 0 then (0 : ℝ) else 1) := by
    apply Finset.sum_le_sum
    intro j _
    by_cases hj : A i j = 0
    · simp [hj]
    · simp [hj]
      exact hentry i j
  have h2 : ∑ j, (if A i j = 0 then (0 : ℝ) else 1) = (rowSupport A i : ℝ) := by
    have hcongr : ∀ j, (if A i j = 0 then (0 : ℝ) else 1) =
        (if A i j ≠ 0 then (1 : ℝ) else 0) := by
      intro j
      by_cases hj : A i j = 0 <;> simp [hj]
    simp only [hcongr]
    rw [rowSupport]
    simpa using (Finset.sum_boole (fun j : Fin N => A i j ≠ 0) (Finset.univ))
  have h3 : (rowSupport A i : ℝ) ≤ (s : ℝ) := by exact_mod_cast hsupp i
  exact h1.trans (h2.trans_le h3)

/-- Column-sum bound, derived from row sparsity plus Hermitian symmetry. -/
theorem col_sum_le {N s : ℕ} {A : Matrix (Fin N) (Fin N) ℂ}
    (hherm : A.IsHermitian) (hrow : ∀ i, ∑ j, ‖A i j‖ ≤ (s : ℝ)) (j : Fin N) :
    ∑ i, ‖A i j‖ ≤ (s : ℝ) := by
  have hentries : ∀ i, ‖A i j‖ = ‖A j i‖ := by
    intro i
    have hh := congrFun (congrFun hherm i) j
    rw [Matrix.conjTranspose_apply] at hh
    calc ‖A i j‖ = ‖star (A j i)‖ := by rw [hh]
      _ = ‖A j i‖ := norm_star _
  calc ∑ i, ‖A i j‖ = ∑ i, ‖A j i‖ := by
        apply Finset.sum_congr rfl
        intro i _
        exact hentries i
    _ ≤ (s : ℝ) := hrow j

/-- The core quadratic-form bound: for any complex vector `x`, the real part of
`∑ᵢ conj(xᵢ)(A x)ᵢ` is bounded by `s · ‖x‖²`.  This is the content of the
Gershgorin circle estimate in quadratic form. -/
theorem re_dotProduct_mulVec_le {N : ℕ} (A : Matrix (Fin N) (Fin N) ℂ) {s : ℝ}
    (hrow : ∀ i, ∑ j, ‖A i j‖ ≤ s) (hcol : ∀ j, ∑ i, ‖A i j‖ ≤ s)
    (x : Fin N → ℂ) :
    |(∑ i, star (x i) * (A *ᵥ x) i).re| ≤ s * ∑ i, ‖x i‖ ^ 2 := by
  classical
  -- Expand the real part as a double sum.
  have hre : (∑ i, star (x i) * (A *ᵥ x) i).re =
      ∑ i, ∑ j, (star (x i) * A i j * x j).re := by
    simp only [Matrix.mulVec, dotProduct, Finset.mul_sum, Complex.re_sum]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    ring_nf
  rw [hre]
  -- Termwise absolute-value bound.
  have hstep1 : |∑ i, ∑ j, (star (x i) * A i j * x j).re| ≤
      ∑ i, ∑ j, ‖A i j‖ * ‖x i‖ * ‖x j‖ := by
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    apply Finset.sum_le_sum
    intro i _
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    apply Finset.sum_le_sum
    intro j _
    calc |(star (x i) * A i j * x j).re| ≤ ‖star (x i) * A i j * x j‖ :=
          Complex.abs_re_le_norm _
      _ = ‖A i j‖ * ‖x i‖ * ‖x j‖ := by
          rw [norm_mul, norm_mul, norm_star]
          ring
  -- Pairwise `2ab ≤ a² + b²` and the row/column sum hypotheses.
  have hstep2 : ∑ i, ∑ j, ‖A i j‖ * ‖x i‖ * ‖x j‖ ≤ s * ∑ i, ‖x i‖ ^ 2 := by
    set a : Fin N → ℝ := fun i => ‖x i‖ with ha
    have hpair : ∀ i j, ‖A i j‖ * a i * a j ≤
        ‖A i j‖ * a i ^ 2 / 2 + ‖A i j‖ * a j ^ 2 / 2 := by
      intro i j
      have h2ab : 2 * (a i * a j) ≤ a i ^ 2 + a j ^ 2 := by
        nlinarith [sq_nonneg (a i - a j)]
      have hc : 0 ≤ ‖A i j‖ := norm_nonneg _
      nlinarith [mul_le_mul_of_nonneg_left h2ab hc]
    have hle : ∑ i, ∑ j, ‖A i j‖ * a i * a j ≤
        ∑ i, ∑ j, (‖A i j‖ * a i ^ 2 / 2 + ‖A i j‖ * a j ^ 2 / 2) := by
      apply Finset.sum_le_sum
      intro i _
      apply Finset.sum_le_sum
      intro j _
      exact hpair i j
    have hsplit : ∑ i, ∑ j, (‖A i j‖ * a i ^ 2 / 2 + ‖A i j‖ * a j ^ 2 / 2) =
        (∑ i, a i ^ 2 / 2 * (∑ j, ‖A i j‖)) +
          (∑ j, a j ^ 2 / 2 * (∑ i, ‖A i j‖)) := by
      simp only [Finset.sum_add_distrib]
      congr 1
      · apply Finset.sum_congr rfl
        intro i _
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro j _
        ring
      · rw [Finset.sum_comm]
        apply Finset.sum_congr rfl
        intro j _
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro i _
        ring
    have hfirst : ∑ i, a i ^ 2 / 2 * (∑ j, ‖A i j‖) ≤ ∑ i, a i ^ 2 / 2 * s := by
      apply Finset.sum_le_sum
      intro i _
      exact mul_le_mul_of_nonneg_left (hrow i) (by positivity)
    have hsecond : ∑ j, a j ^ 2 / 2 * (∑ i, ‖A i j‖) ≤ ∑ j, a j ^ 2 / 2 * s := by
      apply Finset.sum_le_sum
      intro j _
      exact mul_le_mul_of_nonneg_left (hcol j) (by positivity)
    have hsum : (∑ i, a i ^ 2 / 2 * s) + (∑ j, a j ^ 2 / 2 * s) = s * ∑ i, a i ^ 2 := by
      simp only [← Finset.sum_mul]
      have htot : (∑ i, a i ^ 2 / 2) + (∑ j, a j ^ 2 / 2) = ∑ i, a i ^ 2 := by
        simp only [← Finset.sum_add_distrib]
        apply Finset.sum_congr rfl
        intro i _
        ring
      rw [← add_mul, htot]
      ring
    calc ∑ i, ∑ j, ‖A i j‖ * a i * a j
        ≤ ∑ i, ∑ j, (‖A i j‖ * a i ^ 2 / 2 + ‖A i j‖ * a j ^ 2 / 2) := hle
      _ = (∑ i, a i ^ 2 / 2 * (∑ j, ‖A i j‖)) +
            (∑ j, a j ^ 2 / 2 * (∑ i, ‖A i j‖)) := hsplit
      _ ≤ (∑ i, a i ^ 2 / 2 * s) + (∑ j, a j ^ 2 / 2 * s) :=
            add_le_add hfirst hsecond
      _ = s * ∑ i, a i ^ 2 := hsum
  exact hstep1.trans hstep2

/-- The Rayleigh quotient of the operator attached to `A` is bounded by `s`. -/
theorem rayleighQuotient_le {N : ℕ} {s : ℝ} (A : Matrix (Fin N) (Fin N) ℂ)
    (hrow : ∀ i, ∑ j, ‖A i j‖ ≤ s) (hcol : ∀ j, ∑ i, ‖A i j‖ ≤ s) (hs : 0 ≤ s) :
    ∀ x : EuclideanSpace ℂ (Fin N),
      |(LinearMap.toContinuousLinearMap (Matrix.toEuclideanLin A)).rayleighQuotient x| ≤ s := by
  classical
  intro x
  have hTx : (LinearMap.toContinuousLinearMap (Matrix.toEuclideanLin A) x).ofLp =
      A *ᵥ x.ofLp := by
    have := Matrix.ofLp_toLpLin (p := 2) (q := 2) A x
    simpa [Matrix.toEuclideanLin, Matrix.toLin'_apply] using this
  have hinner : (inner ℂ (LinearMap.toContinuousLinearMap (Matrix.toEuclideanLin A) x) x).re =
      (∑ i, star (x.ofLp i) * (A *ᵥ x.ofLp) i).re := by
    have hsym' : (inner ℂ (LinearMap.toContinuousLinearMap (Matrix.toEuclideanLin A) x) x).re =
        (inner ℂ x (LinearMap.toContinuousLinearMap (Matrix.toEuclideanLin A) x)).re := by
      simpa using inner_re_symm (𝕜 := ℂ)
        (LinearMap.toContinuousLinearMap (Matrix.toEuclideanLin A) x) x
    rw [hsym', EuclideanSpace.inner_eq_star_dotProduct]
    simp only [dotProduct, hTx, Complex.re_sum]
    apply Finset.sum_congr rfl
    intro i _
    rw [mul_comm]
    simp only [Pi.star_apply]
  have hxnorm : ‖x‖ ^ 2 = ∑ i, ‖x.ofLp i‖ ^ 2 := by
    rw [EuclideanSpace.norm_sq_eq]
  have hbound := re_dotProduct_mulVec_le A hrow hcol x.ofLp
  have hre_le : |(inner ℂ (LinearMap.toContinuousLinearMap (Matrix.toEuclideanLin A) x) x).re| ≤
      s * ‖x‖ ^ 2 := by
    rw [hinner, hxnorm]
    exact hbound
  by_cases hx : x = 0
  · subst hx
    simp [ContinuousLinearMap.rayleighQuotient_apply_zero, hs]
  · have hx2 : 0 < ‖x‖ ^ 2 := by
      have : 0 < ‖x‖ := norm_pos_iff.mpr hx
      positivity
    have hRQ : (LinearMap.toContinuousLinearMap (Matrix.toEuclideanLin A)).rayleighQuotient x =
        (inner ℂ (LinearMap.toContinuousLinearMap (Matrix.toEuclideanLin A) x) x).re / ‖x‖ ^ 2 := rfl
    rw [hRQ, abs_div, abs_of_pos hx2]
    rw [div_le_iff₀ hx2]
    calc |(inner ℂ (LinearMap.toContinuousLinearMap (Matrix.toEuclideanLin A) x) x).re|
        ≤ s * ‖x‖ ^ 2 := hre_le
      _ = s * ‖x‖ ^ 2 := rfl

/-- **Proposition 5 (arXiv:2409.04550, p. 6).**  For an `s`-sparse Hermitian `N × N`
matrix `h` with `|h_{ij}| ≤ 1`, the L² operator (spectral) norm satisfies
`‖h‖ ≤ s`.  This is the precise content of the paper's Gershgorin argument. -/
theorem prop5_spectralNorm_le {N s : ℕ} (h : SparseHermitian N s) :
    ‖h.A‖ ≤ (s : ℝ) := by
  classical
  have hrow : ∀ i, ∑ j, ‖h.A i j‖ ≤ (s : ℝ) :=
    fun i => row_sum_le h.rowSupport_le h.entry_norm_le_one i
  have hcol : ∀ j, ∑ i, ‖h.A i j‖ ≤ (s : ℝ) :=
    fun j => col_sum_le h.hermitian hrow j
  have hsym : (↑(LinearMap.toContinuousLinearMap (Matrix.toEuclideanLin h.A)) :
      EuclideanSpace ℂ (Fin N) →ₗ[ℂ] EuclideanSpace ℂ (Fin N)).IsSymmetric := by
    have := (Matrix.isSymmetric_toEuclideanLin_iff (A := h.A)).mpr h.hermitian
    simpa using this
  have hnorm : ‖h.A‖ = ‖LinearMap.toContinuousLinearMap (Matrix.toEuclideanLin h.A)‖ := by
    rw [Matrix.l2_opNorm_def]
    rfl
  rw [hnorm, ContinuousLinearMap.norm_eq_iSup_rayleighQuotient _ hsym]
  exact ciSup_le (rayleighQuotient_le h.A hrow hcol (by positivity))

/-- **Proposition 5, paper's literal form (arXiv:2409.04550, p. 6):**
`‖h‖ / s ≤ 1` for `s > 0`. -/
theorem prop5_spectralNorm_div_sparsity {N s : ℕ} (h : SparseHermitian N s)
    (hs : 0 < s) :
    ‖h.A‖ / (s : ℝ) ≤ 1 := by
  have hle := prop5_spectralNorm_le h
  rw [div_le_one (by exact_mod_cast hs)]
  exact hle

end Qatlib.Papers.FreeFermion24.MainResults.Prop5SpectralNorm
