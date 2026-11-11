/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.MixedFidelity.FidelityMetric.ComplexArrowTraceNorm.BlockDefs
import Mathlib.Analysis.Matrix.Spectrum
import Mathlib.Tactic

/-!
# Trace norms of complex arrow blocks

The Hermitian two-dimensional matrix `arrow` has an explicit trace norm determined by its real
diagonal parameters and complex off-diagonal entry. Block-diagonal additivity extends the
formula to `fullBlock`, including positive normalization and the balanced-tail specialization
expressed by `errorNumerator`. See [Bhatia1997].

## Main statements

* `arrow_traceNorm`: an exact trace norm for the two-dimensional block.
* `normalized_fullBlock_half_traceNorm`: the formula with a scalar identity tail.
* `balanced_fullBlock_half_traceNorm`: simplification under the trace-balance relation.

## References

* [Bhatia, 1997][Bhatia1997]
-/

set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open Matrix
open scoped BigOperators
namespace Qatlib.Concepts.MixedFidelity.FidelityMetric.ComplexArrowTraceNorm

/-- The complex arrow matrix with real diagonal parameters is Hermitian. -/
lemma arrow_hermitian (ell mass : ℝ) (z : ℂ) : (Qatlib.Concepts.MixedFidelity.FidelityMetric.ComplexArrowTraceNorm.arrow ell mass z).IsHermitian := by
  apply Matrix.ext
  intro i j
  fin_cases i <;> fin_cases j <;> simp [Qatlib.Concepts.MixedFidelity.FidelityMetric.ComplexArrowTraceNorm.arrow, Matrix.conjTranspose_apply]

/-- For real `x` and `y`, the sum of their absolute values equals the maximum of the absolute
sum and absolute difference. -/
private lemma abs_pair_max (x y : ℝ) : |x| + |y| = max |x + y| |x - y| := by
  simp only [abs_eq_max_neg, max_def]
  split_ifs <;> linarith

/-- The arrow matrix has trace norm equal to the maximum of `|mass|` and `Real.sqrt ((2 * ell +
mass) ^ 2 + 4 * ‖z‖ ^ 2)`. -/
theorem arrow_traceNorm (ell mass : ℝ) (z : ℂ) :
    Matrix.traceNorm (Qatlib.Concepts.MixedFidelity.FidelityMetric.ComplexArrowTraceNorm.arrow ell mass z) =
      max |mass| (Real.sqrt ((2 * ell + mass) ^ 2 + 4 * ‖z‖ ^ 2)) := by
  let h :=
      Qatlib.Concepts.MixedFidelity.FidelityMetric.ComplexArrowTraceNorm.arrow_hermitian ell mass z
  let x := h.eigenvalues 0
  let y := h.eigenvalues 1
  have htrace := congrArg Complex.re h.trace_eq_sum_eigenvalues
  have hdet := congrArg Complex.re h.det_eq_prod_eigenvalues
  have hsum : x + y = -mass := by
    calc
      x + y = ell + (-ell - mass) := by
        simpa [Qatlib.Concepts.MixedFidelity.FidelityMetric.ComplexArrowTraceNorm.arrow,
            Matrix.trace, Fin.sum_univ_two, x, y] using htrace.symm
      _ = -mass := by ring
  have hprod : x * y = -ell * (ell + mass) - ‖z‖ ^ 2 := by
    simp [Qatlib.Concepts.MixedFidelity.FidelityMetric.ComplexArrowTraceNorm.arrow, Matrix.det_fin_two, Fin.prod_univ_two, Complex.mul_re,
      Complex.sq_norm, Complex.normSq_apply, x, y] at hdet ⊢
    nlinarith [hdet]
  have hdelta : (x - y) ^ 2 = (2 * ell + mass) ^ 2 + 4 * ‖z‖ ^ 2 := by
    linear_combination (x + y - mass) * hsum - 4 * hprod
  rw [Matrix.traceNorm_Hermitian_eq_sum_abs_eigenvalues h, Fin.sum_univ_two]
  change |x| + |y| = _
  rw [abs_pair_max, hsum, abs_neg, ← hdelta, Real.sqrt_sq_eq_abs]

/-- The trace norm of a block-diagonal matrix is the sum of the trace norms of its two diagonal
blocks. -/
private lemma traceNorm_fromBlocks_diagonal {I J : Type*} [Fintype I] [DecidableEq I]
    [Fintype J] [DecidableEq J] (A : Matrix I I ℂ) (D : Matrix J J ℂ) :
    Matrix.traceNorm (Matrix.fromBlocks A 0 0 D) = A.traceNorm + D.traceNorm := by
  classical
  letI : DecidableEq I := Classical.decEq I
  letI : DecidableEq J := Classical.decEq J
  letI : DecidableEq (I ⊕ J) := Classical.decEq (I ⊕ J)
  let L : Matrix (I ⊕ J) I ℂ := fun a b => match a with
    | .inl i => if i = b then 1 else 0
    | .inr _ => 0
  let R : Matrix (I ⊕ J) J ℂ := fun a b => match a with
    | .inl _ => 0
    | .inr i => if i = b then 1 else 0
  have hL : L.Isometry := by
    ext a b
    simp [Matrix.mul_apply, Matrix.conjTranspose_apply, L, Fintype.sum_sum_type,
      Matrix.one_apply, eq_comm]
  have hR : R.Isometry := by
    ext a b
    simp [Matrix.mul_apply, Matrix.conjTranspose_apply, R, Fintype.sum_sum_type,
      Matrix.one_apply, eq_comm]
  have hsplit : Matrix.fromBlocks A 0 0 D = L * A * Lᴴ + R * D * Rᴴ := by
    ext a b
    cases a <;> cases b <;>
      simp [L, R, Matrix.mul_apply, Matrix.conjTranspose_apply]
  have hupper : Matrix.traceNorm (Matrix.fromBlocks A 0 0 D) ≤ A.traceNorm + D.traceNorm := by
    rw [hsplit]
    have h := Matrix.traceNorm_add_le (L * A * Lᴴ) (R * D * Rᴴ)
    rwa [Matrix.traceNorm_isometry_right hL, Matrix.traceNorm_isometry_left hL,
      Matrix.traceNorm_isometry_right hR, Matrix.traceNorm_isometry_left hR] at h
  obtain ⟨U, hU⟩ := (Matrix.traceNorm_eq_max_re_tr_U A).1
  obtain ⟨V, hV⟩ := (Matrix.traceNorm_eq_max_re_tr_U D).1
  let W : Matrix (I ⊕ J) (I ⊕ J) ℂ := Matrix.fromBlocks U.val 0 0 V.val
  have hUU : U.valᴴ * U.val = 1 := Matrix.UnitaryGroup.star_mul_self U
  have hVV : V.valᴴ * V.val = 1 := Matrix.UnitaryGroup.star_mul_self V
  have hW : W.Isometry := by
    change Wᴴ * W = 1
    simp [W, Matrix.fromBlocks_conjTranspose, Matrix.fromBlocks_multiply, hUU, hVV,
      Matrix.fromBlocks_one]
    ext a b
    by_cases hab : a = b <;> simp [Matrix.one_apply, hab]
  have htrace : ((W * Matrix.fromBlocks A 0 0 D).trace).re = A.traceNorm + D.traceNorm := by
    simp only [W, Matrix.fromBlocks_multiply, Matrix.zero_mul, Matrix.mul_zero,
      zero_add, add_zero]
    simp only [Matrix.trace, Fintype.sum_sum_type, Complex.add_re]
    exact congrArg₂ (· + ·) hU hV
  have hlower : A.traceNorm + D.traceNorm ≤ Matrix.traceNorm (Matrix.fromBlocks A 0 0 D) := by
    rw [← htrace]
    exact (Complex.re_le_norm _).trans ((Matrix.abs_trace_le_traceNorm _).trans_eq
      (Matrix.traceNorm_isometry_left hW))
  exact le_antisymm hupper hlower

/-- The trace norm of a real scalar times the `n`-dimensional identity is `n * |tail|`. -/
private lemma traceNorm_scalar_one (n : ℕ) (tail : ℝ) :
    Matrix.traceNorm ((tail : ℂ) • (1 : Matrix (Fin n) (Fin n) ℂ)) = (n : ℝ) * |tail| := by
  rw [Matrix.traceNorm_smul]
  simp [Matrix.traceNorm, Complex.norm_real, Real.norm_eq_abs, mul_comm]

/-- For positive `q`, half the trace norm of `fullBlock / q` is the arrow trace norm plus `n *
|tail|`, divided by `2 * q`. -/
theorem normalized_fullBlock_half_traceNorm (n : ℕ) (ell mass tail q : ℝ)
    (z : ℂ) (hq : 0 < q) :
    Matrix.traceNorm (((q⁻¹ : ℝ) : ℂ) • Qatlib.Concepts.MixedFidelity.FidelityMetric.ComplexArrowTraceNorm.fullBlock n ell mass tail z) / 2 =
      (max |mass| (Real.sqrt ((2 * ell + mass) ^ 2 + 4 * ‖z‖ ^ 2)) +
        (n : ℝ) * |tail|) / (2 * q) := by
  rw [Matrix.traceNorm_smul]
  simp only [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hq)]
  rw [Qatlib.Concepts.MixedFidelity.FidelityMetric.ComplexArrowTraceNorm.fullBlock,
      traceNorm_fromBlocks_diagonal, Qatlib.Concepts.MixedFidelity.FidelityMetric.ComplexArrowTraceNorm.arrow_traceNorm, traceNorm_scalar_one]
  ring

/-- If `mass` is nonnegative and `n * tail = mass`, the normalized half trace norm equals
`errorNumerator ell mass (‖z‖ ^ 2) / q`. -/
theorem balanced_fullBlock_half_traceNorm (n : ℕ) (ell mass tail q : ℝ)
    (z : ℂ) (hq : 0 < q) (hmass : 0 ≤ mass) (hbalance : (n : ℝ) * tail = mass) :
    Matrix.traceNorm (((q⁻¹ : ℝ) : ℂ) • Qatlib.Concepts.MixedFidelity.FidelityMetric.ComplexArrowTraceNorm.fullBlock n ell mass tail z) / 2 =
      Qatlib.Concepts.MixedFidelity.FidelityMetric.ComplexArrowTraceNorm.errorNumerator ell mass (‖z‖ ^ 2) / q := by
  have htail : (n : ℝ) * |tail| = mass := by
    calc
      (n : ℝ) * |tail| = |(n : ℝ) * tail| := by
        simpa only [abs_of_nonneg (Nat.cast_nonneg n : (0 : ℝ) ≤ (n : ℝ))] using
          (abs_mul (n : ℝ) tail).symm
      _ = mass := by rw [hbalance, abs_of_nonneg hmass]
  rw [Qatlib.Concepts.MixedFidelity.FidelityMetric.ComplexArrowTraceNorm.normalized_fullBlock_half_traceNorm n ell mass tail q z hq, htail,
    abs_of_nonneg hmass]
  unfold Qatlib.Concepts.MixedFidelity.FidelityMetric.ComplexArrowTraceNorm.errorNumerator
  by_cases hs : Real.sqrt ((2 * ell + mass) ^ 2 + 4 * ‖z‖ ^ 2) ≤ mass
  · rw [max_eq_left hs, max_eq_left (by linarith :
      (mass + Real.sqrt ((2 * ell + mass) ^ 2 + 4 * ‖z‖ ^ 2)) / 2 ≤ mass)]
    ring
  · have hs' := le_of_not_ge hs
    rw [max_eq_right hs', max_eq_right (by linarith :
      mass ≤ (mass + Real.sqrt ((2 * ell + mass) ^ 2 + 4 * ‖z‖ ^ 2)) / 2)]
    ring
end Qatlib.Concepts.MixedFidelity.FidelityMetric.ComplexArrowTraceNorm
