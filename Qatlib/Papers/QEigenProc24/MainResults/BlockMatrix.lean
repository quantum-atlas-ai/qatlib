/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Analysis.InnerProductSpace.PiL2
import Qatlib.Papers.QEigenProc24.MainResults.SourceModel

set_option backward.isDefEq.respectTransparency false

/-!
# Spectral Norm Bound and Lower-Triangular Inversion for Block Matrices

This module proves Lemma 1 (spectral norm bound for block matrices via block row and
column `ℓ₁`/`ℓ_∞` sums) and Lemma 13 (explicit inverse of a 2-by-2 lower block-triangular
matrix with invertible diagonal blocks).

## Main statements

* `blockMatrix`: assembles blocks `B j k : Matrix (Row j) (Col k) ℂ` on sigma index types.
* `block_matrix_spectral_norm_bound`: Lemma 1 bound `‖[B_{jk}]‖ ≤ √(max_k ∑_j ‖B_{jk}‖) √(max_j ∑_k ‖B_{jk}‖)`.
* `lower_block_inverse`: Lemma 13 explicit formula for `(fromBlocks A11 0 A21 A22)⁻¹`.

## References

* [Low and Su, 2024][LowSu2024QEigenProc], Lemma 1, Eq. (49), p. 19, and Lemma 13, Eq. (129), p. 36.
-/

set_option autoImplicit false
noncomputable section

open Matrix
open scoped Matrix.Norms.L2Operator BigOperators

namespace Qatlib.Papers.QEigenProc24.MainResults.BlockMatrix

open Qatlib.Papers.QEigenProc24.MainResults

/-- Assemble the block matrix with blocks `B j k : Matrix (Row j) (Col k) ℂ` on the direct
sum of the block index types. -/
def blockMatrix {ι : Type*} (Row Col : ι → Type*)
    (B : ∀ j k, Matrix (Row j) (Col k) ℂ) : Matrix (Σ j, Row j) (Σ k, Col k) ℂ :=
  fun jr kc => B jr.1 kc.1 jr.2 kc.2

/-- **Lemma 1**: the spectral norm of a block matrix is bounded by the geometric mean of
its maximum block-column norm sum and maximum block-row norm sum:
`‖B‖ ≤ √(max_k ∑_j ‖B_{jk}‖) · √(max_j ∑_k ‖B_{jk}‖)`. -/
theorem block_matrix_spectral_norm_bound {ι : Type*} [Fintype ι] [Nonempty ι]
    [DecidableEq ι]
    (Row Col : ι → Type*) [∀ j, Fintype (Row j)] [∀ j, DecidableEq (Row j)]
    [∀ k, Fintype (Col k)] [∀ k, DecidableEq (Col k)]
    (B : ∀ j k, Matrix (Row j) (Col k) ℂ) :
    ‖blockMatrix Row Col B‖ ≤
      Real.sqrt (Finset.univ.sup' Finset.univ_nonempty (fun k => ∑ j, ‖B j k‖)) *
        Real.sqrt (Finset.univ.sup' Finset.univ_nonempty (fun j => ∑ k, ‖B j k‖)) := by
  let C₁ := Finset.univ.sup' Finset.univ_nonempty (fun k => ∑ j, ‖B j k‖)
  let C₂ := Finset.univ.sup' Finset.univ_nonempty (fun j => ∑ k, ‖B j k‖)
  have hcol (k : ι) : ∑ j, ‖B j k‖ ≤ C₁ :=
    Finset.le_sup' (fun k => ∑ j, ‖B j k‖) (Finset.mem_univ k)
  have hrow (j : ι) : ∑ k, ‖B j k‖ ≤ C₂ :=
    Finset.le_sup' (fun j => ∑ k, ‖B j k‖) (Finset.mem_univ j)
  obtain ⟨i⟩ := ‹Nonempty ι›
  have hC₁ : 0 ≤ C₁ :=
    (Finset.sum_nonneg fun j _ => norm_nonneg (B j i)).trans (hcol i)
  have hC₂ : 0 ≤ C₂ :=
    (Finset.sum_nonneg fun k _ => norm_nonneg (B i k)).trans (hrow i)
  change ‖blockMatrix Row Col B‖ ≤ Real.sqrt C₁ * Real.sqrt C₂
  rw [Matrix.l2_opNorm_def]
  refine ContinuousLinearMap.opNorm_le_bound _
    (mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)) fun x => ?_
  let xs (k : ι) : EuclideanSpace ℂ (Col k) :=
    WithLp.toLp 2 (fun c => x.ofLp ⟨k, c⟩)
  let y := toEuclideanLin (blockMatrix Row Col B) x
  let ys (j : ι) : EuclideanSpace ℂ (Row j) :=
    WithLp.toLp 2 (fun r => y.ofLp ⟨j, r⟩)
  have hxs : ∑ k, ‖xs k‖ ^ 2 = ‖x‖ ^ 2 := by
    simp_rw [PiLp.norm_sq_eq_of_L2]
    exact (Fintype.sum_sigma (fun kc : Σ k, Col k => ‖x.ofLp kc‖ ^ 2)).symm
  have hys : ‖y‖ ^ 2 = ∑ j, ‖ys j‖ ^ 2 := by
    simp_rw [PiLp.norm_sq_eq_of_L2]
    exact Fintype.sum_sigma (fun jr : Σ j, Row j => ‖y.ofLp jr‖ ^ 2)
  have hys_apply (j : ι) : ys j = ∑ k, toEuclideanLin (B j k) (xs k) := by
    apply InnerProductSpace.ext_inner_left_basis (EuclideanSpace.basisFun (Row j) ℂ).toBasis
    intro r
    simp only [OrthonormalBasis.coe_toBasis, EuclideanSpace.basisFun_apply,
      EuclideanSpace.inner_single_left, map_one, one_mul]
    simp only [ys, y, xs, toEuclideanLin, Matrix.toLpLin_apply,
      WithLp.ofLp_toLp, Matrix.mulVec, dotProduct, blockMatrix,
      WithLp.ofLp_sum, Finset.sum_apply]
    exact Fintype.sum_sigma _
  have hys_bound (j : ι) :
      ‖ys j‖ ^ 2 ≤ C₂ * ∑ k, ‖B j k‖ * ‖xs k‖ ^ 2 := by
    have htriangle : ‖ys j‖ ≤ ∑ k, ‖B j k‖ * ‖xs k‖ := by
      rw [hys_apply]
      refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun k _ => ?_)
      exact Matrix.l2_opNorm_mulVec (B j k) (xs k)
    have hcs := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ
      (fun k => Real.sqrt ‖B j k‖) (fun k => Real.sqrt ‖B j k‖ * ‖xs k‖)
    have hfactor (k : ι) :
        Real.sqrt ‖B j k‖ * (Real.sqrt ‖B j k‖ * ‖xs k‖) =
          ‖B j k‖ * ‖xs k‖ := by
      rw [← mul_assoc, Real.mul_self_sqrt (norm_nonneg _)]
    simp_rw [hfactor, mul_pow, Real.sq_sqrt (norm_nonneg _)] at hcs
    calc
      ‖ys j‖ ^ 2 ≤ (∑ k, ‖B j k‖ * ‖xs k‖) ^ 2 :=
        (sq_le_sq₀ (norm_nonneg _) (Finset.sum_nonneg fun k _ =>
          mul_nonneg (norm_nonneg _) (norm_nonneg _))).2 htriangle
      _ ≤ (∑ k, ‖B j k‖) * ∑ k, ‖B j k‖ * ‖xs k‖ ^ 2 := hcs
      _ ≤ C₂ * ∑ k, ‖B j k‖ * ‖xs k‖ ^ 2 :=
        mul_le_mul_of_nonneg_right (hrow j) (Finset.sum_nonneg fun k _ =>
          mul_nonneg (norm_nonneg _) (sq_nonneg _))
  have hbound : ‖y‖ ^ 2 ≤ C₁ * C₂ * ‖x‖ ^ 2 := by
    calc
      ‖y‖ ^ 2 = ∑ j, ‖ys j‖ ^ 2 := hys
      _ ≤ ∑ j, C₂ * ∑ k, ‖B j k‖ * ‖xs k‖ ^ 2 :=
        Finset.sum_le_sum fun j _ => hys_bound j
      _ = C₂ * ∑ k, (∑ j, ‖B j k‖) * ‖xs k‖ ^ 2 := by
        rw [← Finset.mul_sum, Finset.sum_comm]
        simp_rw [Finset.sum_mul]
      _ ≤ C₂ * ∑ k, C₁ * ‖xs k‖ ^ 2 := by
        apply mul_le_mul_of_nonneg_left _ hC₂
        exact Finset.sum_le_sum fun k _ =>
          mul_le_mul_of_nonneg_right (hcol k) (sq_nonneg _)
      _ = C₁ * C₂ * ‖x‖ ^ 2 := by
        rw [← Finset.mul_sum, hxs]
        ring
  change ‖y‖ ≤ (Real.sqrt C₁ * Real.sqrt C₂) * ‖x‖
  apply (sq_le_sq₀ (norm_nonneg _) (by positivity)).1
  simpa only [mul_pow, Real.sq_sqrt hC₁, Real.sq_sqrt hC₂] using hbound

/-- **Lemma 13**: for invertible square matrices `A11` and `A22`,
`[[A11, 0], [A21, A22]]⁻¹ = [[A11⁻¹, 0], [-A22⁻¹ A21 A11⁻¹, A22⁻¹]]`. -/
theorem lower_block_inverse {m n : Type*} [Fintype m] [DecidableEq m]
    [Fintype n] [DecidableEq n] {𝕜 : Type*} [Field 𝕜]
    (A11 : Matrix m m 𝕜) (A21 : Matrix n m 𝕜) (A22 : Matrix n n 𝕜)
    (h11 : IsUnit A11) (h22 : IsUnit A22) :
    (fromBlocks A11 0 A21 A22)⁻¹ = fromBlocks A11⁻¹ 0 (-(A22⁻¹ * A21 * A11⁻¹)) A22⁻¹ :=
  Matrix.inv_fromBlocks_zero₁₂_of_isUnit_iff A11 A21 A22 ⟨fun _ => h22, fun _ => h11⟩

end Qatlib.Papers.QEigenProc24.MainResults.BlockMatrix
