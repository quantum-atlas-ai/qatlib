/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.NonSparseHam09.MainResults.Prop2Arboricity

/-!
# Exact norm estimates for weighted star matrices

Defines `starMatrix` and computes its action and column norms. When the center weight vanishes,
its spectral norm and maximum-column norm both equal the Euclidean norm of the weights; the same
identity controls the complex entrywise absolute-value matrix. See [ChildsKothari2010] for the
surrounding analysis.

## Main statements

* `mcnNorm_starMatrix`: With zero center weight, the maximum Euclidean column norm of the star
  matrix is `√(∑ i, ‖w i‖²)`.
* `specNorm_starMatrix`: With zero center weight, the spectral norm of the star matrix is `√(∑
  i, ‖w i‖²)`.
* `star_abs_specNorm_eq_mcn`: With zero center weight, the spectral norm of the complex
  entrywise absolute-value star matrix equals the original star matrix's maximum Euclidean
  column norm.

## References

* [Childs and Kothari, 2010][ChildsKothari2010]
-/

set_option autoImplicit false
set_option maxHeartbeats 800000
noncomputable section

open Matrix Finset
open scoped Matrix.Norms.L2Operator BigOperators

namespace Qatlib.Papers.NonSparseHam09.MainResults

variable {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]

/-- The weighted star matrix with center column `w`, conjugated center-row entries away from the
center, and all other entries zero. -/
def starMatrix (c : ι) (w : ι → ℂ) : Matrix ι ι ℂ :=
  fun i j => if j = c then w i else if i = c then star (w j) else 0

omit [Fintype ι] [Nonempty ι] in

/-- If the center weight is zero, the weighted star matrix is Hermitian [ChildsKothari2010]. -/
lemma starMatrix_isHermitian {c : ι} {w : ι → ℂ} (hc : w c = 0) :
    (starMatrix c w).IsHermitian := by
  refine Matrix.IsHermitian.ext fun i j => ?_
  by_cases hjc : j = c
  · by_cases hic : i = c
    · simp [starMatrix, hjc, hic, hc]
    · simp [starMatrix, hjc, hic]
  · by_cases hic : i = c
    · simp [starMatrix, hjc, hic]
    · simp [starMatrix, hjc, hic]

omit [Nonempty ι] in

/-- With zero center weight, multiplication by the star matrix gives the conjugate-weighted sum
at the center and `w i * v c` at every other vertex [ChildsKothari2010]. -/
lemma starMatrix_mulVec {c : ι} {w : ι → ℂ} (hc : w c = 0) (v : ι → ℂ) :
    starMatrix c w *ᵥ v
      = fun i => if i = c then ∑ j, star (w j) * v j else w i * v c := by
  funext i
  rw [Matrix.mulVec, dotProduct]
  by_cases hi : i = c
  · rw [ite_eq_left hi]
    refine Finset.sum_congr rfl fun j _ => ?_
    by_cases hj : j = c
    · simp [starMatrix, hj, hi, hc]
    · simp [starMatrix, hj, hi]
  · rw [ite_eq_right hi]
    rw [Finset.sum_eq_single c]
    · simp [starMatrix]
    · intro b _ hb
      simp [starMatrix, hi, hb]
    · intro hc'
      exact absurd (Finset.mem_univ c) hc'

omit [Nonempty ι] in

/-- The squared Euclidean norm of the center column of a star matrix is `∑ i, ‖w i‖²`
[ChildsKothari2010]. -/
lemma starMatrix_col_center {c : ι} (w : ι → ℂ) :
    (∑ i, ‖starMatrix c w i c‖ ^ 2) = ∑ i, ‖w i‖ ^ 2 := by
  refine Finset.sum_congr rfl fun i _ => ?_
  simp [starMatrix]

omit [Nonempty ι] in

/-- For `j ≠ c`, the squared Euclidean norm of column `j` of the star matrix is `‖w j‖²`
[ChildsKothari2010]. -/
lemma starMatrix_col_other {c : ι} (w : ι → ℂ) {j : ι} (hj : j ≠ c) :
    (∑ i, ‖starMatrix c w i j‖ ^ 2) = ‖w j‖ ^ 2 := by
  rw [Finset.sum_eq_single c]
  · simp [starMatrix, hj]
  · intro b _ hb
    simp [starMatrix, hj, hb]
  · intro hc
    exact absurd (Finset.mem_univ c) hc

/-- With zero center weight, the maximum Euclidean column norm of the star matrix is `√(∑ i, ‖w
i‖²)` [ChildsKothari2010]. -/
theorem mcnNorm_starMatrix {c : ι} {w : ι → ℂ} (_hc : w c = 0) :
    mcnNorm (starMatrix c w) = Real.sqrt (∑ i, ‖w i‖ ^ 2) := by
  unfold mcnNorm
  refine le_antisymm ?_ ?_
  · refine Finset.sup'_le _ _ fun j _ => ?_
    change Real.sqrt (∑ i, ‖starMatrix c w i j‖ ^ 2)
      ≤ Real.sqrt (∑ i, ‖w i‖ ^ 2)
    by_cases hj : j = c
    · rw [hj, starMatrix_col_center]
    · rw [starMatrix_col_other w hj]
      exact Real.sqrt_le_sqrt
        (Finset.single_le_sum (f := fun i => ‖w i‖ ^ 2)
          (fun _ _ => sq_nonneg _) (Finset.mem_univ j))
  · have h := Finset.le_sup' (fun j => Real.sqrt (∑ i, ‖starMatrix c w i j‖ ^ 2))
      (Finset.mem_univ c)
    rw [starMatrix_col_center] at h
    exact h

omit [Nonempty ι] in

/-- With zero center weight, the squared norm of the conjugate-weighted center sum is bounded by
the product of the weight and vector squared norms away from the center [ChildsKothari2010]. -/
lemma starMatrix_center_sq_bound {c : ι} {w : ι → ℂ} (hc : w c = 0) (v : ι → ℂ) :
    ‖∑ j, star (w j) * v j‖ ^ 2
      ≤ (∑ j ∈ Finset.univ.erase c, ‖w j‖ ^ 2)
          * (∑ j ∈ Finset.univ.erase c, ‖v j‖ ^ 2) := by
  have hzero : star (w c) * v c = 0 := by simp [hc]
  have hsplit : (∑ j, star (w j) * v j)
      = ∑ j ∈ Finset.univ.erase c, star (w j) * v j := by
    rw [← Finset.sum_erase_add (s := Finset.univ) (a := c)
      (f := fun j => star (w j) * v j) (Finset.mem_univ c), hzero, add_zero]
  rw [hsplit]
  have hle : ‖∑ j ∈ Finset.univ.erase c, star (w j) * v j‖
      ≤ ∑ j ∈ Finset.univ.erase c, ‖w j‖ * ‖v j‖ := by
    refine (norm_sum_le _ _).trans (le_of_eq ?_)
    refine Finset.sum_congr rfl fun j _ => ?_
    simp
  have hnonneg : 0 ≤ ∑ j ∈ Finset.univ.erase c, ‖w j‖ * ‖v j‖ :=
    Finset.sum_nonneg fun _ _ => mul_nonneg (norm_nonneg _) (norm_nonneg _)
  have hsq : ‖∑ j ∈ Finset.univ.erase c, star (w j) * v j‖ ^ 2
      ≤ (∑ j ∈ Finset.univ.erase c, ‖w j‖ * ‖v j‖) ^ 2 := by
    nlinarith [norm_nonneg (∑ j ∈ Finset.univ.erase c, star (w j) * v j), hle]
  refine hsq.trans ?_
  simpa [mul_comm, mul_left_comm, mul_assoc] using
    (Finset.sum_mul_sq_le_sq_mul_sq (Finset.univ.erase c)
      (fun j => ‖w j‖) (fun j => ‖v j‖))

/-- With zero center weight, the squared Euclidean norm of the star matrix applied to `v` is at
most `(∑ i, ‖w i‖²) * (∑ i, ‖v i‖²)` [ChildsKothari2010]. -/
lemma starMatrix_sum_sq_bound {c : ι} {w : ι → ℂ} (hc : w c = 0) (v : ι → ℂ) :
    (∑ i, ‖(starMatrix c w *ᵥ v) i‖ ^ 2)
      ≤ (∑ i, ‖w i‖ ^ 2) * (∑ i, ‖v i‖ ^ 2) := by
  rw [starMatrix_mulVec hc]
  set S := ∑ i, ‖v i‖ ^ 2 with hS
  set Vc := ‖v c‖ ^ 2 with hVc
  set W2 := ∑ i, ‖w i‖ ^ 2 with hW2
  have hsplit : (∑ i, ‖(if i = c then (∑ j, star (w j) * v j) else w i * v c)‖ ^ 2)
      = ‖∑ j, star (w j) * v j‖ ^ 2
        + ∑ i ∈ Finset.univ.erase c, ‖w i * v c‖ ^ 2 := by
    rw [← Finset.sum_erase_add (s := Finset.univ) (a := c)
      (f := fun i => ‖(if i = c then (∑ j, star (w j) * v j) else w i * v c)‖ ^ 2)
      (Finset.mem_univ c)]
    have hcval : (if c = c then (∑ j, star (w j) * v j) else w c * v c)
        = ∑ j, star (w j) * v j := by simp
    have hsums : (∑ i ∈ Finset.univ.erase c,
          ‖(if i = c then (∑ j, star (w j) * v j) else w i * v c)‖ ^ 2)
        = ∑ i ∈ Finset.univ.erase c, ‖w i * v c‖ ^ 2 := by
      refine Finset.sum_congr rfl fun i hi => ?_
      have hi' : i ≠ c := (Finset.mem_erase.mp hi).1
      simp [hi']
    rw [hcval, hsums, add_comm]
  have herase_w : (∑ i ∈ Finset.univ.erase c, ‖w i‖ ^ 2) = W2 := by
    rw [Finset.sum_erase_eq_sub (Finset.mem_univ c), hW2]
    simp [hc]
  have herase_v : (∑ i ∈ Finset.univ.erase c, ‖v i‖ ^ 2) = S - Vc := by
    rw [hS, hVc, Finset.sum_erase_eq_sub (Finset.mem_univ c)]
  have herase_noncenter : (∑ i ∈ Finset.univ.erase c, ‖w i * v c‖ ^ 2) = W2 * Vc := by
    have hmul : ∀ i, ‖w i * v c‖ ^ 2 = ‖w i‖ ^ 2 * Vc := by
      intro i; rw [norm_mul, mul_pow]
    rw [Finset.sum_congr rfl (fun i _ => hmul i), ← Finset.sum_mul, herase_w]
  have hcenterbound := starMatrix_center_sq_bound hc v
  rw [herase_w, herase_v] at hcenterbound
  rw [hsplit, herase_noncenter]
  have hVc_le : Vc ≤ S := by
    rw [hVc, hS]
    exact Finset.single_le_sum (f := fun i => ‖v i‖ ^ 2)
      (fun _ _ => sq_nonneg _) (Finset.mem_univ c)
  nlinarith [hcenterbound, hVc_le]

/-- With zero center weight, the spectral norm of the star matrix is `√(∑ i, ‖w i‖²)`
[ChildsKothari2010]. -/
theorem specNorm_starMatrix {c : ι} {w : ι → ℂ} (hc : w c = 0) :
    specNorm (starMatrix c w) = Real.sqrt (∑ i, ‖w i‖ ^ 2) := by
  set W := Real.sqrt (∑ i, ‖w i‖ ^ 2) with hW
  have hW2 : W ^ 2 = ∑ i, ‖w i‖ ^ 2 :=
    Real.sq_sqrt (Finset.sum_nonneg fun _ _ => sq_nonneg _)
  have hWnonneg : 0 ≤ W := Real.sqrt_nonneg _
  refine le_antisymm ?_ ?_
  · rw [specNorm_eq_l2, ← Matrix.l2_opNorm_toEuclideanCLM]
    refine ContinuousLinearMap.opNorm_le_bound _ hWnonneg fun v => ?_
    have hdelC : (⇑(Matrix.toEuclideanCLM (n := ι) (𝕜 := ℂ)) (starMatrix c w)) v
        = (EuclideanSpace.equiv ι ℂ).symm (starMatrix c w *ᵥ v.ofLp) := by
      apply WithLp.ofLp_injective
      simp [Matrix.ofLp_toEuclideanCLM]
    rw [hdelC, EuclideanSpace.norm_eq, EuclideanSpace.norm_eq]
    have hb := starMatrix_sum_sq_bound hc v.ofLp
    rw [← hW2] at hb
    refine (Real.sqrt_le_sqrt hb).trans (le_of_eq ?_)
    rw [Real.sqrt_mul (sq_nonneg W), Real.sqrt_sq hWnonneg]
  · have hmem := specNorm_mulVec (starMatrix c w)
        ((WithLp.toLp 2 (Pi.single c (1 : ℂ))) : EuclideanSpace ℂ ι)
    rw [single_one_norm, mul_one] at hmem
    have hmv : starMatrix c w *ᵥ (Pi.single c (1 : ℂ)) = w := by
      rw [starMatrix_mulVec hc]
      funext i
      by_cases hi : i = c
      · rw [ite_eq_left hi, hi]
        simp [hc, Pi.single_apply]
      · rw [ite_eq_right hi]
        simp
    rw [WithLp.ofLp_toLp, hmv] at hmem
    have hnorm : ‖(EuclideanSpace.equiv ι ℂ).symm w‖ = W := by
      rw [EuclideanSpace.norm_eq, hW]
      rfl
    rwa [hnorm] at hmem

omit [Fintype ι] [Nonempty ι] in

/-- The entrywise absolute-value matrix of a star matrix has center column `‖w i‖`, center-row
entries `‖w j‖` away from the center, and zeros elsewhere [ChildsKothari2010]. -/
lemma absMatrix_starMatrix {c : ι} (w : ι → ℂ) :
    absMatrix (starMatrix c w)
      = fun i j => if j = c then ‖w i‖ else if i = c then ‖w j‖ else 0 := by
  funext i j
  simp only [absMatrix, starMatrix]
  by_cases hj : j = c
  · rw [ite_eq_left hj, ite_eq_left hj]
  · by_cases hi : i = c
    · rw [ite_eq_right hj, ite_eq_left hi, ite_eq_right hj, ite_eq_left hi]
      exact norm_star (w j)
    · rw [ite_eq_right hj, ite_eq_right hi, ite_eq_right hj, ite_eq_right hi]
      simp

/-- With zero center weight, the spectral norm of the complex entrywise absolute-value star
matrix equals the original star matrix's maximum Euclidean column norm [ChildsKothari2010]. -/
theorem star_abs_specNorm_eq_mcn {c : ι} {w : ι → ℂ} (hc : w c = 0) :
    specNorm ((absMatrix (starMatrix c w)).map Complex.ofReal) = mcnNorm (starMatrix c w) := by
  have hwRc : (fun i => ((‖w i‖ : ℝ) : ℂ)) c = 0 := by
    simp [hc]
  have habs : (absMatrix (starMatrix c w)).map Complex.ofReal
      = starMatrix c (fun i => ((‖w i‖ : ℝ) : ℂ)) := by
    funext i j
    rw [Matrix.map_apply, absMatrix_starMatrix]
    simp only [starMatrix]
    by_cases hj : j = c
    · rw [ite_eq_left hj, ite_eq_left hj]
    · by_cases hi : i = c
      · rw [ite_eq_right hj, ite_eq_left hi, ite_eq_right hj, ite_eq_left hi]
        simp
      · rw [ite_eq_right hj, ite_eq_right hi, ite_eq_right hj, ite_eq_right hi]
        simp
  rw [habs,
    specNorm_starMatrix (c := c) (w := fun i => ((‖w i‖ : ℝ) : ℂ)) hwRc,
    mcnNorm_starMatrix (c := c) (w := w) hc]
  have hsum : (∑ i : ι, ‖(((‖w i‖ : ℝ)) : ℂ)‖ ^ 2) = ∑ i : ι, ‖w i‖ ^ 2 := by
    refine Finset.sum_congr (rfl : (Finset.univ : Finset ι) = Finset.univ) ?_
    intro i _
    rw [Complex.norm_real, Real.norm_of_nonneg (norm_nonneg (w i))]
  rw [hsum]

end Qatlib.Papers.NonSparseHam09.MainResults
