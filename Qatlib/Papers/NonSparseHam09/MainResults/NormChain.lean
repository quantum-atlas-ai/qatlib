/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.NonSparseHam09.MainResults.Defs
import Mathlib.LinearAlgebra.Matrix.Hermitian

/-!
# Matrix norm comparison chain

Proves comparisons among maximum-entry, maximum-column, spectral, entrywise-absolute spectral,
and column-sum norms of finite matrices. The theorem `lemma1_norm_chain` assembles the Hermitian
norm chain, and the identity and all-ones matrices provide exact comparison values. See
[ChildsKothari2010] for the surrounding analysis.

## Main statements

* `lemma1_norm_chain`: For Hermitian `H`, the norms satisfy `maxNorm H ≤ mcnNorm H ≤ specNorm H
  ≤ specNorm (absMatrix H) ≤ l1Norm H ≤ √N * mcnNorm H ≤ N * maxNorm H`, where `N` is the index
  cardinality.
* `lemma1_tight_identity`: The maximum-entry, maximum-column, spectral, and entrywise-absolute
  spectral norms of the identity matrix are all one.
* `lemma1_tight_allOnes`: For the all-ones matrix in dimension `N`, the column-sum,
  maximum-column, and maximum-entry norms are `N`, `√N`, and one, respectively.

## References

* [Childs and Kothari, 2010][ChildsKothari2010]
-/

set_option warningAsError false

set_option autoImplicit false
set_option linter.unusedSectionVars false
noncomputable section

open Matrix Finset
open scoped Matrix.Norms.L2Operator BigOperators

namespace Qatlib.Papers.NonSparseHam09.MainResults

variable {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]

/-- For a complex matrix, `specNorm` equals the norm supplied by the Euclidean operator-norm
instance. -/
lemma specNorm_eq_l2 (H : Matrix ι ι ℂ) : specNorm H = ‖H‖ := rfl

/-- For a real or complex matrix, `specNorm` equals the norm supplied by the Euclidean
operator-norm instance. -/
lemma specNorm_eq_l2' {𝕜 : Type*} [RCLike 𝕜] (H : Matrix ι ι 𝕜) : specNorm H = ‖H‖ := rfl

/-- The spectral norm of a real or complex matrix is nonnegative. -/
lemma specNorm_nonneg {𝕜 : Type*} [RCLike 𝕜] (H : Matrix ι ι 𝕜) : 0 ≤ specNorm H := by
  rw [specNorm_eq_l2']
  exact norm_nonneg H

/-- The norm of each matrix entry is at most `maxNorm H`. -/
lemma le_maxNorm (H : Matrix ι ι ℂ) (i j : ι) : ‖H i j‖ ≤ maxNorm H :=
  (Finset.le_sup' (fun j : ι => ‖H i j‖) (Finset.mem_univ j)).trans
    (Finset.le_sup' (fun i : ι => Finset.univ.sup' Finset.univ_nonempty
      (fun j : ι => ‖H i j‖)) (Finset.mem_univ i))

/-- The maximum-entry norm is nonnegative. -/
lemma maxNorm_nonneg (H : Matrix ι ι ℂ) : 0 ≤ maxNorm H := by
  obtain ⟨i⟩ := (inferInstance : Nonempty ι)
  exact (norm_nonneg (H i i)).trans (le_maxNorm H i i)

/-- The maximum Euclidean column norm is nonnegative. -/
lemma mcnNorm_nonneg (H : Matrix ι ι ℂ) : 0 ≤ mcnNorm H := by
  obtain ⟨j⟩ := (inferInstance : Nonempty ι)
  exact (Real.sqrt_nonneg _).trans
    (Finset.le_sup' (fun j : ι => Real.sqrt (∑ i : ι, ‖H i j‖ ^ 2)) (Finset.mem_univ j))

/-- The maximum column-sum norm is nonnegative. -/
lemma l1Norm_nonneg (H : Matrix ι ι ℂ) : 0 ≤ l1Norm H := by
  obtain ⟨j⟩ := (inferInstance : Nonempty ι)
  exact (Finset.sum_nonneg (fun i _ => norm_nonneg _)).trans
    (Finset.le_sup' (fun j : ι => ∑ i : ι, ‖H i j‖) (Finset.mem_univ j))

/-- The square root of the sum of squared entry norms in column `j` equals the Euclidean norm of
that column. -/
lemma sqrt_col_sq_eq (H : Matrix ι ι ℂ) (j : ι) :
    Real.sqrt (∑ i, ‖H i j‖ ^ 2)
      = ‖(EuclideanSpace.equiv ι ℂ).symm (fun i => H i j)‖ := by
  rw [EuclideanSpace.norm_eq]
  congr 1

/-- The Euclidean norm of a coordinate vector with a single entry equal to one is one. -/
lemma single_one_norm (j : ι) :
    ‖(WithLp.toLp 2 (Pi.single j (1 : ℂ)) : EuclideanSpace ℂ ι)‖ = 1 := by
  rw [EuclideanSpace.norm_eq]
  have h : ∑ i : ι, ‖(WithLp.toLp 2 (Pi.single j (1 : ℂ)) : EuclideanSpace ℂ ι) i‖ ^ 2 = 1 := by
    have h' : ∑ i : ι, ‖(Pi.single j (1 : ℂ) : ι → ℂ) i‖ ^ 2 = 1 := by
      rw [Fintype.sum_eq_single j]
      · simp
      · intro b hb
        simp [Pi.single_apply, Ne.symm hb]
    simpa using h'
  rw [h, Real.sqrt_one]

/-- The Euclidean norm of a matrix-vector product is at most the spectral norm of the matrix
times the norm of the vector. -/
lemma specNorm_mulVec {𝕜 : Type*} [RCLike 𝕜] (H : Matrix ι ι 𝕜) (x : EuclideanSpace 𝕜 ι) :
    ‖(EuclideanSpace.equiv ι 𝕜).symm (H *ᵥ x.ofLp)‖ ≤ specNorm H * ‖x‖ := by
  have h := Matrix.l2_opNorm_mulVec H x
  simpa [specNorm_eq_l2'] using h

/-- The maximum-entry norm is at most the maximum Euclidean column norm. -/
lemma maxNorm_le_mcnNorm (H : Matrix ι ι ℂ) : maxNorm H ≤ mcnNorm H := by
  refine Finset.sup'_le _ _ fun i _ => Finset.sup'_le _ _ fun j _ => ?_
  have h1 : ‖H i j‖ ≤ Real.sqrt (∑ i', ‖H i' j‖ ^ 2) := by
    rw [← Real.sqrt_sq (norm_nonneg (H i j))]
    refine Real.sqrt_le_sqrt ?_
    simpa using Finset.single_le_sum (f := fun i' => ‖H i' j‖ ^ 2)
      (fun _ _ => sq_nonneg _) (Finset.mem_univ i)
  exact h1.trans
    (Finset.le_sup' (fun j => Real.sqrt (∑ i, ‖H i j‖ ^ 2)) (Finset.mem_univ j))

/-- The maximum Euclidean column norm is at most the spectral norm. -/
lemma mcnNorm_le_specNorm (H : Matrix ι ι ℂ) : mcnNorm H ≤ specNorm H := by
  refine Finset.sup'_le _ _ fun j _ => ?_
  rw [sqrt_col_sq_eq]
  have hmv := specNorm_mulVec H ((WithLp.toLp 2 (Pi.single j (1 : ℂ))) : EuclideanSpace ℂ ι)
  simp only [WithLp.ofLp_toLp] at hmv
  rw [single_one_norm, mul_one] at hmv
  have hsingle : (H *ᵥ (Pi.single j (1 : ℂ))) = fun i => H i j := by
    funext i
    simp [Matrix.mulVec, dotProduct, Pi.single_apply]
  simpa [hsingle] using hmv

/-- The spectral norm of a complex matrix is at most the spectral norm of its real entrywise
absolute-value matrix. -/
lemma specNorm_le_specNorm_abs (H : Matrix ι ι ℂ) :
    specNorm H ≤ specNorm (absMatrix H) := by
  have hR : 0 ≤ specNorm (absMatrix H) := specNorm_nonneg _
  rw [specNorm_eq_l2, ← Matrix.l2_opNorm_toEuclideanCLM]
  refine ContinuousLinearMap.opNorm_le_bound _ hR fun v => ?_
  have hdelC : (⇑(Matrix.toEuclideanCLM (n := ι) (𝕜 := ℂ)) H) v
      = (EuclideanSpace.equiv ι ℂ).symm (H *ᵥ v.ofLp) := by
    apply WithLp.ofLp_injective
    simp [Matrix.ofLp_toEuclideanCLM]
  rw [hdelC]

  have hdom :
      ‖(EuclideanSpace.equiv ι ℂ).symm (H *ᵥ v.ofLp)‖
        ≤ ‖(EuclideanSpace.equiv ι ℝ).symm
            (absMatrix H *ᵥ (fun j => ‖v.ofLp j‖))‖ := by
    rw [EuclideanSpace.norm_eq, EuclideanSpace.norm_eq]
    refine Real.sqrt_le_sqrt (Finset.sum_le_sum fun i _ => ?_)
    have hcomp : ‖(H *ᵥ v.ofLp) i‖
        ≤ (absMatrix H *ᵥ (fun j => ‖v.ofLp j‖)) i := by
      change ‖∑ j, H i j * v.ofLp j‖ ≤ ∑ j, ‖H i j‖ * ‖v.ofLp j‖
      exact (norm_sum_le _ _).trans_eq
        (Finset.sum_congr rfl fun j _ => by simp only [norm_mul])
    have hb : 0 ≤ (absMatrix H *ᵥ (fun j => ‖v.ofLp j‖)) i := by
      change 0 ≤ ∑ j, ‖H i j‖ * ‖v.ofLp j‖
      exact Finset.sum_nonneg fun j _ => mul_nonneg (norm_nonneg _) (norm_nonneg _)
    have hsq : ‖(H *ᵥ v.ofLp) i‖ ^ 2
        ≤ ((absMatrix H *ᵥ (fun j => ‖v.ofLp j‖)) i) ^ 2 := by
      nlinarith [norm_nonneg ((H *ᵥ v.ofLp) i), hcomp, hb]
    calc ‖(H *ᵥ v.ofLp) i‖ ^ 2
        ≤ ((absMatrix H *ᵥ (fun j => ‖v.ofLp j‖)) i) ^ 2 := hsq
      _ = ‖(absMatrix H *ᵥ (fun j => ‖v.ofLp j‖)) i‖ ^ 2 := by
          rw [Real.norm_eq_abs, sq_abs]
  have hstep :
      ‖(EuclideanSpace.equiv ι ℝ).symm
            (absMatrix H *ᵥ (fun j => ‖v.ofLp j‖))‖
        ≤ specNorm (absMatrix H)
            * ‖(EuclideanSpace.equiv ι ℝ).symm (fun j => ‖v.ofLp j‖)‖ := by
    have h := specNorm_mulVec (absMatrix H)
      ((WithLp.toLp 2 (fun j => ‖v.ofLp j‖)) : EuclideanSpace ℝ ι)
    simpa only [WithLp.ofLp_toLp] using! h
  have hveq :
      ‖(EuclideanSpace.equiv ι ℝ).symm (fun j => ‖v.ofLp j‖)‖ = ‖v‖ := by
    rw [EuclideanSpace.norm_eq, EuclideanSpace.norm_eq]
    congr 1
    refine Finset.sum_congr rfl fun i _ => ?_
    simp [Real.norm_eq_abs, sq_abs]
  exact hdom.trans (hstep.trans_eq (by rw [hveq]))

/-- For a Hermitian matrix, each row sum of entry norms is at most the maximum column-sum norm. -/
lemma absMatrix_rowSum_le_l1 (H : Matrix ι ι ℂ) (hH : H.IsHermitian) (i : ι) :
    ∑ j, absMatrix H i j ≤ l1Norm H := by
  have hsymm : ∀ j : ι, absMatrix H i j = absMatrix H j i := by
    intro j
    have h := congrArg norm (hH.apply i j)
    simp only [norm_star] at h
    simpa using! h.symm
  have hEq : ∑ j, absMatrix H i j = ∑ j, ‖H j i‖ := by
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [hsymm j]
    rfl
  rw [hEq]
  exact Finset.le_sup' (fun j => ∑ x : ι, ‖H x j‖) (Finset.mem_univ i)

/-- For a Hermitian matrix, the spectral norm of its entrywise absolute-value matrix is at most
`l1Norm H`. -/
lemma specNorm_abs_le_l1 (H : Matrix ι ι ℂ) (hH : H.IsHermitian) :
    specNorm (absMatrix H) ≤ l1Norm H := by
  have hAnonneg : ∀ i j, 0 ≤ absMatrix H i j := fun i j => norm_nonneg _
  have hRnn : 0 ≤ l1Norm H := l1Norm_nonneg H
  rw [specNorm_eq_l2', ← Matrix.l2_opNorm_toEuclideanCLM]
  refine ContinuousLinearMap.opNorm_le_bound _ hRnn fun v => ?_
  have hdel : (⇑(Matrix.toEuclideanCLM (n := ι) (𝕜 := ℝ)) (absMatrix H)) v
      = (EuclideanSpace.equiv ι ℝ).symm (absMatrix H *ᵥ v.ofLp) := by
    apply WithLp.ofLp_injective
    simp [Matrix.ofLp_toEuclideanCLM]
  rw [hdel]
  set w : ι → ℝ := fun j => v.ofLp j with hw
  have hwn : ‖v‖ = Real.sqrt (∑ i, (w i) ^ 2) := by
    rw [EuclideanSpace.norm_eq]
    congr 1
    refine Finset.sum_congr rfl fun i _ => ?_
    simp [hw, Real.norm_eq_abs, sq_abs]
  have hmainsum :
      ∑ i, ((absMatrix H *ᵥ w) i) ^ 2
        ≤ (l1Norm H) ^ 2 * ∑ i, (w i) ^ 2 := by
    have hcs : ∀ i : ι, ((absMatrix H *ᵥ w) i) ^ 2
        ≤ (∑ j, absMatrix H i j)
            * (∑ j, absMatrix H i j * (w j) ^ 2) := by
      intro i
      have h := Finset.sum_mul_sq_le_sq_mul_sq (s := Finset.univ)
        (f := fun j : ι => Real.sqrt (absMatrix H i j))
        (g := fun j : ι => Real.sqrt (absMatrix H i j) * w j)
      have e1 : (∑ j : ι, Real.sqrt (absMatrix H i j) * (Real.sqrt (absMatrix H i j) * w j))
          = ∑ j : ι, absMatrix H i j * w j := by
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [← mul_assoc, Real.mul_self_sqrt (hAnonneg i j)]
      have e2 : (∑ j : ι, (Real.sqrt (absMatrix H i j)) ^ 2)
          = ∑ j : ι, absMatrix H i j := by
        refine Finset.sum_congr rfl fun j _ => ?_
        exact Real.sq_sqrt (hAnonneg i j)
      have e3 : (∑ j : ι, (Real.sqrt (absMatrix H i j) * w j) ^ 2)
          = ∑ j : ι, absMatrix H i j * (w j) ^ 2 := by
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [mul_pow, Real.sq_sqrt (hAnonneg i j)]
      have hav : (absMatrix H *ᵥ w) i = ∑ j, absMatrix H i j * w j := rfl
      rw [hav, ← e1, ← e2, ← e3]
      exact h
    calc ∑ i, ((absMatrix H *ᵥ w) i) ^ 2
        ≤ ∑ i, (∑ j, absMatrix H i j) * (∑ j, absMatrix H i j * (w j) ^ 2) :=
          Finset.sum_le_sum fun i _ => hcs i
      _ ≤ ∑ i, l1Norm H * (∑ j, absMatrix H i j * (w j) ^ 2) := by
          refine Finset.sum_le_sum fun i _ => ?_
          exact mul_le_mul_of_nonneg_right (absMatrix_rowSum_le_l1 H hH i)
            (Finset.sum_nonneg fun j _ => mul_nonneg (hAnonneg i j) (sq_nonneg _))
      _ = l1Norm H * ∑ i, ∑ j, absMatrix H i j * (w j) ^ 2 := by
          rw [Finset.mul_sum]
      _ = l1Norm H * ∑ j, (∑ i, absMatrix H i j) * (w j) ^ 2 := by
          congr 1
          rw [Finset.sum_comm]
          refine Finset.sum_congr rfl fun j _ => ?_
          rw [Finset.sum_mul]
      _ ≤ l1Norm H * (l1Norm H * ∑ j, (w j) ^ 2) := by
          refine mul_le_mul_of_nonneg_left ?_ hRnn
          rw [Finset.mul_sum]
          refine Finset.sum_le_sum fun j _ => ?_
          refine mul_le_mul_of_nonneg_right ?_ (sq_nonneg _)
          have hcol : ∑ i, absMatrix H i j = ∑ i, ‖H i j‖ := by
            refine Finset.sum_congr rfl fun i _ => rfl
          rw [hcol]
          exact Finset.le_sup' (fun j => ∑ x : ι, ‖H x j‖) (Finset.mem_univ j)
      _ = (l1Norm H) ^ 2 * ∑ j, (w j) ^ 2 := by ring
  have hsq : ‖(EuclideanSpace.equiv ι ℝ).symm (absMatrix H *ᵥ w)‖ ^ 2
      ≤ (l1Norm H * ‖v‖) ^ 2 := by
    rw [EuclideanSpace.norm_eq]
    rw [Real.sq_sqrt (Finset.sum_nonneg fun i _ => sq_nonneg _)]
    have hcoe : (∑ i, ‖((EuclideanSpace.equiv ι ℝ).symm (absMatrix H *ᵥ w)) i‖ ^ 2)
        = ∑ i, ((absMatrix H *ᵥ w) i) ^ 2 := by
      refine Finset.sum_congr rfl fun i _ => ?_
      simp [Real.norm_eq_abs, sq_abs]
    rw [hcoe, hwn, mul_pow, Real.sq_sqrt (Finset.sum_nonneg fun i _ => sq_nonneg _)]
    exact hmainsum
  have hRHSnn : 0 ≤ l1Norm H * ‖v‖ := mul_nonneg hRnn (norm_nonneg _)
  have hle := Real.sqrt_le_sqrt hsq
  rwa [Real.sqrt_sq (norm_nonneg _), Real.sqrt_sq hRHSnn] at hle

/-- The maximum column-sum norm is at most the square root of the dimension times the maximum
Euclidean column norm. -/
lemma l1Norm_le_sqrt_card_mul_mcnNorm (H : Matrix ι ι ℂ) :
    l1Norm H ≤ Real.sqrt (Fintype.card ι) * mcnNorm H := by
  refine Finset.sup'_le _ _ fun j _ => ?_
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq (s := Finset.univ)
    (f := fun _ : ι => (1 : ℝ)) (g := fun i : ι => ‖H i j‖)
  have h1 : (∑ i, ‖H i j‖) ^ 2 ≤ (Fintype.card ι : ℝ) * ∑ i, ‖H i j‖ ^ 2 := by
    have h2 : (∑ i ∈ Finset.univ, (1 : ℝ) * ‖H i j‖) ^ 2
        ≤ (∑ i ∈ Finset.univ, (1 : ℝ) ^ 2) * ∑ i ∈ Finset.univ, ‖H i j‖ ^ 2 := hcs
    simpa [Finset.sum_const, Finset.card_univ, nsmul_eq_mul] using h2
  have hcol : ∑ i, ‖H i j‖
      ≤ Real.sqrt (Fintype.card ι) * Real.sqrt (∑ i, ‖H i j‖ ^ 2) := by
    have hnn : 0 ≤ ∑ i, ‖H i j‖ := Finset.sum_nonneg fun _ _ => norm_nonneg _
    calc ∑ i, ‖H i j‖ = Real.sqrt ((∑ i, ‖H i j‖) ^ 2) := (Real.sqrt_sq hnn).symm
      _ ≤ Real.sqrt ((Fintype.card ι : ℝ) * ∑ i, ‖H i j‖ ^ 2) := Real.sqrt_le_sqrt h1
      _ = Real.sqrt (Fintype.card ι) * Real.sqrt (∑ i, ‖H i j‖ ^ 2) := by
          rw [Real.sqrt_mul (by positivity)]
  refine hcol.trans (mul_le_mul_of_nonneg_left ?_ (Real.sqrt_nonneg _))
  exact Finset.le_sup' (fun j => Real.sqrt (∑ i : ι, ‖H i j‖ ^ 2)) (Finset.mem_univ j)

/-- The square root of the dimension times the maximum Euclidean column norm is at most the
dimension times the maximum-entry norm. -/
lemma sqrt_card_mul_mcnNorm_le_card_mul_maxNorm (H : Matrix ι ι ℂ) :
    Real.sqrt (Fintype.card ι) * mcnNorm H ≤ (Fintype.card ι) * maxNorm H := by
  have hN : 0 ≤ (Fintype.card ι : ℝ) := by positivity
  have hmcn : mcnNorm H ≤ Real.sqrt (Fintype.card ι) * maxNorm H := by
    refine Finset.sup'_le _ _ fun j _ => ?_
    have hterm : ∀ i : ι, ‖H i j‖ ^ 2 ≤ (maxNorm H) ^ 2 := by
      intro i
      nlinarith [norm_nonneg (H i j), maxNorm_nonneg H, le_maxNorm H i j]
    have hsum : ∑ i, ‖H i j‖ ^ 2 ≤ (Fintype.card ι : ℝ) * (maxNorm H) ^ 2 := by
      calc ∑ i, ‖H i j‖ ^ 2 ≤ ∑ _i : ι, (maxNorm H) ^ 2 :=
            Finset.sum_le_sum fun i _ => hterm i
        _ = (Fintype.card ι : ℝ) * (maxNorm H) ^ 2 := by
            simp [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    calc Real.sqrt (∑ i, ‖H i j‖ ^ 2)
        ≤ Real.sqrt ((Fintype.card ι : ℝ) * (maxNorm H) ^ 2) := Real.sqrt_le_sqrt hsum
      _ = Real.sqrt (Fintype.card ι) * maxNorm H := by
          rw [Real.sqrt_mul hN, Real.sqrt_sq (maxNorm_nonneg H)]
  calc Real.sqrt (Fintype.card ι) * mcnNorm H
      ≤ Real.sqrt (Fintype.card ι) * (Real.sqrt (Fintype.card ι) * maxNorm H) :=
        mul_le_mul_of_nonneg_left hmcn (Real.sqrt_nonneg _)
    _ = (Fintype.card ι : ℝ) * maxNorm H := by
        rw [← mul_assoc, Real.mul_self_sqrt hN]

/-- For Hermitian `H`, the norms satisfy `maxNorm H ≤ mcnNorm H ≤ specNorm H ≤ specNorm
(absMatrix H) ≤ l1Norm H ≤ √N * mcnNorm H ≤ N * maxNorm H`, where `N` is the index
cardinality [ChildsKothari2010]. -/
theorem lemma1_norm_chain (H : Matrix ι ι ℂ) (hH : H.IsHermitian) :
    maxNorm H ≤ mcnNorm H ∧ mcnNorm H ≤ specNorm H ∧
    specNorm H ≤ specNorm (absMatrix H) ∧
    specNorm (absMatrix H) ≤ l1Norm H ∧
    l1Norm H ≤ Real.sqrt (Fintype.card ι) * mcnNorm H ∧
    Real.sqrt (Fintype.card ι) * mcnNorm H ≤ (Fintype.card ι) * maxNorm H :=
  ⟨maxNorm_le_mcnNorm H, mcnNorm_le_specNorm H, specNorm_le_specNorm_abs H,
   specNorm_abs_le_l1 H hH, l1Norm_le_sqrt_card_mul_mcnNorm H,
   sqrt_card_mul_mcnNorm_le_card_mul_maxNorm H⟩

/-- The maximum-entry norm of the identity matrix is one. -/
lemma maxNorm_one : maxNorm (1 : Matrix ι ι ℂ) = 1 := by
  obtain ⟨i₀⟩ := (inferInstance : Nonempty ι)
  refine le_antisymm ?_ ?_
  · refine Finset.sup'_le _ _ fun i _ => Finset.sup'_le _ _ fun j _ => ?_
    rw [Matrix.one_apply]
    split_ifs <;> simp
  · have h := le_maxNorm (1 : Matrix ι ι ℂ) i₀ i₀
    simpa using h

/-- The maximum Euclidean column norm of the identity matrix is one. -/
lemma mcnNorm_one : mcnNorm (1 : Matrix ι ι ℂ) = 1 := by
  obtain ⟨j₀⟩ := (inferInstance : Nonempty ι)
  have hsum : ∀ j : ι, ∑ i, ‖(1 : Matrix ι ι ℂ) i j‖ ^ 2 = 1 := by
    intro j
    rw [Fintype.sum_eq_single j]
    · simp
    · intro b hb
      rw [Matrix.one_apply]
      simp [hb]
  refine le_antisymm ?_ ?_
  · refine Finset.sup'_le _ _ fun j _ => ?_
    rw [hsum j, Real.sqrt_one]
  · have h := Finset.le_sup' (fun j => Real.sqrt (∑ i : ι, ‖(1 : Matrix ι ι ℂ) i j‖ ^ 2))
      (Finset.mem_univ j₀)
    rw [hsum j₀, Real.sqrt_one] at h
    exact h

/-- The spectral norm of the identity matrix over a real or complex scalar field is one. -/
lemma specNorm_one {𝕜 : Type*} [RCLike 𝕜] : specNorm (1 : Matrix ι ι 𝕜) = 1 := by
  rw [specNorm_eq_l2', ← Matrix.l2_opNorm_toEuclideanCLM]
  have h : ⇑(Matrix.toEuclideanCLM (n := ι) (𝕜 := 𝕜)) (1 : Matrix ι ι 𝕜) = 1 := map_one _
  rw [h]
  exact norm_one

/-- The entrywise absolute-value matrix of the complex identity is the real identity. -/
lemma absMatrix_one : absMatrix (1 : Matrix ι ι ℂ) = (1 : Matrix ι ι ℝ) := by
  ext i j
  rw [absMatrix, Matrix.one_apply, Matrix.one_apply]
  split_ifs <;> simp

/-- The spectral norm of the entrywise absolute-value matrix of the identity is one. -/
lemma specNorm_abs_one : specNorm (absMatrix (1 : Matrix ι ι ℂ)) = 1 := by
  rw [absMatrix_one]
  exact specNorm_one

/-- The maximum-entry, maximum-column, spectral, and entrywise-absolute spectral norms of the
identity matrix are all one [ChildsKothari2010]. -/
theorem lemma1_tight_identity :
    maxNorm (1 : Matrix ι ι ℂ) = 1 ∧ mcnNorm (1 : Matrix ι ι ℂ) = 1 ∧
    specNorm (1 : Matrix ι ι ℂ) = 1 ∧ specNorm (absMatrix (1 : Matrix ι ι ℂ)) = 1 :=
  ⟨maxNorm_one, mcnNorm_one, specNorm_one, specNorm_abs_one⟩

/-- The maximum-entry norm of the all-ones matrix is one. -/
lemma maxNorm_const_one : maxNorm (fun _ _ : ι => (1 : ℂ)) = 1 := by
  refine le_antisymm ?_ ?_
  · refine Finset.sup'_le _ _ fun i _ => Finset.sup'_le _ _ fun j _ => ?_
    simp
  · obtain ⟨i₀⟩ := (inferInstance : Nonempty ι)
    have h := le_maxNorm (fun _ _ : ι => (1 : ℂ)) i₀ i₀
    simpa using h

/-- The maximum Euclidean column norm of the all-ones matrix is the square root of the index
cardinality. -/
lemma mcnNorm_const_one :
    mcnNorm (fun _ _ : ι => (1 : ℂ)) = Real.sqrt (Fintype.card ι) := by
  have hcol : ∀ j : ι, ∑ i, ‖(fun _ _ : ι => (1 : ℂ)) i j‖ ^ 2 = (Fintype.card ι : ℝ) := by
    intro j
    simp [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  refine le_antisymm ?_ ?_
  · refine Finset.sup'_le _ _ fun j _ => ?_
    rw [hcol j]
  · obtain ⟨j₀⟩ := (inferInstance : Nonempty ι)
    have h := Finset.le_sup'
      (fun j => Real.sqrt (∑ i : ι, ‖(fun _ _ : ι => (1 : ℂ)) i j‖ ^ 2))
      (Finset.mem_univ j₀)
    rwa [hcol j₀] at h

/-- The maximum column-sum norm of the all-ones matrix equals the index cardinality. -/
lemma l1Norm_const_one : l1Norm (fun _ _ : ι => (1 : ℂ)) = (Fintype.card ι : ℝ) := by
  have hcol : ∀ j : ι, ∑ i, ‖(fun _ _ : ι => (1 : ℂ)) i j‖ = (Fintype.card ι : ℝ) := by
    intro j
    simp [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  refine le_antisymm ?_ ?_
  · refine Finset.sup'_le _ _ fun j _ => ?_
    rw [hcol j]
  · obtain ⟨j₀⟩ := (inferInstance : Nonempty ι)
    have h := Finset.le_sup' (fun j => ∑ i : ι, ‖(fun _ _ : ι => (1 : ℂ)) i j‖)
      (Finset.mem_univ j₀)
    rwa [hcol j₀] at h

/-- For the all-ones matrix in dimension `N`, the column-sum, maximum-column, and maximum-entry
norms are `N`, `√N`, and one, respectively [ChildsKothari2010]. -/
theorem lemma1_tight_allOnes :
    l1Norm (fun _ _ : ι => (1 : ℂ)) = (Fintype.card ι : ℝ) ∧
    mcnNorm (fun _ _ : ι => (1 : ℂ)) = Real.sqrt (Fintype.card ι) ∧
    maxNorm (fun _ _ : ι => (1 : ℂ)) = 1 :=
  ⟨l1Norm_const_one, mcnNorm_const_one, maxNorm_const_one⟩

end Qatlib.Papers.NonSparseHam09.MainResults
