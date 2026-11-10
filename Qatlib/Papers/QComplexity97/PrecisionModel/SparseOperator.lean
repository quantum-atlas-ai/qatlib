/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Tactic

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.QComplexity97.PrecisionModel

open Matrix
open scoped Matrix.Norms.L2Operator

theorem sparse_opNorm_le {ι : Type*} [Fintype ι] [DecidableEq ι]
    (M : Matrix ι ι ℂ) {ε : ℝ} (hε : 0 ≤ ε) (N : ℕ)
    (hentry : ∀ i j, ‖M i j‖ ≤ ε)
    (hrows : ∀ j, (Finset.univ.filter (fun i => M j i ≠ 0)).card ≤ N)
    (hcols : ∀ i, (Finset.univ.filter (fun j => M j i ≠ 0)).card ≤ N) :
    ‖M‖ ≤ (N : ℝ) * ε := by
  classical
  rw [Matrix.cstar_norm_def]
  refine ContinuousLinearMap.opNorm_le_bound _
    (mul_nonneg (Nat.cast_nonneg N) hε) (fun x => ?_)
  have hxi : ∀ j, (Matrix.toEuclideanCLM (n := ι) (𝕜 := ℂ) M x) j =
      ∑ i, M j i * x i := by
    intro j
    have hx := congrFun (Matrix.ofLp_toEuclideanCLM (n := ι) M x) j
    simp only [Matrix.mulVec, dotProduct] at hx
    exact hx

  have hcoord : ∀ j, ‖(Matrix.toEuclideanCLM (n := ι) (𝕜 := ℂ) M x) j‖ ^ 2 ≤
      (N : ℝ) * ∑ i, ‖M j i‖ ^ 2 * ‖x i‖ ^ 2 := by
    intro j
    set s : Finset ι := Finset.univ.filter (fun i => M j i ≠ 0) with hs
    have hsum : ∑ i ∈ s, M j i * x i = ∑ i, M j i * x i := by
      refine Finset.sum_subset (Finset.filter_subset _ _) ?_
      intro i _ hi
      have hi0 : M j i = 0 := by
        have hni : ¬ (M j i ≠ 0) := by
          intro h; exact hi (by simp [hs, h])
        simpa using hni
      simp [hi0]
    have hcard : (s.card : ℝ) ≤ (N : ℝ) := by exact_mod_cast hrows j
    calc ‖(Matrix.toEuclideanCLM (n := ι) (𝕜 := ℂ) M x) j‖ ^ 2
        = ‖∑ i ∈ s, M j i * x i‖ ^ 2 := by rw [hxi j, ← hsum]
      _ ≤ (∑ i ∈ s, ‖M j i * x i‖) ^ 2 := by
          exact pow_le_pow_left₀ (norm_nonneg _) (norm_sum_le _ _) 2
      _ = (∑ i ∈ s, ‖M j i‖ * ‖x i‖) ^ 2 := by simp
      _ ≤ (s.card : ℝ) * ∑ i ∈ s, (‖M j i‖ * ‖x i‖) ^ 2 :=
          sq_sum_le_card_mul_sum_sq
      _ ≤ (N : ℝ) * ∑ i ∈ s, (‖M j i‖ * ‖x i‖) ^ 2 := by
          have hsq : (0 : ℝ) ≤ ∑ i ∈ s, (‖M j i‖ * ‖x i‖) ^ 2 := by positivity
          exact mul_le_mul_of_nonneg_right hcard hsq
      _ = (N : ℝ) * ∑ i ∈ s, ‖M j i‖ ^ 2 * ‖x i‖ ^ 2 := by
          congr 1
          refine Finset.sum_congr rfl fun i _ => ?_
          ring
      _ ≤ (N : ℝ) * ∑ i, ‖M j i‖ ^ 2 * ‖x i‖ ^ 2 := by
          have hle : (0 : ℝ) ≤ (N : ℝ) := Nat.cast_nonneg N
          have hmono : ∑ i ∈ s, ‖M j i‖ ^ 2 * ‖x i‖ ^ 2 ≤
              ∑ i, ‖M j i‖ ^ 2 * ‖x i‖ ^ 2 :=
            Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
              (fun i _ _ => by positivity)
          exact mul_le_mul_of_nonneg_left hmono hle

  have hcol : ∀ i, ∑ j, ‖M j i‖ ^ 2 ≤ (N : ℝ) * ε ^ 2 := by
    intro i
    set t : Finset ι := Finset.univ.filter (fun j => M j i ≠ 0) with ht
    have hsum : ∑ j ∈ t, ‖M j i‖ ^ 2 = ∑ j, ‖M j i‖ ^ 2 := by
      refine Finset.sum_subset (Finset.filter_subset _ _) ?_
      intro j _ hj
      have hj0 : M j i = 0 := by
        have hni : ¬ (M j i ≠ 0) := by
          intro h; exact hj (by simp [ht, h])
        simpa using hni
      simp [hj0]
    have hcard : (t.card : ℝ) ≤ (N : ℝ) := by exact_mod_cast hcols i
    rw [← hsum]
    calc ∑ j ∈ t, ‖M j i‖ ^ 2 ≤ ∑ j ∈ t, ε ^ 2 := by
          refine Finset.sum_le_sum fun j _ => ?_
          exact pow_le_pow_left₀ (norm_nonneg _) (hentry j i) 2
      _ = (t.card : ℝ) * ε ^ 2 := by simp [Finset.sum_const]
      _ ≤ (N : ℝ) * ε ^ 2 := by
          exact mul_le_mul_of_nonneg_right hcard (by positivity)

  have hsq : ‖Matrix.toEuclideanCLM (n := ι) (𝕜 := ℂ) M x‖ ^ 2 ≤
      ((N : ℝ) * ε * ‖x‖) ^ 2 := by
    rw [EuclideanSpace.norm_sq_eq]
    calc ∑ j, ‖(Matrix.toEuclideanCLM (n := ι) (𝕜 := ℂ) M x) j‖ ^ 2
        ≤ ∑ j, (N : ℝ) * ∑ i, ‖M j i‖ ^ 2 * ‖x i‖ ^ 2 :=
          Finset.sum_le_sum fun j _ => hcoord j
      _ = (N : ℝ) * ∑ i, ‖x i‖ ^ 2 * (∑ j, ‖M j i‖ ^ 2) := by
          rw [← Finset.mul_sum, Finset.sum_comm]
          congr 1
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun j _ => ?_
          ring
      _ ≤ (N : ℝ) * ∑ i, ‖x i‖ ^ 2 * ((N : ℝ) * ε ^ 2) := by
          have hle : (0 : ℝ) ≤ (N : ℝ) := Nat.cast_nonneg N
          refine mul_le_mul_of_nonneg_left ?_ hle
          refine Finset.sum_le_sum fun i _ => ?_
          exact mul_le_mul_of_nonneg_left (hcol i) (by positivity)
      _ = ((N : ℝ) * ε) ^ 2 * ∑ i, ‖x i‖ ^ 2 := by
          rw [← Finset.sum_mul]
          ring
      _ = ((N : ℝ) * ε * ‖x‖) ^ 2 := by
          rw [show ∑ i, ‖x.ofLp i‖ ^ 2 = ‖x‖ ^ 2 from
            (EuclideanSpace.norm_sq_eq x).symm]
          ring
  have hnonneg : (0 : ℝ) ≤ ‖Matrix.toEuclideanCLM (n := ι) (𝕜 := ℂ) M x‖ :=
    norm_nonneg _
  have hrhs : (0 : ℝ) ≤ (N : ℝ) * ε * ‖x‖ :=
    mul_nonneg (mul_nonneg (Nat.cast_nonneg N) hε) (norm_nonneg _)
  exact (sq_le_sq₀ hnonneg hrhs).mp hsq

end Qatlib.Papers.QComplexity97.PrecisionModel
