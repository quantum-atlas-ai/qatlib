/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Analysis.Normed.Operator.Basic
import Mathlib.Analysis.Complex.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

set_option backward.isDefEq.respectTransparency false

/-!
# Additive error of a chronological contraction product

Fixed arXiv:2610.08714v1, Corollary 4.4 (printed p.30, Section 4.3).  If the
`t`-th implemented query block differs from the ideal designated block by at
most `η_t`, the exact-known-gate circuit differs from the ideal product by at
most `∑_t η_t`.  The proof is the product telescope used in the paper: peel off
the last contraction and charge the defect of that layer.

The statement isolates the operator-norm telescope.  The second term `ε_g` for
the synthesis of the known gates and the concrete oracle/label construction are
not part of this module.
-/

set_option autoImplicit false
noncomputable section

open scoped BigOperators

namespace Qatlib.Papers.PolyTransform26.ResidualCert

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

/-- The chronological product of layers `A 0`, then `A 1`, …, then `A (N-1)`. -/
noncomputable def queryProduct (A : ℕ → E →L[ℂ] E) : ℕ → E →L[ℂ] E
  | 0 => 1
  | n + 1 => (A n).comp (queryProduct A n)

/-- The empty chronological product is the identity. -/
@[simp]
theorem queryProduct_zero (A : ℕ → E →L[ℂ] E) : queryProduct A 0 = 1 := rfl

/-- A chronological product prepends the newest layer on the left. -/
@[simp]
theorem queryProduct_succ (A : ℕ → E →L[ℂ] E) (n : ℕ) :
    queryProduct A (n + 1) = (A n).comp (queryProduct A n) := rfl

/-- A product of contractions is a contraction. -/
theorem queryProduct_norm_le_one (A : ℕ → E →L[ℂ] E)
    (hA : ∀ t, ‖A t‖ ≤ 1) (N : ℕ) : ‖queryProduct A N‖ ≤ 1 := by
  induction N with
  | zero =>
      refine ContinuousLinearMap.opNorm_le_bound _ zero_le_one ?_
      intro x
      simp
  | succ n ih =>
      rw [queryProduct_succ]
      calc
        ‖(A n).comp (queryProduct A n)‖ ≤
            ‖A n‖ * ‖queryProduct A n‖ :=
          ContinuousLinearMap.opNorm_comp_le _ _
        _ ≤ 1 * 1 :=
          mul_le_mul (hA n) ih (norm_nonneg _) (by positivity)
        _ = 1 := by ring

/-- Corollary 4.4, operator-norm telescope: replacing every contraction in a
chronological product perturbs the product by at most the sum of the layer
defects. -/
theorem query_product_error_le (A B : ℕ → E →L[ℂ] E)
    (hA : ∀ t, ‖A t‖ ≤ 1) (hB : ∀ t, ‖B t‖ ≤ 1) (N : ℕ) :
    ‖queryProduct A N - queryProduct B N‖ ≤
      ∑ t ∈ Finset.range N, ‖A t - B t‖ := by
  induction N with
  | zero => simp
  | succ n ih =>
      rw [queryProduct_succ, queryProduct_succ]
      have hdecomp :
          (A n).comp (queryProduct A n) - (B n).comp (queryProduct B n) =
            (A n).comp (queryProduct A n - queryProduct B n) +
              (A n - B n).comp (queryProduct B n) := by
        ext x
        simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.sub_apply,
          ContinuousLinearMap.add_apply, map_sub]
        abel
      rw [hdecomp]
      have h1 : ‖(A n).comp (queryProduct A n - queryProduct B n)‖ ≤
          ‖queryProduct A n - queryProduct B n‖ := by
        calc
          ‖(A n).comp (queryProduct A n - queryProduct B n)‖ ≤
              ‖A n‖ * ‖queryProduct A n - queryProduct B n‖ :=
            ContinuousLinearMap.opNorm_comp_le _ _
          _ ≤ 1 * ‖queryProduct A n - queryProduct B n‖ :=
            mul_le_mul_of_nonneg_right (hA n) (norm_nonneg _)
          _ = ‖queryProduct A n - queryProduct B n‖ := one_mul _
      have h2 : ‖(A n - B n).comp (queryProduct B n)‖ ≤ ‖A n - B n‖ := by
        calc
          ‖(A n - B n).comp (queryProduct B n)‖ ≤
              ‖A n - B n‖ * ‖queryProduct B n‖ :=
            ContinuousLinearMap.opNorm_comp_le _ _
          _ ≤ ‖A n - B n‖ * 1 :=
            mul_le_mul_of_nonneg_left
              (queryProduct_norm_le_one B hB n) (norm_nonneg _)
          _ = ‖A n - B n‖ := mul_one _
      calc
        ‖(A n).comp (queryProduct A n - queryProduct B n) +
            (A n - B n).comp (queryProduct B n)‖ ≤
            ‖(A n).comp (queryProduct A n - queryProduct B n)‖ +
              ‖(A n - B n).comp (queryProduct B n)‖ := norm_add_le _ _
        _ ≤ ‖queryProduct A n - queryProduct B n‖ + ‖A n - B n‖ :=
          add_le_add h1 h2
        _ ≤ (∑ t ∈ Finset.range n, ‖A t - B t‖) + ‖A n - B n‖ :=
          add_le_add ih le_rfl
        _ = ∑ t ∈ Finset.range (n + 1), ‖A t - B t‖ := by
          rw [Finset.sum_range_succ]

/-- Corollary 4.4 with a uniform per-query defect: `Q` layers give total
operator-norm error at most `Q η`. -/
theorem query_product_error_le_uniform (A B : ℕ → E →L[ℂ] E)
    (hA : ∀ t, ‖A t‖ ≤ 1) (hB : ∀ t, ‖B t‖ ≤ 1) (N : ℕ) (η : ℝ)
    (hη : ∀ t, ‖A t - B t‖ ≤ η) :
    ‖queryProduct A N - queryProduct B N‖ ≤ (N : ℝ) * η := by
  calc
    ‖queryProduct A N - queryProduct B N‖ ≤
        ∑ t ∈ Finset.range N, ‖A t - B t‖ :=
      query_product_error_le A B hA hB N
    _ ≤ ∑ _t ∈ Finset.range N, η :=
      Finset.sum_le_sum fun t _ => hη t
    _ = (N : ℝ) * η := by
      rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]

/-- Corollary 4.4 with an additional exact-known-gate synthesis error `εg`:
the total selected-block error is at most the sum of the per-query submatrix
defects plus `εg`, exactly the second sentence of the corollary. -/
theorem query_product_error_le_with_gate_error (A B : ℕ → E →L[ℂ] E)
    (hA : ∀ t, ‖A t‖ ≤ 1) (hB : ∀ t, ‖B t‖ ≤ 1) (N : ℕ) (εg : ℝ)
    (hεg : 0 ≤ εg) :
    ‖queryProduct A N - queryProduct B N‖ ≤
      (∑ t ∈ Finset.range N, ‖A t - B t‖) + εg := by
  linarith [query_product_error_le A B hA hB N]

/-- Corollary 4.4 in the uniform form stated in the paper: per-query defect at
most `ηo` and known-gate synthesis error `εg` give total error at most
`Q ηo + εg`. -/
theorem query_product_error_le_uniform_gate (A B : ℕ → E →L[ℂ] E)
    (hA : ∀ t, ‖A t‖ ≤ 1) (hB : ∀ t, ‖B t‖ ≤ 1) (N : ℕ) (ηo εg : ℝ)
    (hη : ∀ t, ‖A t - B t‖ ≤ ηo) (hεg : 0 ≤ εg) :
    ‖queryProduct A N - queryProduct B N‖ ≤ (N : ℝ) * ηo + εg := by
  linarith [query_product_error_le_uniform A B hA hB N ηo hη]

end Qatlib.Papers.PolyTransform26.ResidualCert
