/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Foundations.OperatorErrors.OperatorError

/-!
# Matrix product perturbation estimates

`segment_product_perturbation_sandwich` bounds the difference of finite matrix products by
weighted local differences. When all factors are contractions,
`segment_product_perturbation_contraction_sum` reduces this to the sum of the local errors.
These estimates support the interaction-picture simulation analysis of [LowWiebe2018].

## Main statements

* `segment_product_perturbation_sandwich`: the weighted local-error estimate.
* `segment_product_perturbation_contraction_sum`: the contraction specialization.

## References

* [Low and Wiebe, 2018][LowWiebe2018]
-/

set_option warningAsError false

open Qatlib.Foundations.OperatorErrors.OperatorError

set_option autoImplicit false

namespace Qatlib.Concepts.InteractionEvo.SegmentProduct

open scoped BigOperators Matrix.Norms.L2Operator

/-- Bounds the operator norm of a matrix product indexed by `List.range M` by the product of the
individual operator norms. -/
private theorem segment_range_norm_prod_le {I : Type} [Fintype I] [DecidableEq I]
    (g : ℕ → Matrix I I ℂ) (M : ℕ) :
    ‖((List.range M).map g).prod‖ ≤ ∏ j ∈ Finset.range M, ‖g j‖ := by
  induction M with
  | zero => simpa using (l2_norm_one_le (I := I))
  | succ M ih =>
    simp only [List.range_succ, List.map_append, List.map_cons, List.map_nil,
      List.prod_append, List.prod_cons, List.prod_nil, mul_one, Finset.prod_range_succ]
    exact (norm_mul_le _ _).trans (mul_le_mul_of_nonneg_right ih (norm_nonneg _))

/-- Bounds the difference of two finite matrix products by the sum of local differences weighted
by products of the indicated surrounding factor norms. -/
theorem segment_product_perturbation_sandwich
    (I : Type) [Fintype I] [DecidableEq I] (f g : ℕ → Matrix I I ℂ) (M : ℕ) :
    ‖((List.range M).map f).prod - ((List.range M).map g).prod‖ ≤
      ∑ k ∈ Finset.range M,
        (∏ j ∈ Finset.filter (fun j => k < j) (Finset.range M), ‖f j‖) *
        ‖f k - g k‖ *
        (∏ j ∈ Finset.filter (fun j => j < k) (Finset.range M), ‖g j‖) := by
  classical
  induction M with
  | zero => simp
  | succ M ih =>
    let term (m k : ℕ) : ℝ :=
      (∏ j ∈ (Finset.range m).filter (fun j => k < j), ‖f j‖) *
      ‖f k - g k‖ * (∏ j ∈ (Finset.range m).filter (fun j => j < k), ‖g j‖)
    change ‖((List.range (M + 1)).map f).prod - ((List.range (M + 1)).map g).prod‖ ≤
      ∑ k ∈ Finset.range (M + 1), term (M + 1) k
    have hstep (k : ℕ) (hk : k ∈ Finset.range M) :
        term (M + 1) k = term M k * ‖f M‖ := by
      have hkm : k < M := Finset.mem_range.mp hk
      have hsuffix : (Finset.range (M + 1)).filter (fun j => k < j) =
          insert M ((Finset.range M).filter (fun j => k < j)) := by
        ext j
        simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_insert]
        omega
      have hprefix : (Finset.range (M + 1)).filter (fun j => j < k) =
          (Finset.range M).filter (fun j => j < k) := by
        ext j
        simp only [Finset.mem_filter, Finset.mem_range]
        omega
      dsimp [term]
      rw [hsuffix, hprefix, Finset.prod_insert (by simp)]
      ring
    have hend : term (M + 1) M =
        (∏ j ∈ Finset.range M, ‖g j‖) * ‖f M - g M‖ := by
      have hsuffix : (Finset.range (M + 1)).filter (fun j => M < j) = ∅ := by
        ext j
        simp only [Finset.mem_filter, Finset.mem_range, Finset.notMem_empty, iff_false]
        omega
      have hprefix : (Finset.range (M + 1)).filter (fun j => j < M) = Finset.range M := by
        ext j
        simp only [Finset.mem_filter, Finset.mem_range]
        omega
      simp only [term, hsuffix, hprefix, Finset.prod_empty, one_mul]
      ring
    have hrhs : (∑ k ∈ Finset.range (M + 1), term (M + 1) k) =
        (∑ k ∈ Finset.range M, term M k) * ‖f M‖ +
          (∏ j ∈ Finset.range M, ‖g j‖) * ‖f M - g M‖ := by
      rw [Finset.sum_range_succ, hend, Finset.sum_mul]
      congr 1
      exact Finset.sum_congr rfl hstep
    rw [hrhs]
    simp only [List.range_succ, List.map_append, List.map_cons, List.map_nil,
      List.prod_append, List.prod_cons, List.prod_nil, mul_one]
    exact (l2_norm_mul_sub_mul_le _ _ _ _).trans
      (add_le_add (mul_le_mul_of_nonneg_right ih (norm_nonneg _))
        (mul_le_mul_of_nonneg_right (segment_range_norm_prod_le g M) (norm_nonneg _)))

/-- For two sequences of contractions, bounds the norm of the difference of their first `M`
products by the sum of their first `M` factorwise differences. -/
theorem segment_product_perturbation_contraction_sum
    (I : Type) [Fintype I] [DecidableEq I] (f g : ℕ → Matrix I I ℂ) (M : ℕ)
    (hf : ∀ j < M, ‖f j‖ ≤ 1) (hg : ∀ j < M, ‖g j‖ ≤ 1) :
    ‖((List.range M).map f).prod - ((List.range M).map g).prod‖ ≤
      ∑ k ∈ Finset.range M, ‖f k - g k‖ := by
  classical
  refine (segment_product_perturbation_sandwich I f g M).trans ?_
  apply Finset.sum_le_sum
  intro k _
  have hleft : (∏ j ∈ (Finset.range M).filter (fun j => k < j), ‖f j‖) ≤ 1 :=
    Finset.prod_le_one₀ (fun _ _ => norm_nonneg _)
      (fun j hj => hf j (Finset.mem_range.mp (Finset.mem_filter.mp hj).1))
  have hright : (∏ j ∈ (Finset.range M).filter (fun j => j < k), ‖g j‖) ≤ 1 :=
    Finset.prod_le_one₀ (fun _ _ => norm_nonneg _)
      (fun j hj => hg j (Finset.mem_range.mp (Finset.mem_filter.mp hj).1))
  have hfirst := mul_le_mul_of_nonneg_right hleft (norm_nonneg (f k - g k))
  have hsecond := mul_le_mul_of_nonneg_left hright (norm_nonneg (f k - g k))
  calc
    _ ≤ ‖f k - g k‖ *
        (∏ j ∈ (Finset.range M).filter (fun j => j < k), ‖g j‖) := by
      simpa only [one_mul] using mul_le_mul_of_nonneg_right hfirst
        (Finset.prod_nonneg (fun _ _ => norm_nonneg _))
    _ ≤ ‖f k - g k‖ := by simpa only [mul_one] using hsecond

end Qatlib.Concepts.InteractionEvo.SegmentProduct
