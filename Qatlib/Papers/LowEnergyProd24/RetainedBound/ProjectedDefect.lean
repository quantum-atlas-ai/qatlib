/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.LowEnergyProd24.RetainedBound.Duhamel

/-!
# Projected defect and retained kernel bounds

This module inserts complementary energy projectors between the defect and the product word. The
resulting bounds separate a compressed defect from a defect norm multiplied by leakage,
providing the pointwise estimates for the retained-error integral in [HejaziZiniArrazola2024].

## Main statements

* `actual_projected_defect_bound`: Splits the projected defect-product norm into retained and
  leakage contributions.
* `actual_retained_kernel_bound`: Applies the same estimate to the Duhamel kernel.

## References

* [Hejazi et al., 2024][HejaziZiniArrazola2024]
-/

set_option warningAsError false

set_option autoImplicit false
set_option maxHeartbeats 250000
noncomputable section
open Matrix
open scoped Classical BigOperators Matrix.Norms.L2Operator MatrixOrder ComplexOrder
namespace Qatlib.Papers.LowEnergyProd24.RetainedBound
open Qatlib.Papers.LowEnergyProd24.LocalModel
open Qatlib.Papers.LowEnergyProd24.ProductError
open Qatlib.Foundations.MatrixGeometry.SpectralCutoff
variable {N R M k d : ℕ} {J : ℝ}

/-- The defect-product word between cutoffs `Λ` and `Δ` is bounded by the defect compressed at
`Λ` plus the defect norm times product-word leakage above `Λ`. -/
theorem actual_projected_defect_bound (h : Hamiltonian N R M k d J)
    (stages : List (ℝ × Fin M)) (t Δ Λ : ℝ) :
    ‖low h.total h.total_hermitian Λ*defect h stages t*approximate h stages t*low h.total h.total_hermitian Δ‖ ≤
      ‖low h.total h.total_hermitian Λ*defect h stages t*low h.total h.total_hermitian Λ‖+
      ‖defect h stages t‖*‖high h.total h.total_hermitian Λ*approximate h stages t*low h.total h.total_hermitian Δ‖ := by
  let P := low h.total h.total_hermitian Λ
  let Q := high h.total h.total_hermitian Λ
  let S := low h.total h.total_hermitian Δ
  let D := defect h stages t
  let W := approximate h stages t
  have hQ : Q*Q=Q := high_square _ _ _
  have he : P*D*W*S=(P*D*P)*W*S+(P*D*Q)*(Q*W*S) := by
    calc
      _ = (P*D*P)*W*S+P*D*Q*W*S := by dsimp only [Q, high]; noncomm_ring
      _ = _ := by
        calc
          _ = (P*D*P)*W*S+P*D*(Q*Q)*W*S := by rw [hQ]
          _ = _ := by noncomm_ring
  have hfirst : ‖(P*D*P)*W*S‖ ≤ ‖P*D*P‖ := by
    calc
      _ ≤ ‖(P*D*P)*W‖*‖S‖ := norm_mul_le _ _
      _ = ‖P*D*P‖*‖S‖ := by rw [CStarRing.norm_mul_mem_unitary _ (approximate_unitary h stages t)]
      _ ≤ ‖P*D*P‖*1 := mul_le_mul_of_nonneg_left (low_norm _ _ _) (norm_nonneg _)
      _ = _ := mul_one _
  have hmixed : ‖P*D*Q‖ ≤ ‖D‖ := by
    calc
      _ ≤ (‖P‖*‖D‖)*‖Q‖ := (norm_mul_le _ _).trans (mul_le_mul_of_nonneg_right (norm_mul_le _ _) (norm_nonneg _))
      _ ≤ (1*‖D‖)*1 := by
        have hP : ‖P‖ ≤ 1 := low_norm h.total h.total_hermitian Λ
        have hQn : ‖Q‖ ≤ 1 := high_norm h.total h.total_hermitian Λ
        exact mul_le_mul (mul_le_mul_of_nonneg_right hP (norm_nonneg D)) hQn (norm_nonneg Q)
            (by positivity)
      _ = _ := by ring
  change ‖P*D*W*S‖ ≤ ‖P*D*P‖+‖D‖*‖Q*W*S‖
  rw [he]
  exact (norm_add_le _ _).trans (add_le_add hfirst
    ((norm_mul_le _ _).trans (mul_le_mul_of_nonneg_right hmixed (norm_nonneg _))))

/-- The projected Duhamel kernel is bounded by the compressed defect norm plus the defect norm
times leakage, with exact evolution contributing no additional norm factor. -/
theorem actual_retained_kernel_bound (h : Hamiltonian N R M k d J)
    (stages : List (ℝ × Fin M)) (t s Δ Λ : ℝ) :
    ‖low h.total h.total_hermitian Λ*(evolve h.total (t-s)*defect h stages s*approximate h stages s)*low h.total h.total_hermitian Δ‖ ≤
      ‖low h.total h.total_hermitian Λ*defect h stages s*low h.total h.total_hermitian Λ‖+
      ‖defect h stages s‖*‖high h.total h.total_hermitian Λ*approximate h stages s*low h.total h.total_hermitian Δ‖ := by
  let P := low h.total h.total_hermitian Λ
  let S := low h.total h.total_hermitian Δ
  let U := evolve h.total (t-s)
  let D := defect h stages s
  let W := approximate h stages s
  have hc : U*P=P*U := (evolve_low_commute h.total h.total_hermitian (t-s) Λ).eq
  have he : P*(U*D*W)*S=U*(P*D*W*S) := by
    calc
      _ = (P*U)*(D*W*S) := by noncomm_ring
      _ = _ := by rw [← hc]; noncomm_ring
  change ‖P*(U*D*W)*S‖ ≤ _
  rw [he, CStarRing.norm_mem_unitary_mul _ (evolve_unitary _ h.total_hermitian (t-s))]
  exact actual_projected_defect_bound h stages s Δ Λ
end Qatlib.Papers.LowEnergyProd24.RetainedBound
