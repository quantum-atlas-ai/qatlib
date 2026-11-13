/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.LowEnergyProd24.ProductError.ActualWord

/-!
# Spectral splitting and state-tail error bounds

This module separates error on a low-energy input sector into a retained output part and a
high-energy leakage part. For product words, `actual_state_tail_bound` combines repeated-step
error control with the actual high-energy component of a normalized input state, following
[HejaziZiniArrazola2024].

## Main statements

* `actual_error_sector_split`: Splits restricted error at a larger output cutoff.
* `actual_state_tail_bound`: Bounds state error by repeated low-energy error and twice the input
  tail norm.

## References

* [Hejazi et al., 2024][HejaziZiniArrazola2024]
-/

set_option autoImplicit false
set_option maxHeartbeats 200000
noncomputable section
open Matrix
open scoped Classical BigOperators Matrix.Norms.L2Operator MatrixOrder ComplexOrder
namespace Qatlib.Papers.LowEnergyProd24.RetainedBound
open Qatlib.Papers.LowEnergyProd24.LocalModel
open Qatlib.Papers.LowEnergyProd24.ProductError
open Qatlib.Foundations.MatrixGeometry.SpectralCutoff
variable {N R M k d : ℕ} {J : ℝ}

/-- For `Δ ≤ Λ`, the error of any matrix approximation on the input sector below `Δ` is bounded
by its retained error below `Λ` plus leakage above `Λ`. -/
theorem actual_error_sector_split (h : Hamiltonian N R M k d J) (W : Matrix (Register N) (Register N) ℂ)
    (t Δ Λ : ℝ) (hΔ : Δ ≤ Λ) :
    ‖(W-evolve h.total t)*low h.total h.total_hermitian Δ‖ ≤
      ‖low h.total h.total_hermitian Λ*(W-evolve h.total t)*low h.total h.total_hermitian Δ‖+
      ‖high h.total h.total_hermitian Λ*W*low h.total h.total_hermitian Δ‖ := by
  have he : (W-evolve h.total t)*low h.total h.total_hermitian Δ =
      low h.total h.total_hermitian Λ*(W-evolve h.total t)*low h.total h.total_hermitian Δ+
      high h.total h.total_hermitian Λ*W*low h.total h.total_hermitian Δ := by
    have hz := evolve_no_leak h.total h.total_hermitian t Δ Λ hΔ
    calc
      _ = low h.total h.total_hermitian Λ*(W-evolve h.total t)*low h.total h.total_hermitian Δ+
          high h.total h.total_hermitian Λ*(W-evolve h.total t)*low h.total h.total_hermitian Δ := by
        simp only [high]
        noncomm_ring
      _ = _ := by simp only [mul_sub, sub_mul, hz, sub_zero]
  rw [he]
  exact norm_add_le _ _

/-- For a unit vector, the error after `r` product-word powers is at most `r` times the one-step
low-energy operator error plus twice the high-energy tail norm. -/
theorem actual_state_tail_bound (h : Hamiltonian N R M k d J) (stages : List (ℝ × Fin M))
    (t Δ : ℝ) (r : ℕ) (ψ : EuclideanSpace ℂ (Register N)) (hψ : ‖ψ‖=1) :
    ‖(Matrix.toEuclideanCLM (n := Register N) (𝕜 := ℂ)) (approximate h stages t^r-evolve h.total t^r) ψ‖ ≤
      (r : ℝ)*‖(approximate h stages t-evolve h.total t)*low h.total h.total_hermitian Δ‖+
      2*‖(Matrix.toEuclideanCLM (n := Register N) (𝕜 := ℂ)) (high h.total h.total_hermitian Δ) ψ‖ := by
  let W := approximate h stages t^r
  let U := evolve h.total t^r
  let P := low h.total h.total_hermitian Δ
  let Q := high h.total h.total_hermitian Δ
  let T := Matrix.toEuclideanCLM (n := Register N) (𝕜 := ℂ)
  have hW : W ∈ unitary (Matrix (Register N) (Register N) ℂ) :=
      pow_mem (approximate_unitary h stages t) r
  have hU : U ∈ unitary (Matrix (Register N) (Register N) ℂ) :=
      pow_mem (evolve_unitary _ h.total_hermitian t) r
  have he : W-U=(W-U)*P+W*Q-U*Q := by
    dsimp only [Q, high]
    change W-U=(W-U)*P+W*(1-P)-U*(1-P)
    noncomm_ring
  have hs : T (W-U) ψ = T ((W-U)*P) ψ + T W (T Q ψ) - T U (T Q ψ) := by
    conv_lhs => rw [he]
    simp only [map_add, map_sub, map_mul, ContinuousLinearMap.add_apply,
      ContinuousLinearMap.sub_apply, ContinuousLinearMap.mul_apply]
  have hlow : ‖T ((W-U)*P) ψ‖ ≤ ‖(W-U)*P‖ := by
    calc
      _ ≤ ‖T ((W-U)*P)‖*‖ψ‖ := (T ((W-U)*P)).le_opNorm ψ
      _ = _ := by rw [Matrix.l2_opNorm_toEuclideanCLM, hψ, mul_one]
  have hw : ‖T W (T Q ψ)‖ ≤ ‖T Q ψ‖ := by
    calc
      _ ≤ ‖T W‖*‖T Q ψ‖ := (T W).le_opNorm _
      _ = _ := by rw [Matrix.l2_opNorm_toEuclideanCLM, CStarRing.norm_of_mem_unitary hW, one_mul]
  have hu : ‖T U (T Q ψ)‖ ≤ ‖T Q ψ‖ := by
    calc
      _ ≤ ‖T U‖*‖T Q ψ‖ := (T U).le_opNorm _
      _ = _ := by rw [Matrix.l2_opNorm_toEuclideanCLM, CStarRing.norm_of_mem_unitary hU, one_mul]
  change ‖T (W-U) ψ‖ ≤ _
  rw [hs]
  calc
    _ ≤ (‖T ((W-U)*P) ψ‖+‖T W (T Q ψ)‖)+‖T U (T Q ψ)‖ :=
      (norm_sub_le _ _).trans (add_le_add (norm_add_le _ _) le_rfl)
    _ ≤ (‖(W-U)*P‖+‖T Q ψ‖)+‖T Q ψ‖ := add_le_add (add_le_add hlow hw) hu
    _ ≤ _ := by
      have hr := actual_repeated_error h stages t Δ r
      change ‖(W-U)*P‖ ≤ _ at hr
      change _ ≤ (r : ℝ)*‖(approximate h stages t-evolve h.total t)*P‖+2*‖T Q ψ‖
      linarith only [hr]
end Qatlib.Papers.LowEnergyProd24.RetainedBound
