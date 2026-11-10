/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Analysis.Calculus.FDeriv.Basic
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.Complex.Basic
import Mathlib.Data.Fin.Basic

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.LatentPQCTran26.MainResults.GradientLipschitz

open Complex

def expectationLoss {K : ℕ} {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (O : H →L[ℂ] H) (ψ : (Fin K → ℝ) → H) : (Fin K → ℝ) → ℝ :=
  fun θ => (inner ℂ (ψ θ) (O (ψ θ))).re

def partialDeriv {K : ℕ} {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (O : H →L[ℂ] H) (ψ : (Fin K → ℝ) → H) (θ : Fin K → ℝ) (j : Fin K) : ℝ :=
  (fderiv ℝ (expectationLoss O ψ) θ) (Pi.single j 1)

private theorem abs_re_inner_le {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (M : H →L[ℂ] H) (φ : H) (hφ : ‖φ‖ = 1) :
    |(inner ℂ φ (M φ)).re| ≤ ‖M‖ := by
  have h1 : |(inner ℂ φ (M φ)).re| ≤ ‖(inner ℂ φ (M φ) : ℂ)‖ :=
    Complex.abs_re_le_norm _
  have h2 : ‖(inner ℂ φ (M φ) : ℂ)‖ ≤ ‖φ‖ * ‖M φ‖ := norm_inner_le_norm _ _
  have h4 := M.le_opNorm φ
  rw [hφ, mul_one] at h4
  have h3 : ‖φ‖ * ‖M φ‖ ≤ ‖M‖ := by
    rw [hφ, one_mul]
    exact h4
  exact h1.trans (h2.trans h3)

theorem lemma5_first_derivative
    {K : ℕ} {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (O : H →L[ℂ] H)
    (ψ : (Fin K → ℝ) → H) (hunit : ∀ θ, ‖ψ θ‖ = 1)
    (hins : ∀ (θ : Fin K → ℝ) (j : Fin K), ∃ M : H →L[ℂ] H, ‖M‖ ≤ 2 ∧
      partialDeriv O ψ θ j = (inner ℂ (ψ θ) (M (ψ θ))).re) :
    ∀ θ (j : Fin K), |partialDeriv O ψ θ j| ≤ 2 := by
  intro θ j
  obtain ⟨M, hM, heq⟩ := hins θ j
  rw [heq]
  exact (abs_re_inner_le M (ψ θ) (hunit θ)).trans hM

theorem lemma5_second_derivative
    {K : ℕ} {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (O : H →L[ℂ] H)
    (ψ : (Fin K → ℝ) → H) (hunit : ∀ θ, ‖ψ θ‖ = 1)
    (hins : ∀ (θ : Fin K → ℝ) (j k : Fin K), ∃ M : H →L[ℂ] H, ‖M‖ ≤ 4 ∧
      (fderiv ℝ (fun θ' => (fderiv ℝ (expectationLoss O ψ) θ') (Pi.single k 1)) θ)
        (Pi.single j 1) = (inner ℂ (ψ θ) (M (ψ θ))).re) :
    ∀ θ (j k : Fin K),
      |(fderiv ℝ (fun θ' => (fderiv ℝ (expectationLoss O ψ) θ') (Pi.single k 1)) θ)
        (Pi.single j 1)| ≤ 4 := by
  intro θ j k
  obtain ⟨M, hM, heq⟩ := hins θ j k
  rw [heq]
  exact (abs_re_inner_le M (ψ θ) (hunit θ)).trans hM

private theorem single_eq_ite {K : ℕ} (i : Fin K) :
    (Pi.single i 1 : Fin K → ℝ) = fun j => if i = j then 1 else 0 := by
  funext j
  by_cases h : i = j
  · rw [Pi.single_apply, if_pos h.symm, if_pos h]
  · rw [Pi.single_apply, if_neg (fun hc => h hc.symm), if_neg h]

private theorem scalarClm_bound {K : ℕ} (T : (Fin K → ℝ) →L[ℝ] ℝ) {B : ℝ} (hB : 0 ≤ B)
    (hent : ∀ i : Fin K, |T (Pi.single i 1)| ≤ B) (x : Fin K → ℝ) :
    |T x| ≤ (K : ℝ) * B * ‖x‖ := by
  have hexp : T x = ∑ i, x i * T (Pi.single i 1 : Fin K → ℝ) := by
    conv_lhs => rw [pi_eq_sum_univ x]
    rw [map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_smul, smul_eq_mul, single_eq_ite]
  have hxi : ∀ i : Fin K, |x i| ≤ ‖x‖ := fun i => by
    haveI : Nonempty (Fin K) := ⟨i⟩
    rw [← Real.norm_eq_abs]
    exact (pi_norm_le_iff_of_nonempty (r := ‖x‖) x).1 le_rfl i
  calc |T x| ≤ ∑ i : Fin K, |x i * T (Pi.single i 1)| := by
        rw [hexp]
        exact Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i : Fin K, |x i| * B :=
        Finset.sum_le_sum fun i _ => by
          rw [abs_mul]
          exact mul_le_mul_of_nonneg_left (hent i) (abs_nonneg _)
    _ ≤ ∑ i : Fin K, ‖x‖ * B :=
        Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_right (hxi i) hB
    _ = (K : ℝ) * (‖x‖ * B) := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    _ = (K : ℝ) * B * ‖x‖ := by ring

theorem lemma5_gradient_lipschitz
    {K : ℕ} {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (O : H →L[ℂ] H)
    (ψ : (Fin K → ℝ) → H)
    (hdg : ∀ (k : Fin K), Differentiable ℝ
      (fun θ => (fderiv ℝ (expectationLoss O ψ) θ) (Pi.single k 1)))
    (hH : ∀ (θ : Fin K → ℝ) (j k : Fin K),
      |(fderiv ℝ (fun θ' => (fderiv ℝ (expectationLoss O ψ) θ') (Pi.single k 1)) θ)
        (Pi.single j 1)| ≤ 4) :
    ∃ Λ : ℝ, Λ ≤ 4 * ((K : ℝ) + 1) * ((K : ℝ) + 1) ∧ ∀ θ θ',
      ‖fderiv ℝ (expectationLoss O ψ) θ - fderiv ℝ (expectationLoss O ψ) θ'‖
        ≤ Λ * ‖θ - θ'‖ := by
  classical

  have hop : ∀ (j : Fin K) (z : Fin K → ℝ),
      ‖fderiv ℝ (fun θ => (fderiv ℝ (expectationLoss O ψ) θ) (Pi.single j 1)) z‖
        ≤ 4 * ((K : ℝ) + 1) := by
    intro j z
    refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun x => ?_
    have hx := scalarClm_bound (fderiv ℝ
      (fun θ => (fderiv ℝ (expectationLoss O ψ) θ) (Pi.single j 1)) z) (B := (4 : ℝ))
      (by positivity) (fun i => hH z i j) x
    rw [Real.norm_eq_abs]
    calc |(fderiv ℝ (fun θ => (fderiv ℝ (expectationLoss O ψ) θ) (Pi.single j 1)) z) x|
        ≤ (K : ℝ) * 4 * ‖x‖ := hx
      _ ≤ 4 * ((K : ℝ) + 1) * ‖x‖ := by
          refine mul_le_mul_of_nonneg_right ?_ (norm_nonneg _)
          linarith

  have hmvt : ∀ (j : Fin K) (θ θ' : Fin K → ℝ),
      |(fderiv ℝ (expectationLoss O ψ) θ) (Pi.single j 1) -
        (fderiv ℝ (expectationLoss O ψ) θ') (Pi.single j 1)|
        ≤ 4 * ((K : ℝ) + 1) * ‖θ - θ'‖ := by
    intro j θ θ'
    have hkey := Convex.norm_image_sub_le_of_norm_fderiv_le
      (f := fun θ'' => (fderiv ℝ (expectationLoss O ψ) θ'') (Pi.single j 1))
      (fun z _ => (hdg j).differentiableAt)
      (fun z _ => hop j z)
      (convex_segment (𝕜 := ℝ) θ' θ)
      (left_mem_segment ℝ θ' θ) (right_mem_segment ℝ θ' θ)
    rw [Real.norm_eq_abs] at hkey
    exact hkey

  refine ⟨4 * ((K : ℝ) + 1) * ((K : ℝ) + 1), by linarith, fun θ θ' => ?_⟩
  refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun x => ?_
  set T := fderiv ℝ (expectationLoss O ψ) θ - fderiv ℝ (expectationLoss O ψ) θ' with hT
  have hexp : T x = ∑ i, x i * T (Pi.single i 1 : Fin K → ℝ) := by
    conv_lhs => rw [pi_eq_sum_univ x]
    rw [map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_smul, smul_eq_mul, single_eq_ite]
  have hent : ∀ i : Fin K, |T (Pi.single i 1)| ≤ 4 * ((K : ℝ) + 1) * ‖θ - θ'‖ := by
    intro i
    rw [hT, ContinuousLinearMap.sub_apply]
    exact hmvt i θ θ'
  have hxi : ∀ i : Fin K, |x i| ≤ ‖x‖ := fun i => by
    haveI : Nonempty (Fin K) := ⟨i⟩
    rw [← Real.norm_eq_abs]
    exact (pi_norm_le_iff_of_nonempty (r := ‖x‖) x).1 le_rfl i
  rw [Real.norm_eq_abs]
  have h1a : ∑ i : Fin K, |x i * T (Pi.single i 1 : Fin K → ℝ)|
      ≤ ∑ i : Fin K, |x i| * (4 * ((K : ℝ) + 1) * ‖θ - θ'‖) :=
    Finset.sum_le_sum fun i _ => by
      rw [abs_mul]
      exact mul_le_mul_of_nonneg_left (hent i) (abs_nonneg _)
  have h1b : |T x| ≤ ∑ i : Fin K, |x i * T (Pi.single i 1 : Fin K → ℝ)| := by
    rw [hexp]
    exact Finset.abs_sum_le_sum_abs _ _
  have h1 := h1b.trans h1a
  have h2 : ∑ i : Fin K, |x i| * (4 * ((K : ℝ) + 1) * ‖θ - θ'‖)
      ≤ ∑ i : Fin K, ‖x‖ * (4 * ((K : ℝ) + 1) * ‖θ - θ'‖) :=
    Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_right (hxi i) (by positivity)
  have h3 : ∑ i : Fin K, ‖x‖ * (4 * ((K : ℝ) + 1) * ‖θ - θ'‖)
      = (K : ℝ) * ‖x‖ * (4 * ((K : ℝ) + 1) * ‖θ - θ'‖) := by
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    ring
  calc |T x| ≤ (K : ℝ) * ‖x‖ * (4 * ((K : ℝ) + 1) * ‖θ - θ'‖) :=
        h1.trans (h2.trans (by rw [h3]))
    _ ≤ 4 * ((K : ℝ) + 1) * ((K : ℝ) + 1) * ‖θ - θ'‖ * ‖x‖ := by
        have hC : (0 : ℝ) ≤ 4 * ((K : ℝ) + 1) * ‖θ - θ'‖ * ‖x‖ := by positivity
        have hstep : (K : ℝ) * (4 * ((K : ℝ) + 1) * ‖θ - θ'‖ * ‖x‖)
            ≤ ((K : ℝ) + 1) * (4 * ((K : ℝ) + 1) * ‖θ - θ'‖ * ‖x‖) :=
          mul_le_mul_of_nonneg_right (by linarith) hC
        linear_combination hstep

end Qatlib.Papers.LatentPQCTran26.MainResults.GradientLipschitz
