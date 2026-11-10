/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Foundations.CbmdAnalysis.Core.CosineApplications
import Mathlib.Analysis.Real.Pi.Bounds
set_option warningAsError false

namespace Qatlib.Foundations.CbmdAnalysis.Core

set_option autoImplicit false
noncomputable section
namespace CBMD
open Complex Filter Metric
open scoped Topology BigOperators

theorem cosineSampleCoefficient_norm_tsum_le_scale {γ τ : ℝ}
    (hγ : 0 < γ) (hτ : 0 < τ) :
    (∑' k : ℕ, ‖cosineSampleCoefficient γ τ k‖) ≤ γ * τ ^ 2 := by
  have hsplit := (cosineSampleCoefficient_norm_summable hγ hτ).sum_add_tsum_nat_add 1
  have hz := cosineSampleCoefficient_norm_le_cubic hγ hτ 0
  have ht := cosineSampleCoefficient_tail_tsum_le hγ hτ 0
  norm_num only [Nat.cast_zero, zero_add] at hz ht
  have hz' : ‖cosineSampleCoefficient γ τ 0‖ ≤ 16 * γ * τ ^ 2 / Real.pi ^ 3 := by
    convert! hz using 1
    ring
  have ht' : (∑' k : ℕ, ‖cosineSampleCoefficient γ τ (k + 1)‖) ≤
      4 * γ * τ ^ 2 / Real.pi ^ 3 := by
    simp only [Nat.add_comm 1] at ht
    convert! ht using 1
    ring
  have hπ : 20 ≤ Real.pi ^ 3 := by nlinarith [Real.pi_gt_three, sq_nonneg (Real.pi - 3)]
  have hc : 20 * γ * τ ^ 2 / Real.pi ^ 3 ≤ γ * τ ^ 2 := by
    apply (div_le_iff₀ (pow_pos Real.pi_pos _)).mpr
    nlinarith [mul_le_mul_of_nonneg_right hπ (show 0 ≤ γ * τ ^ 2 by positivity)]
  rw [← hsplit]
  simp only [Finset.sum_range_one]
  calc
    _ ≤ 16 * γ * τ ^ 2 / Real.pi ^ 3 + 4 * γ * τ ^ 2 / Real.pi ^ 3 := add_le_add hz' ht'
    _ = 20 * γ * τ ^ 2 / Real.pi ^ 3 := by ring
    _ ≤ _ := hc

def cosineCutoff (γ τ δ : ℝ) : ℕ :=
  ⌈Real.sqrt (γ * τ ^ 2 * Real.exp (τ * Real.sqrt (γ / 2)) / (Real.pi ^ 3 * δ))⌉₊

def cosineRetainedCount (γ τ δ : ℝ) : ℕ :=
  if γ * τ ^ 2 * Real.exp (τ * Real.sqrt (γ / 2)) ≤ δ then 0 else cosineCutoff γ τ δ + 1

theorem cosineCutoff_tail_budget {γ τ δ : ℝ}
    (hγ : 0 < γ) (hτ : 0 < τ) (hδ : 0 < δ) :
    ‖cosineRegulator γ τ 1‖ * γ * τ ^ 2 /
      (Real.pi ^ 3 * ((cosineCutoff γ τ δ : ℝ) + 1 / 2) ^ 2) ≤ δ := by
  let Y := γ * τ ^ 2 * Real.exp (τ * Real.sqrt (γ / 2)) / (Real.pi ^ 3 * δ)
  have hY : 0 ≤ Y := by dsimp [Y]; positivity
  have hK : Real.sqrt Y ≤ (cosineCutoff γ τ δ : ℝ) := Nat.le_ceil _
  have hsq : Y ≤ ((cosineCutoff γ τ δ : ℝ) + 1 / 2) ^ 2 := by
    nlinarith [Real.sq_sqrt hY, Real.sqrt_nonneg Y]
  have hnum : ‖cosineRegulator γ τ 1‖ * γ * τ ^ 2 ≤
      Real.exp (τ * Real.sqrt (γ / 2)) * γ * τ ^ 2 :=
    mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
      (cosineRegulator_one_norm_le hγ hτ) hγ.le) (sq_nonneg τ)
  apply (div_le_iff₀ (by positivity)).mpr
  have hb := (div_le_iff₀ (show 0 < Real.pi ^ 3 * δ by positivity)).mp hsq
  nlinarith

theorem cosineRetainedCount_le {γ τ δ : ℝ}
    (hγ : 0 < γ) (hτ : 0 < τ) (hδ : 0 < δ) :
    (cosineRetainedCount γ τ δ : ℝ) ≤
      Real.sqrt (γ * τ ^ 2 * Real.exp (τ * Real.sqrt (γ / 2)) / (Real.pi ^ 3 * δ)) + 2 := by
  unfold cosineRetainedCount
  split_ifs
  · simp only [Nat.cast_zero]
    positivity
  · have hk := Nat.ceil_lt_add_one (Real.sqrt_nonneg
      (γ * τ ^ 2 * Real.exp (τ * Real.sqrt (γ / 2)) / (Real.pi ^ 3 * δ)))
    dsimp [cosineCutoff]
    push_cast
    linarith

theorem cosineRetained_sampleScale_le {γ τ δ : ℝ}
    (hγ : 0 < γ) (hτ : 0 < τ) (hδ : 0 < δ) (k : ℕ)
    (hk : k < cosineRetainedCount γ τ δ) :
    cosineSampleScale γ τ k ≤ 169 * Real.exp (τ * Real.sqrt (γ / 2)) / δ := by
  unfold cosineRetainedCount at hk
  split_ifs at hk with hempty
  · omega
  · let X := γ * τ ^ 2
    let e := Real.exp (τ * Real.sqrt (γ / 2))
    let Y := X * e / (Real.pi ^ 3 * δ)
    have hX : 0 < X := by dsimp [X]; positivity
    have he : 0 < e := Real.exp_pos _
    have hY : 0 < Y := by dsimp [Y]; positivity
    have hπ3 : Real.pi ^ 3 < (64 : ℝ) := by
      nlinarith [Real.pi_lt_four, Real.pi_pos, sq_nonneg (Real.pi - 4)]
    have hlo : (1 / 64 : ℝ) < Y := by
      apply (lt_div_iff₀ (show 0 < Real.pi ^ 3 * δ by positivity)).mpr
      have hm := mul_lt_mul_of_pos_right hπ3 hδ
      dsimp [X, e] at *
      linarith
    have hyr : (1 / 8 : ℝ) < Real.sqrt Y := by
      nlinarith [Real.sq_sqrt hY.le, Real.sqrt_nonneg Y]
    have hKu : (cosineCutoff γ τ δ : ℝ) < Real.sqrt Y + 1 :=
        Nat.ceil_lt_add_one (Real.sqrt_nonneg Y)
    have hkc : (k : ℝ) ≤ (cosineCutoff γ τ δ : ℝ) := by
      exact_mod_cast (show k ≤ cosineCutoff γ τ δ by omega)
    have hsq : ((k : ℝ) + 1 / 2) ^ 2 ≤ 169 * Y := by
      have hl : (k : ℝ) + 1 / 2 ≤ 13 * Real.sqrt Y := by linarith
      have h := pow_le_pow_left₀ (show 0 ≤ (k : ℝ) + 1 / 2 by positivity) hl 2
      nlinarith [Real.sq_sqrt hY.le]
    have hπ : 1 ≤ Real.pi := by linarith [Real.two_le_pi]
    calc
      cosineSampleScale γ τ k = Real.pi ^ 2 * ((k : ℝ) + 1 / 2) ^ 2 / X := by
        unfold cosineSampleScale cosineSampleAngle X
        ring
      _ ≤ Real.pi ^ 2 * (169 * Y) / X :=
        div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hsq (sq_nonneg _)) hX.le
      _ = 169 * e / (Real.pi * δ) := by
        dsimp [Y]
        field_simp
      _ ≤ 169 * e / δ := div_le_div_of_nonneg_left (by positivity) hδ (by nlinarith)
      _ = _ := rfl

section Banach
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]

def cosineApproximation (γ τ : ℝ) (N : ℕ) (U : ℂ → E) : E :=
  cosineRegulator γ τ 1 • U 0 - cosineRegulator γ τ 1 • cosineLCUSum γ τ N U

omit [CompleteSpace E] in

theorem cosineSample_full_weighted_norm_le {γ τ : ℝ} (hγ : 0 < γ) (hτ : 0 < τ)
    (U : ℂ → E) (hUsample : ∀ k, ‖U (cosineSamplePole γ τ k)‖ ≤ 1) :
    ‖cosineRegulator γ τ 1 • ∑' k : ℕ, cosineSample γ τ U k‖ ≤
      γ * τ ^ 2 * Real.exp (τ * Real.sqrt (γ / 2)) := by
  have hn := cosineSample_norm_summable hγ hτ U hUsample
  have hc := cosineSampleCoefficient_norm_summable hγ hτ
  have hs : (∑' k : ℕ, ‖cosineSample γ τ U k‖) ≤
      ∑' k : ℕ, ‖cosineSampleCoefficient γ τ k‖ := by
    apply Summable.tsum_le_tsum _ hn hc
    intro k
    rw [cosineSample, norm_smul]
    simpa only [mul_one] using! mul_le_mul_of_nonneg_left (hUsample k)
      (norm_nonneg (cosineSampleCoefficient γ τ k))
  rw [norm_smul]
  have hnorm := (norm_tsum_le_tsum_norm hn).trans
    (hs.trans (cosineSampleCoefficient_norm_tsum_le_scale hγ hτ))
  have hh := mul_le_mul (cosineRegulator_one_norm_le hγ hτ) hnorm
    (norm_nonneg _) (Real.exp_pos _).le
  convert! hh using 1
  ring

theorem cosine_chosen_target_error_le {γ τ δ C : ℝ}
    (hγ : 0 < γ) (hτ : 0 < τ) (hδ : 0 < δ) (hC : 0 ≤ C)
    (U : ℂ → E) (hUanalytic : Differentiable ℂ U)
    (hUsample : ∀ k, ‖U (cosineSamplePole γ τ k)‖ ≤ 1)
    (hUcircle : ∀ᶠ n : ℕ in atTop, ∀ z ∈ sphere 0 (cosineCircleRadius γ τ n),
      ‖U z‖ ≤ C * ‖cosineRegulator γ τ z‖) :
    ‖U 1 - cosineApproximation γ τ (cosineRetainedCount γ τ δ) U‖ ≤ δ := by
  unfold cosineRetainedCount
  split_ifs with hempty
  · have hid := cosine_kernel_series_identity hγ hτ hC U hUanalytic hUsample hUcircle
    have he : U 1 - cosineApproximation γ τ 0 U =
        -(cosineRegulator γ τ 1 • ∑' k : ℕ, cosineSample γ τ U k) := by
      rw [hid]
      simp only [cosineApproximation, cosineLCUSum, Finset.range_zero, Finset.sum_empty,
        smul_zero, sub_zero]
      abel
    rw [he, norm_neg]
    exact (cosineSample_full_weighted_norm_le hγ hτ U hUsample).trans hempty
  · exact (cosineLCU_target_error_le hγ hτ hC U hUanalytic hUsample hUcircle
      (cosineCutoff γ τ δ)).trans (cosineCutoff_tail_budget hγ hτ hδ)

end Banach
section Matrix
open scoped Matrix.Norms.L2Operator ComplexOrder MatrixOrder
variable {n : Type*} [Fintype n] [DecidableEq n]

theorem wave_cbmd_chosen_error (L H : Matrix n n ℂ) (hL : L.PosSemidef) (hH : H.PosDef)
    {γ t δ : ℝ} (hγ : 0 < γ) (ht : 0 < t) (hδ : 0 < δ) (hγH : ‖H‖ ≤ γ) :
    ‖wavePropagator (L + I • H) (t : ℂ) -
      cosineApproximation γ t (cosineRetainedCount γ t δ) (waveCosineNumerator L H (t : ℂ))‖ ≤ δ := by
  simpa only [waveCosineNumerator, mul_one] using!
    cosine_chosen_target_error_le hγ ht hδ (cosineAngularConstant_pos L H t).le
      (waveCosineNumerator L H (t : ℂ)) (waveCosineNumerator_differentiable L H (t : ℂ))
      (waveCosineNumerator_sample_norm_le_one L H hL hH.posSemidef hγ ht t)
      (waveCosineNumerator_circle_comparison L H hH hγ ht hγH)

theorem bessel_cbmd_chosen_error (L H : Matrix n n ℂ) (hL : L.PosSemidef) (hH : H.PosDef)
    {γ t δ : ℝ} (hγ : 0 < γ) (ht : 0 < t) (hδ : 0 < δ) (hγH : ‖H‖ ≤ γ) :
    ‖besselPropagator (L + I • H) (t : ℂ) -
      cosineApproximation γ t (cosineRetainedCount γ t δ) (besselCosineNumerator L H (t : ℂ))‖ ≤ δ := by
  simpa only [besselCosineNumerator, mul_one] using!
    cosine_chosen_target_error_le hγ ht hδ (cosineAngularConstant_pos L H t).le
      (besselCosineNumerator L H (t : ℂ)) (besselCosineNumerator_differentiable L H (t : ℂ))
      (besselCosineNumerator_sample_norm_le_one L H hL hH.posSemidef hγ ht t)
      (besselCosineNumerator_circle_comparison L H hH hγ ht hγH)

theorem airy_cbmd_chosen_error (L H : Matrix n n ℂ) (hL : L.PosSemidef) (hH : H.PosDef)
    {γ t δ : ℝ} (hγ : 0 < γ) (ht : 0 < t) (hδ : 0 < δ) (hγH : ‖H‖ ≤ γ) :
    ‖airyPropagator (L + I • H) (t : ℂ) -
      cosineApproximation γ (airyTimeScale t) (cosineRetainedCount γ (airyTimeScale t) δ)
        (airyCosineNumerator L H (t : ℂ))‖ ≤ δ := by
  simpa only [airyCosineNumerator, mul_one] using!
    cosine_chosen_target_error_le hγ (airyTimeScale_pos_of_pos ht) hδ
      (cosineAngularConstant_pos L H (airyTimeScale t)).le
      (airyCosineNumerator L H (t : ℂ)) (airyCosineNumerator_differentiable L H (t : ℂ))
      (airyCosineNumerator_sample_norm_le_one L H hL hH.posSemidef hγ
        (airyTimeScale_pos_of_pos ht) t ht.le)
      (airyCosineNumerator_circle_comparison L H hH hγ ht hγH)

theorem cosineRetained_blockNormalization_le (L H : Matrix n n ℂ)
    {γ τ δ : ℝ} (hγ : 0 < γ) (hτ : 0 < τ) (hδ : 0 < δ) (k : ℕ)
    (hk : k < cosineRetainedCount γ τ δ) :
    ‖L‖ + cosineSampleScale γ τ k * ‖H‖ ≤
      ‖L‖ + 169 * ‖H‖ * Real.exp (τ * Real.sqrt (γ / 2)) / δ := by
  have h := mul_le_mul_of_nonneg_right (cosineRetained_sampleScale_le hγ hτ hδ k hk) (norm_nonneg H)
  calc
    _ ≤ ‖L‖ + (169 * Real.exp (τ * Real.sqrt (γ / 2)) / δ) * ‖H‖ := by linarith
    _ = _ := by ring

end Matrix
end CBMD

end
end Qatlib.Foundations.CbmdAnalysis.Core
