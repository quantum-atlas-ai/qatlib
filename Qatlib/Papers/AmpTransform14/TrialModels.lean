/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Data.Real.Sqrt

set_option autoImplicit false

namespace Qatlib.Papers.AmpTransform14.TrialModels

noncomputable section

def expectedTrials (p : ℝ) : ℝ := 1 / p

def trialsVariance (p : ℝ) : ℝ := (1 - p) / p ^ 2

def qftSuccessBound (M N : ℝ) : ℝ := 4 * M / N * (1 - M / N)

def qhsSuccessBound (M N : ℝ) : ℝ := 2 * M / N * (1 - M / N)

def amplifiedWorkFactor (M N : ℝ) : ℝ := Real.sqrt (N / M)

@[simp]
theorem expectedTrials_eq_inv (p : ℝ) : expectedTrials p = p⁻¹ := by
  unfold expectedTrials; rw [one_div]

@[simp]
theorem amplifiedWorkFactor_sq {M N : ℝ} (hM : 0 < M) (hN : 0 ≤ N) :
    amplifiedWorkFactor M N ^ 2 = N / M := by
  unfold amplifiedWorkFactor
  rw [Real.sq_sqrt (by positivity)]

theorem hasSum_geometric_firstSuccess {p : ℝ} (hp : 0 < p) (hp1 : p ≤ 1) :
    HasSum (fun k : ℕ => ((k : ℝ) + 1) * (1 - p) ^ k * p) (expectedTrials p) := by
  have hr : ‖1 - p‖ < 1 := by
    rw [Real.norm_eq_abs, abs_lt]
    constructor <;> linarith
  have hgeom :
      HasSum (fun n : ℕ => (n : ℝ) * (1 - p) ^ n + (1 - p) ^ n)
        ((1 - p) / (1 - (1 - p)) ^ 2 + (1 - (1 - p))⁻¹) :=
    (hasSum_coe_mul_geometric_of_norm_lt_one (𝕜 := ℝ) hr).add
      (hasSum_geometric_of_norm_lt_one (K := ℝ) hr)
  have hfun₁ : (fun k : ℕ => ((k : ℝ) + 1) * (1 - p) ^ k)
      = (fun n : ℕ => (n : ℝ) * (1 - p) ^ n + (1 - p) ^ n) := by
    ext k
    ring
  have hsplit : HasSum (fun k : ℕ => ((k : ℝ) + 1) * (1 - p) ^ k)
      ((1 - p) / (1 - (1 - p)) ^ 2 + (1 - (1 - p))⁻¹) := by
    rw [hfun₁]
    exact hgeom
  have hscaled := hsplit.mul_left p
  have hval : p * ((1 - p) / (1 - (1 - p)) ^ 2 + (1 - (1 - p))⁻¹) = expectedTrials p := by
    have hsub : (1 : ℝ) - (1 - p) = p := by ring
    rw [hsub, expectedTrials_eq_inv]
    field_simp
    try ring_nf
  have hfun₂ : (fun k : ℕ => ((k : ℝ) + 1) * (1 - p) ^ k * p)
      = (fun i : ℕ => p * (((i : ℝ) + 1) * (1 - p) ^ i)) := by
    ext k
    ring
  rw [hfun₂]
  rwa [hval] at hscaled

theorem expectedTrials_ge_of_le {p B : ℝ} (hp : 0 < p) (hpB : p ≤ B) (hB : 0 < B) :
    expectedTrials B ≤ expectedTrials p := by
  rw [expectedTrials_eq_inv, expectedTrials_eq_inv]
  exact (inv_le_inv₀ hB hp).2 hpB

theorem qftSuccessBound_pos {M N : ℝ} (hM : 0 < M) (hMN : M < N) :
    0 < qftSuccessBound M N := by
  have hN : 0 < N := lt_trans hM hMN
  have h1 : qftSuccessBound M N = 4 * M * (N - M) / N ^ 2 := by
    unfold qftSuccessBound
    field_simp
    try ring_nf
  rw [h1]; positivity

theorem qhsSuccessBound_pos {M N : ℝ} (hM : 0 < M) (hMN : M < N) :
    0 < qhsSuccessBound M N := by
  have hN : 0 < N := lt_trans hM hMN
  have h1 : qhsSuccessBound M N = 2 * M * (N - M) / N ^ 2 := by
    unfold qhsSuccessBound
    field_simp
    try ring_nf
  rw [h1]; positivity

theorem qft_expectedTrials_ge {M N p : ℝ} (hM : 0 < M) (hMN : M < N) (hp : 0 < p)
    (hpB : p ≤ qftSuccessBound M N) : N / (4 * M) ≤ expectedTrials p := by
  have hN : 0 < N := lt_trans hM hMN
  have hB : 0 < qftSuccessBound M N := qftSuccessBound_pos hM hMN
  have hkey : qftSuccessBound M N = 4 * M * (N - M) / N ^ 2 := by
    unfold qftSuccessBound
    field_simp
    try ring_nf
  have hinv : (qftSuccessBound M N)⁻¹ = N ^ 2 / (4 * M * (N - M)) := by
    rw [hkey]; field_simp
  have hstep : N / (4 * M) ≤ (qftSuccessBound M N)⁻¹ := by
    rw [hinv, ← sub_nonneg]
    have hdiff : N ^ 2 / (4 * M * (N - M)) - N / (4 * M) = N * M / (4 * M * (N - M)) := by
      have h1 : (N - M) ≠ 0 := by linarith
      field_simp
      ring
    rw [hdiff]
    have h1 : 0 < N - M := by linarith
    positivity
  have hinvle : (qftSuccessBound M N)⁻¹ ≤ p⁻¹ := (inv_le_inv₀ hB hp).2 hpB
  rw [expectedTrials_eq_inv]
  linarith

theorem qhs_expectedTrials_ge {M N p : ℝ} (hM : 0 < M) (hMN : M < N) (hp : 0 < p)
    (hpB : p ≤ qhsSuccessBound M N) : N / (2 * M) ≤ expectedTrials p := by
  have hN : 0 < N := lt_trans hM hMN
  have hB : 0 < qhsSuccessBound M N := qhsSuccessBound_pos hM hMN
  have hkey : qhsSuccessBound M N = 2 * M * (N - M) / N ^ 2 := by
    unfold qhsSuccessBound
    field_simp
    try ring_nf
  have hinv : (qhsSuccessBound M N)⁻¹ = N ^ 2 / (2 * M * (N - M)) := by
    rw [hkey]; field_simp
  have hstep : N / (2 * M) ≤ (qhsSuccessBound M N)⁻¹ := by
    rw [hinv, ← sub_nonneg]
    have hdiff : N ^ 2 / (2 * M * (N - M)) - N / (2 * M) = N * M / (2 * M * (N - M)) := by
      have h1 : (N - M) ≠ 0 := by linarith
      field_simp
      ring
    rw [hdiff]
    have h1 : 0 < N - M := by linarith
    positivity
  have hinvle : (qhsSuccessBound M N)⁻¹ ≤ p⁻¹ := (inv_le_inv₀ hB hp).2 hpB
  rw [expectedTrials_eq_inv]
  linarith

theorem trialsVariance_ge_bound {p B f : ℝ} (hp : 0 < p) (hpB : p ≤ B)
    (hf : 0 < f) (hfail : f ≤ 1 - p) :
    f / B ^ 2 ≤ trialsVariance p := by
  have hpsq : p ^ 2 ≤ B ^ 2 := by
    have := pow_le_pow_left₀ (le_of_lt hp) hpB 2
    simpa using this
  have h1 : f / p ^ 2 ≤ (1 - p) / p ^ 2 := by
    gcongr
  have h2 : f / B ^ 2 ≤ f / p ^ 2 := by
    gcongr
  unfold trialsVariance
  linarith

theorem qft_variance_algebra {M N : ℝ} (hM : 0 < M) (hMN : 4 * M ≤ N)
    (h2M : 2 * M ^ 2 < N) :
    (N / (N - M)) ^ 2 * ((N - 2 * M ^ 2) / (4 * M))
      ≤ ((N - 2 * M ^ 2) / N) / (qftSuccessBound M N) ^ 2 := by
  have hN : 0 < N := by linarith
  have hNM : 0 < N - M := by linarith
  have hfac : 1 ≤ N / (4 * M) := by
    rw [le_div_iff₀ (by positivity)]
    linarith
  have hid : ((N - 2 * M ^ 2) / N) / (qftSuccessBound M N) ^ 2
      = (N / (N - M)) ^ 2 * ((N - 2 * M ^ 2) / (4 * M)) * (N / (4 * M)) := by
    unfold qftSuccessBound
    field_simp
  rw [hid]
  have hA : 0 ≤ (N / (N - M)) ^ 2 * ((N - 2 * M ^ 2) / (4 * M)) := by positivity
  calc (N / (N - M)) ^ 2 * ((N - 2 * M ^ 2) / (4 * M))
      = (N / (N - M)) ^ 2 * ((N - 2 * M ^ 2) / (4 * M)) * 1 := by ring
    _ ≤ (N / (N - M)) ^ 2 * ((N - 2 * M ^ 2) / (4 * M)) * (N / (4 * M)) :=
        mul_le_mul_of_nonneg_left hfac hA

theorem qft_trialsVariance_ge {M N p : ℝ} (hM : 0 < M) (hMN : 4 * M ≤ N)
    (h2M : 2 * M ^ 2 < N) (hp : 0 < p) (hpB : p ≤ qftSuccessBound M N)
    (hfail : (N - 2 * M ^ 2) / N ≤ 1 - p) :
    (N / (N - M)) ^ 2 * ((N - 2 * M ^ 2) / (4 * M)) ≤ trialsVariance p := by
  have hN : 0 < N := by linarith
  have hf : 0 < (N - 2 * M ^ 2) / N := div_pos (by linarith) hN
  have hB : 0 < qftSuccessBound M N := qftSuccessBound_pos hM (by linarith)
  have h1 := trialsVariance_ge_bound hp hpB hf hfail
  have h2 := qft_variance_algebra (M := M) (N := N) hM hMN h2M
  linarith

theorem qhs_variance_algebra {M N : ℝ} (hM : 0 < M) (hMN : M < N) :
    (N / (N - M)) ^ 2 * (((N - M) ^ 2 + M ^ 2) / (4 * M ^ 2))
      = (1 - 2 * M * (N - M) / N ^ 2) / (qhsSuccessBound M N) ^ 2 := by
  have hN : 0 < N := lt_trans hM hMN
  have hNM : 0 < N - M := by linarith
  unfold qhsSuccessBound
  field_simp
  ring

theorem qhs_trialsVariance_ge {M N p : ℝ} (hM : 0 < M) (hMN : M < N) (hp : 0 < p)
    (hpB : p ≤ qhsSuccessBound M N)
    (hfail : 1 - 2 * M * (N - M) / N ^ 2 ≤ 1 - p) :
    (N / (N - M)) ^ 2 * (((N - M) ^ 2 + M ^ 2) / (4 * M ^ 2)) ≤ trialsVariance p := by
  have hN : 0 < N := lt_trans hM hMN
  have hf : 0 < 1 - 2 * M * (N - M) / N ^ 2 := by
    have h1 : 1 - 2 * M * (N - M) / N ^ 2 = ((N - M) ^ 2 + M ^ 2) / N ^ 2 := by
      field_simp
      try ring_nf
    rw [h1]; positivity
  have hB : 0 < qhsSuccessBound M N := qhsSuccessBound_pos hM hMN
  have h1 := trialsVariance_ge_bound hp hpB hf hfail
  have h2 := qhs_variance_algebra (M := M) (N := N) hM hMN
  linarith

theorem qft_trials_over_workFactor {M N : ℝ} (hM : 0 < M) (hMN : M < N) :
    N / (4 * M) / amplifiedWorkFactor M N = Real.sqrt (N / M) / 4 := by
  have hN : 0 < N := lt_trans hM hMN
  have hs : 0 < Real.sqrt (N / M) := Real.sqrt_pos.2 (by positivity)
  have hkey : Real.sqrt (N / M) / 4 * Real.sqrt (N / M) = N / (4 * M) := by
    have hmul : Real.sqrt (N / M) * Real.sqrt (N / M) = N / M :=
      Real.mul_self_sqrt (by positivity)
    calc Real.sqrt (N / M) / 4 * Real.sqrt (N / M)
        = Real.sqrt (N / M) * Real.sqrt (N / M) / 4 := by ring
      _ = N / M / 4 := by rw [hmul]
      _ = N / (4 * M) := by
        rw [div_div]
        congr 1
        ring
  rw [amplifiedWorkFactor, div_eq_iff (ne_of_gt hs), hkey]

theorem qft_speedup_of_successBound {M N p : ℝ} (hM : 0 < M) (hMN : M < N)
    (hp : 0 < p) (hpB : p ≤ qftSuccessBound M N) :
    Real.sqrt (N / M) / 4 ≤ expectedTrials p / amplifiedWorkFactor M N := by
  have h1 := qft_expectedTrials_ge hM hMN hp hpB
  have h2 := qft_trials_over_workFactor (M := M) (N := N) hM hMN
  rw [← h2]
  exact div_le_div_of_nonneg_right h1 (Real.sqrt_nonneg (N / M))

theorem qhs_trials_over_workFactor {M N : ℝ} (hM : 0 < M) (hMN : M < N) :
    N / (2 * M) / amplifiedWorkFactor M N = Real.sqrt (N / M) / 2 := by
  have hN : 0 < N := lt_trans hM hMN
  have hs : 0 < Real.sqrt (N / M) := Real.sqrt_pos.2 (by positivity)
  have hkey : Real.sqrt (N / M) / 2 * Real.sqrt (N / M) = N / (2 * M) := by
    have hmul : Real.sqrt (N / M) * Real.sqrt (N / M) = N / M :=
      Real.mul_self_sqrt (by positivity)
    calc Real.sqrt (N / M) / 2 * Real.sqrt (N / M)
        = Real.sqrt (N / M) * Real.sqrt (N / M) / 2 := by ring
      _ = N / M / 2 := by rw [hmul]
      _ = N / (2 * M) := by
        rw [div_div]
        congr 1
        ring
  rw [amplifiedWorkFactor, div_eq_iff (ne_of_gt hs), hkey]

theorem qhs_speedup_of_successBound {M N p : ℝ} (hM : 0 < M) (hMN : M < N)
    (hp : 0 < p) (hpB : p ≤ qhsSuccessBound M N) :
    Real.sqrt (N / M) / 2 ≤ expectedTrials p / amplifiedWorkFactor M N := by
  have h1 := qhs_expectedTrials_ge hM hMN hp hpB
  have h2 := qhs_trials_over_workFactor (M := M) (N := N) hM hMN
  rw [← h2]
  exact div_le_div_of_nonneg_right h1 (Real.sqrt_nonneg (N / M))

theorem groverIterations_le_workFactor {θ M N : ℝ} (hθ : 0 < θ)
    (hsin : Real.sin θ = Real.sqrt (M / N)) (hM : 0 < M) (hN : 0 < N) :
    (⌊Real.pi / (4 * θ)⌋₊ : ℝ) ≤ Real.pi / (4 * Real.sqrt (M / N)) := by
  have hpi : 0 < Real.pi := Real.pi_pos
  have hspos : 0 < Real.sqrt (M / N) := Real.sqrt_pos.2 (by positivity)
  have hsinθ : Real.sqrt (M / N) ≤ θ := by
    rw [← hsin]
    exact le_of_lt (Real.sin_lt hθ)
  have hfl : (⌊Real.pi / (4 * θ)⌋₊ : ℝ) ≤ Real.pi / (4 * θ) := Nat.floor_le (by positivity)
  have hkey : Real.pi / (4 * θ) ≤ Real.pi / (4 * Real.sqrt (M / N)) := by
    gcongr
  linarith

theorem one_le_speedup_of_sparse {M N : ℝ} (hM : 0 < M) (hMN : 16 * M ≤ N) :
    1 ≤ Real.sqrt (N / M) / 4 := by
  have hratio : 16 ≤ N / M := by
    rw [le_div_iff₀ hM]
    linarith
  have hsqrt : 4 ≤ Real.sqrt (N / M) := by
    have h4 : Real.sqrt 16 ≤ Real.sqrt (N / M) := Real.sqrt_le_sqrt hratio
    have h16 : Real.sqrt 16 = 4 := by
      rw [show (16:ℝ) = 4 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
    rwa [h16] at h4
  linarith

end

end Qatlib.Papers.AmpTransform14.TrialModels
