/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.GevreyGrad19.MainResults.Model.GevreyGradDefinitions
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
/-!
# Robustness of Inverse Quantum Fourier Transform Phase Estimation (Theorem 3.12)

This module formalizes Theorem 3.12 (Section 3, p. 33) of Cornelissen bounding
from below the measurement outcome mass `qftOutcomeProb n a b` concentrated
within distance `4` of the scaled phase `2^n a / (2 pi)` for `n >= 4` and
`|a| <= 2 pi / 3`.

## Main statements

* `qftRobustness`: Theorem 3.12, lower bound `5 / 6` on the sum of
  `qftOutcomeProb n a b` over outcomes within `4` of `2^n a / (2 pi)`.

## References

* [Cornelissen, 2019][Cornelissen2019], Section 3, Theorem 3.12, p. 33.
-/

set_option autoImplicit false
noncomputable section

open scoped BigOperators ENNReal
open Finset

namespace Qatlib.Papers.GevreyGrad19.MainResults.QFT
open Qatlib.Papers.GevreyGrad19.MainResults

private lemma cosineSum_lower_bound (p : ℤ) (hp : 0 < p) (δ : ℝ)
    (hd : |δ| ≤ Real.pi / (16 * p)) :
    4 * (p : ℝ) ≤ ∑ k ∈ Ico (-(8 * p)) (8 * p), Real.cos (δ * k) := by
  have hp' : (0 : ℝ) < p := by exact_mod_cast hp
  have hbound (c k : ℤ) (hk : k ∈ Ico (-(c * p)) (c * p)) :
      |δ * k| ≤ Real.pi / 16 * c := by
    have hk' : |k| ≤ c * p := abs_le.mpr ⟨(mem_Ico.mp hk).1, (mem_Ico.mp hk).2.le⟩
    calc
      _ = |δ| * |(k : ℝ)| := abs_mul _ _
      _ ≤ Real.pi / (16 * p) * (c * p) :=
        mul_le_mul hd (by exact_mod_cast hk') (abs_nonneg _) (by positivity)
      _ = _ := by field_simp
  have hcos (k : ℤ) (hk : k ∈ Ico (-(8 * p)) (8 * p)) : 0 ≤ Real.cos (δ * k) := by
    have h := abs_le.mp (hbound 8 k hk)
    apply Real.cos_nonneg_of_mem_Icc; constructor <;> norm_num at h ⊢ <;> linarith
  have hsub : Ico (-(4 * p)) (4 * p) ⊆ Ico (-(8 * p)) (8 * p) := by
    intro k hk; rw [mem_Ico] at *; constructor <;> omega
  calc
    _ = ∑ _k ∈ Ico (-(4 * p)) (4 * p), (1 / 2 : ℝ) := by
      have hc := Int.card_Ico_of_le (-(4 * p)) (4 * p) (by omega)
      have hc' : ((Ico (-(4 * p)) (4 * p)).card : ℝ) = 4 * p - -(4 * p) := by exact_mod_cast hc
      rw [sum_const, nsmul_eq_mul, hc']; ring
    _ ≤ ∑ k ∈ Ico (-(4 * p)) (4 * p), Real.cos (δ * k) := by
      apply sum_le_sum; intro k hk; have h := hbound 4 k hk
      rw [← Real.cos_pi_div_three, ← Real.cos_abs (δ * k)]
      apply Real.cos_le_cos_of_nonneg_of_le_pi (abs_nonneg _) (by linarith [Real.pi_pos])
      nlinarith [Real.pi_pos]
    _ ≤ _ := sum_le_sum_of_subset_of_nonneg hsub (fun k hk _ => hcos k hk)

/-- **Theorem 3.12**, p. 33: for `n ≥ 4` and `a ∈ [−2π/3, 2π/3]`, the
computational-basis measurement of
`QFT_{2^n}† (2^{-n/2} Σ_k e^{i a k}|k⟩)` satisfies
`P[|b − 2^n a/(2π)| ≤ 4] ≥ 5/6`. -/
theorem qftRobustness (n : ℕ) (hn : 4 ≤ n) (a : ℝ)
    (ha : |a| ≤ 2 * Real.pi / 3) :
    (5 : ℝ) / 6 ≤
      ∑ b ∈ (Finset.Ico (-(2 ^ (n - 1) : ℤ)) (2 ^ (n - 1) : ℤ)).filter
        (fun b : ℤ => |(b : ℝ) - (2 : ℝ) ^ n * a / (2 * Real.pi)| ≤ 4),
        qftOutcomeProb n a b := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 4 := ⟨n - 4, by omega⟩
  let p : ℤ := 2 ^ m
  have hp : (1 : ℝ) ≤ p := by dsimp [p]; exact_mod_cast (one_le_pow₀ (by norm_num : (1 : ℤ) ≤ 2))
  have hN : (2 : ℝ) ^ (m + 4) = 16 * p := by norm_num [p, pow_add]; ring
  have hH : (2 : ℤ) ^ (m + 4 - 1) = 8 * p := by norm_num [p, show m + 4 - 1 = m + 3 by omega, pow_add]; ring
  let x : ℝ := 16 * p * a / (2 * Real.pi)
  let b : ℤ := ⌊x + 1 / 2⌋
  have hb : |(b : ℝ) - x| ≤ 1 / 2 := by
    rw [abs_le]; dsimp [b]; constructor <;>
      linarith [Int.floor_le (x + 1 / 2), Int.lt_floor_add_one (x + 1 / 2)]
  have hx : |x| ≤ 16 * p / 3 := by
    dsimp [x]; rw [abs_div, abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 16 * p),
      abs_of_pos (by positivity : 0 < 2 * Real.pi)]
    apply (div_le_iff₀ (by positivity)).2; nlinarith [ha]
  have hmem : b ∈ Ico (-(8 * p)) (8 * p) := by
    have h : -(8 * (p : ℝ)) ≤ b ∧ (b : ℝ) < 8 * p := by
      rcases abs_le.mp hb with ⟨hb₁, hb₂⟩
      rcases abs_le.mp hx with ⟨hx₁, hx₂⟩; constructor <;> linarith
    rw [mem_Ico]; exact_mod_cast h
  let δ : ℝ := (2 * Real.pi / (16 * p)) * (x - b)
  have hd : |δ| ≤ Real.pi / (16 * p) := by
    dsimp only [δ]; rw [abs_mul, abs_of_pos (by positivity), abs_sub_comm]
    convert mul_le_mul_of_nonneg_left hb (by positivity : 0 ≤ 2 * Real.pi / (16 * p)) using 1; ring
  have hphase (k : ℤ) : a * k - 2 * Real.pi * k * b / (16 * p) = δ * k := by
    dsimp [δ, x]; field_simp
  have hre : (qftAmplitude (m + 4) a b).re = (Real.sqrt (16 * p))⁻¹ *
      ∑ k ∈ Ico (-(8 * p)) (8 * p), Real.cos (δ * k) := by
    simp only [qftAmplitude, hN, hH, Complex.mul_re, Complex.re_sum,
      Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero, hphase,
      mul_comm Complex.I, Complex.exp_ofReal_mul_I_re]
  have hrebound : 1 ≤ (qftAmplitude (m + 4) a b).re := by
    rw [hre, ← div_eq_inv_mul, le_div_iff₀ (Real.sqrt_pos.2 (by positivity)), one_mul]
    refine le_trans (Real.sqrt_le_iff.mpr ⟨by positivity, ?_⟩)
      (cosineSum_lower_bound p (by positivity) δ hd)
    nlinarith [sq_nonneg ((p : ℝ) - 1)]
  have hprob : (5 : ℝ) / 6 ≤ qftOutcomeProb (m + 4) a b := by
    dsimp [qftOutcomeProb]; rw [Complex.normSq_apply]
    nlinarith [sq_nonneg (qftAmplitude (m + 4) a b).im]
  apply hprob.trans
  apply single_le_sum (fun k _ => Complex.normSq_nonneg _)
  rw [mem_filter, hH, hN]; exact ⟨hmem, hb.trans (by norm_num)⟩

end Qatlib.Papers.GevreyGrad19.MainResults.QFT
