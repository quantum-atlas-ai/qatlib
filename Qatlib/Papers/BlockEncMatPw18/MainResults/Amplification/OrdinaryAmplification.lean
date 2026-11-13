/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.VarTimeAmpAmp10.CoherentAA.TightAASuccessBound

set_option backward.isDefEq.respectTransparency false

/-!
# Efficiency and Ratio Bounds for Ordinary Amplitude Amplification

This module proves Lemma 20 and Corollary 21 on the trigonometric amplification profile
of `k` ordinary amplitude amplification steps (`n = 2k + 1`, initial angle `θ = arcsin α`,
no-overamplification window `n θ ≤ π / 2`).

## Main statements

* `lemma20_amplification_lower_bound`: `sin(n θ) ≥ √(1 - n^2 sin^2 θ / 3) * (n sin θ)`.
* `cor21_amplification_ratio`: `n sin θ / sin(n θ) ≤ 1 + (3 / 2) sin^2(n θ)`.

## References

* [Chakraborty, Gilyen, and Jeffery, 2018][ChakrabortyGilyenJeffery2018],
  Lemma 20 and Corollary 21, Section 3, pp. 19--20.
-/

set_option autoImplicit false
noncomputable section

open Matrix Qatlib.Foundations.PureStateMath
open Qatlib.Papers.VarTimeAmpAmp10.CoherentAA
open scoped Matrix.Norms.L2Operator BigOperators

namespace Qatlib.Papers.BlockEncMatPw18.MainResults.Amplification

/-- **Lemma 20 (efficiency of ordinary amplitude amplification)**: for `0 ≤ θ ≤ π / 2`
and `(n : ℝ) * θ ≤ π / 2`, `sin(n θ) ≥ √(1 - n^2 sin^2 θ / 3) * (n sin θ)`. -/
theorem lemma20_amplification_lower_bound (n : ℕ) (θ : ℝ)
    (hθ : 0 ≤ θ) (hθpi : θ ≤ Real.pi / 2)
    (hwin : (n : ℝ) * θ ≤ Real.pi / 2) :
    Real.sin ((n : ℝ) * θ) ≥
      Real.sqrt (1 - (n : ℝ) ^ 2 * Real.sin θ ^ 2 / 3) * ((n : ℝ) * Real.sin θ) := by
  have hsq := clause88_tight_sin_sq n θ hθ hθpi hwin
  have hsin0 : 0 ≤ Real.sin θ :=
    Real.sin_nonneg_of_nonneg_of_le_pi hθ (by linarith [Real.pi_pos])
  have hn0 : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
  have hx0 : 0 ≤ (n : ℝ) * θ := mul_nonneg hn0 hθ
  have ht3 : (n : ℝ) ^ 2 * Real.sin θ ^ 2 ≤ 3 := by
    have h1 : Real.sin θ ^ 2 ≤ θ ^ 2 := Real.sin_sq_le_sq
    have h2 : (n : ℝ) ^ 2 * Real.sin θ ^ 2 ≤ (n : ℝ) ^ 2 * θ ^ 2 := by gcongr
    have h3 : (n : ℝ) ^ 2 * θ ^ 2 = ((n : ℝ) * θ) ^ 2 := by ring
    have h4 : ((n : ℝ) * θ) ^ 2 ≤ (Real.pi / 2) ^ 2 := by nlinarith [hwin, hx0]
    have h5 : (Real.pi / 2) ^ 2 ≤ 3 := by
      have hp := Real.pi_lt_d4
      nlinarith [hp]
    linarith [h2, h4, h5]
  have hnonneg : 0 ≤ 1 - (n : ℝ) ^ 2 * Real.sin θ ^ 2 / 3 := by linarith
  have hy0 : 0 ≤ Real.sqrt (1 - (n : ℝ) ^ 2 * Real.sin θ ^ 2 / 3) *
      ((n : ℝ) * Real.sin θ) :=
    mul_nonneg (Real.sqrt_nonneg _) (mul_nonneg hn0 hsin0)
  have hsx : 0 ≤ Real.sin ((n : ℝ) * θ) :=
    Real.sin_nonneg_of_nonneg_of_le_pi hx0 (by linarith [Real.pi_pos])
  have hsq' : (Real.sqrt (1 - (n : ℝ) ^ 2 * Real.sin θ ^ 2 / 3) *
      ((n : ℝ) * Real.sin θ)) ^ 2 ≤ Real.sin ((n : ℝ) * θ) ^ 2 := by
    rw [mul_pow, Real.sq_sqrt hnonneg]
    nlinarith [hsq]
  have hle := Real.sqrt_le_sqrt hsq'
  rwa [Real.sqrt_sq hy0, Real.sqrt_sq hsx] at hle

/-- **Corollary 21 (amplification ratio bound)**: in the no-overamplification regime
`0 ≤ θ ≤ π / 2` and `(n : ℝ) * θ ≤ π / 2`,
`n * sin θ / sin(n θ) ≤ 1 + (3 / 2) * sin(n θ)^2`. -/
theorem cor21_amplification_ratio (n : ℕ) (θ : ℝ)
    (hθ : 0 ≤ θ) (_hθpi : θ ≤ Real.pi / 2)
    (hwin : (n : ℝ) * θ ≤ Real.pi / 2) :
    (n : ℝ) * Real.sin θ / Real.sin ((n : ℝ) * θ) ≤
      1 + (3 / 2) * Real.sin ((n : ℝ) * θ) ^ 2 := by
  let x : ℝ := (n : ℝ) * θ
  let s : ℝ := Real.sin x
  have hn0 : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
  have hx0 : 0 ≤ x := mul_nonneg hn0 hθ
  have hxwin : x ≤ Real.pi / 2 := hwin
  have hs0 : 0 ≤ s :=
    Real.sin_nonneg_of_nonneg_of_le_pi hx0 (by linarith [Real.pi_pos])
  change (n : ℝ) * Real.sin θ / s ≤ 1 + (3 / 2) * s ^ 2
  rcases eq_or_lt_of_le hs0 with hs | hs
  · rw [← hs, div_zero]
    norm_num
  rw [div_le_iff₀ hs]
  have hx2 : x ^ 2 ≤ 3 := by
    have hsq := pow_le_pow_left₀ hx0 hxwin 2
    nlinarith [Real.pi_lt_d4, Real.pi_pos]
  let s₀ : ℝ := x - x ^ 3 / 6
  let q : ℝ := 1 - x ^ 2 / 6
  have hq : (1 / 2 : ℝ) ≤ q := by dsimp [q]; linarith
  have hs₀0 : 0 ≤ s₀ := by
    have heq : s₀ = x * q := by dsimp [s₀, q]; ring
    rw [heq]
    exact mul_nonneg hx0 (by linarith)
  have hq3 := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 1 / 2) hq 3
  have hcoef : 0 ≤ (3 / 2 : ℝ) * q ^ 3 - 1 / 6 := by linarith
  have hid : (1 + (3 / 2 : ℝ) * s₀ ^ 2) * s₀ - x =
      x ^ 3 * ((3 / 2) * q ^ 3 - 1 / 6) := by dsimp [s₀, q]; ring
  have hxs₀ : x ≤ (1 + (3 / 2 : ℝ) * s₀ ^ 2) * s₀ := by
    linarith only [hid, mul_nonneg (pow_nonneg hx0 3) hcoef]
  have hs₀s : s₀ ≤ s := clause88_sin_ge_sub_cube x hx0
  calc
    (n : ℝ) * Real.sin θ ≤ x := mul_le_mul_of_nonneg_left (Real.sin_le hθ) hn0
    _ ≤ (1 + (3 / 2) * s₀ ^ 2) * s₀ := hxs₀
    _ ≤ (1 + (3 / 2) * s ^ 2) * s := by gcongr

end Qatlib.Papers.BlockEncMatPw18.MainResults.Amplification
