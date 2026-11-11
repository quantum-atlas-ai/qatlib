/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Real.Sqrt

/-!
# Scalar work comparison for the Haar transform

The scalar quantities `sampleSize` and `haarWorkFactor` encode the classical three-sigma sample
threshold and the Haar work factor. Their comparison reduces to an explicit polynomial
inequality under `0 < M` and `2 * M < N`. This development supports the treatment in
[Cornwell2014].

## Main statements

* `sampleSize_threeSigma_intersection`: equality of the two three-sigma endpoints.
* `haarWins_iff`: the exact algebraic work comparison.
* `haarWins_of_cubic`: a sufficient cubic inequality for the Haar advantage.

## References

* [Cornwell, 2014][Cornwell2014]
-/

set_option autoImplicit false

namespace Qatlib.Papers.AmpTransform14.ScalarHaar

noncomputable section

/-- The scalar sample threshold `36 * M * (1 - M/N) / (1 - 2 * M/N)^2` used in the three-sigma
comparison. -/
def sampleSize (M N : ℝ) : ℝ := 36 * M * (1 - M / N) / (1 - 2 * M / N) ^ 2

/-- The scalar Haar work factor `sqrt(N/(2 * M))`. -/
def haarWorkFactor (M N : ℝ) : ℝ := Real.sqrt (N / (2 * M))

/-- For positive `M` and nonnegative `N`, the squared Haar work factor equals `N/(2 * M)`. -/
@[simp]
theorem haarWorkFactor_sq {M N : ℝ} (hM : 0 < M) (hN : 0 ≤ N) :
    haarWorkFactor M N ^ 2 = N / (2 * M) := by
  unfold haarWorkFactor
  rw [Real.sq_sqrt (by positivity)]

/-- The sample threshold is positive when `0 < M` and `2 * M < N`. -/
theorem sampleSize_pos {M N : ℝ} (hM : 0 < M) (hMN : 2 * M < N) : 0 < sampleSize M N := by
  have hN : 0 < N := by linarith
  have h1 : 0 < 1 - M / N := by
    rw [sub_pos, div_lt_one hN]
    linarith
  have h2 : 0 < 1 - 2 * M / N := by
    rw [sub_pos, div_lt_one hN]
    linarith
  unfold sampleSize
  positivity

/-- For `0 < M` and `2 * M < N`, multiplying the sample threshold by `(1 - 2 * M/N)^2` yields
`36 * M * (1 - M/N)`. -/
theorem sampleSize_spec {M N : ℝ} (hM : 0 < M) (hMN : 2 * M < N) :
    sampleSize M N * (1 - 2 * M / N) ^ 2 = 36 * M * (1 - M / N) := by
  have hN : 0 < N := by linarith
  have h2 : (1 : ℝ) - 2 * M / N ≠ 0 := by
    have : 0 < 1 - 2 * M / N := by
      rw [sub_pos, div_lt_one hN]
      linarith
    linarith
  have h2 : (1 - 2 * M / N) ^ 2 ≠ 0 := by
    have h3 : 0 < 1 - 2 * M / N := by
      rw [sub_pos, div_lt_one hN]
      linarith
    positivity
  unfold sampleSize
  exact div_mul_cancel₀ _ h2

/-- At `sampleSize`, the upper three-sigma endpoint around `M/N` equals the lower three-sigma
endpoint around `1 - M/N`, assuming `0 < M` and `2 * M < N`. -/
theorem sampleSize_threeSigma_intersection {M N : ℝ} (hM : 0 < M) (hMN : 2 * M < N) :
    M / N + 3 * Real.sqrt (M * (1 - M / N) / sampleSize M N)
      = (1 - M / N) - 3 * Real.sqrt (M * (1 - M / N) / sampleSize M N) := by
  have hN : 0 < N := by linarith
  have hpos : 0 < 1 - 2 * M / N := by
    rw [sub_pos, div_lt_one hN]
    linarith
  have hs : Real.sqrt (M * (1 - M / N) / sampleSize M N) = (1 - 2 * M / N) / 6 := by
    have hq : M * (1 - M / N) / sampleSize M N = ((1 - 2 * M / N) / 6) ^ 2 := by
      rw [show ((1 - 2 * M / N) / 6) ^ 2 = (1 - 2 * M / N) ^ 2 / 36 by ring]
      have hspec := sampleSize_spec hM hMN
      have hn : sampleSize M N ≠ 0 := ne_of_gt (sampleSize_pos hM hMN)
      have h1 : sampleSize M N * (1 - 2 * M / N) ^ 2 = 36 * (M * (1 - M / N)) := by
        rw [hspec]; ring
      rw [div_eq_div_iff hn (by norm_num : (36:ℝ) ≠ 0)]
      nlinarith [h1]
    rw [hq, Real.sqrt_sq (by linarith)]
  rw [hs]
  ring

/-- For `0 < M` and `2 * M < N`, Haar work is below the sample threshold exactly when `N * (1 -
2 * M/N)^4 < 2592 * M^3 * (1 - M/N)^2` [Cornwell2014]. -/
theorem haarWins_iff {M N : ℝ} (hM : 0 < M) (hMN : 2 * M < N) :
    haarWorkFactor M N < sampleSize M N
      ↔ N * (1 - 2 * M / N) ^ 4 < 2592 * M ^ 3 * (1 - M / N) ^ 2 := by
  have hN : 0 < N := by linarith
  have hpos : 0 < 1 - 2 * M / N := by
    rw [sub_pos, div_lt_one hN]
    linarith
  have hn : 0 < sampleSize M N := sampleSize_pos hM hMN
  have hspec := sampleSize_spec hM hMN
  have hsq : sampleSize M N ^ 2
      = 1296 * M ^ 2 * (1 - M / N) ^ 2 / (1 - 2 * M / N) ^ 4 := by
    have hsquare : sampleSize M N ^ 2 * (1 - 2 * M / N) ^ 4
        = (36 * M * (1 - M / N)) ^ 2 := by
      have hs := congrArg (fun z : ℝ => z ^ 2) hspec
      calc sampleSize M N ^ 2 * (1 - 2 * M / N) ^ 4
          = (sampleSize M N * (1 - 2 * M / N) ^ 2) ^ 2 := by ring
        _ = (36 * M * (1 - M / N)) ^ 2 := hs
    rw [eq_div_iff (by positivity : ((1 - 2 * M / N) ^ 4) ≠ 0), hsquare]
    ring
  have h2M : 0 < 2 * M := by linarith
  have hden : 0 < (1 - 2 * M / N) ^ 4 := by positivity
  have key : N / (2 * M) < 1296 * M ^ 2 * (1 - M / N) ^ 2 / (1 - 2 * M / N) ^ 4
      ↔ N * (1 - 2 * M / N) ^ 4 < 2592 * M ^ 3 * (1 - M / N) ^ 2 := by
    rw [lt_div_iff₀ hden, div_mul_eq_mul_div, div_lt_iff₀ h2M,
      show 1296 * M ^ 2 * (1 - M / N) ^ 2 * (2 * M)
          = 2592 * M ^ 3 * (1 - M / N) ^ 2 by ring]
  rw [haarWorkFactor, Real.sqrt_lt' hn, hsq]
  exact key

/-- Under `0 < M` and `2 * M < N`, the inequality `N < 2592 * M^3 * (1 - M/N)^2` suffices for
Haar work to be below the sample threshold. -/
theorem haarWins_of_cubic {M N : ℝ} (hM : 0 < M) (hMN : 2 * M < N)
    (hcubic : N < 2592 * M ^ 3 * (1 - M / N) ^ 2) :
    haarWorkFactor M N < sampleSize M N := by
  have hN : 0 < N := by linarith
  rw [haarWins_iff hM hMN]
  have hpos : 0 < 1 - 2 * M / N := by
    rw [sub_pos, div_lt_one hN]
    linarith
  have hle : 1 - 2 * M / N ≤ 1 := by
    have h2 : 0 < 2 * M / N := by positivity
    linarith
  have h4 : (1 - 2 * M / N) ^ 4 ≤ 1 := by
    have h1 : (1 - 2 * M / N) ^ 4 ≤ 1 ^ 4 :=
      pow_le_pow_left₀ (le_of_lt hpos) hle 4
    simpa using h1
  have hNB : N * (1 - 2 * M / N) ^ 4 ≤ N := by
    calc N * (1 - 2 * M / N) ^ 4 ≤ N * 1 := by
          exact mul_le_mul_of_nonneg_left h4 (le_of_lt hN)
      _ = N := by ring
  linarith

end

end Qatlib.Papers.AmpTransform14.ScalarHaar
