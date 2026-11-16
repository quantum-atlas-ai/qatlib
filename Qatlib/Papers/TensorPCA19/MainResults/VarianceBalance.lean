/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Ring

@[expose] public section


/-!
# Variance optimization in tensor PCA

The scalar balancing step of arXiv:1907.12724v2, Lemma 13.
The two probabilistic input estimates remain explicit hypotheses.
-/

set_option autoImplicit false

namespace Qatlib.Papers.TensorPCA19.MainResults

/-- Balancing the variance and reciprocal-variance bounds eliminates the variance parameter. -/
theorem variance_balance {a δ d prob σ2 : ℝ}
    (ha : 0 < a) (hδ : 0 < δ) (hd : 0 < d) (hprob : 0 ≤ prob) (hσ : 0 < σ2)
    (hcheb : prob ≤ σ2 / d ^ 2)
    (hcw : prob ≤ (a + 1) * (δ ^ 2 / σ2) ^ ((1 : ℝ) / a)) :
    prob ≤ (δ / d) ^ (2 / (a + 1)) * (a + 1) := by
  rcases hprob.eq_or_lt with hzero | _hpos
  · rw [← hzero]
    positivity
  let B : ℝ := (δ / d) ^ (2 / (a + 1))
  have hB : 0 < B := Real.rpow_pos_of_pos (div_pos hδ hd) _
  have hK : 0 < a + 1 := by linarith
  have hbalance : (δ ^ 2 / (d ^ 2 * B)) ^ ((1 : ℝ) / a) = B := by
    calc
      (δ ^ 2 / (d ^ 2 * B)) ^ ((1 : ℝ) / a)
          = ((δ / d) ^ 2 / B) ^ ((1 : ℝ) / a) := by
            congr 1
            field_simp
      _ = ((δ / d) ^ ((2 : ℝ) - 2 / (a + 1))) ^ ((1 : ℝ) / a) := by
            rw [Real.rpow_sub (div_pos hδ hd), Real.rpow_two]
      _ = (δ / d) ^ (((2 : ℝ) - 2 / (a + 1)) * ((1 : ℝ) / a)) :=
            (Real.rpow_mul (div_pos hδ hd).le _ _).symm
      _ = B := by
            dsimp [B]
            congr 1
            field_simp
            ring
  by_cases hsmall : σ2 ≤ d ^ 2 * B
  · have hp : prob ≤ B := hcheb.trans
      ((div_le_iff₀ (sq_pos_of_pos hd)).2 (by simpa [mul_comm] using hsmall))
    change prob ≤ B * (a + 1)
    nlinarith
  · have hlarge : d ^ 2 * B ≤ σ2 := le_of_lt (lt_of_not_ge hsmall)
    have hratio : δ ^ 2 / σ2 ≤ δ ^ 2 / (d ^ 2 * B) :=
      div_le_div_of_nonneg_left (sq_nonneg δ) (by positivity) hlarge
    have hpow := Real.rpow_le_rpow (by positivity : 0 ≤ δ ^ 2 / σ2) hratio
      (by positivity : 0 ≤ (1 : ℝ) / a)
    rw [hbalance] at hpow
    calc
      prob ≤ (a + 1) * (δ ^ 2 / σ2) ^ ((1 : ℝ) / a) := hcw
      _ ≤ (a + 1) * B := mul_le_mul_of_nonneg_left hpow hK.le
      _ = B * (a + 1) := mul_comm _ _

/-- Source Lemma 13 optimizes the two supplied anti-concentration bounds over the variance. -/
theorem lemma13_carbery_wright (k : ℕ) (hk : 0 < k) {δ t mean : ℝ} (hδ : 0 < δ)
    (hsep : δ < |t - mean|) (prob σ2 : ℝ) (hprob : 0 ≤ prob) (hσ : 0 < σ2)
    (hcheb : prob ≤ σ2 / (|t - mean| - δ) ^ 2)
    (hcw : prob ≤ (2 * (k : ℝ) + 1) * (δ ^ 2 / σ2) ^ ((1 : ℝ) / (2 * (k : ℝ)))) :
    prob ≤ (δ / (|t - mean| - δ)) ^ (2 / (2 * (k : ℝ) + 1)) * (2 * (k : ℝ) + 1) := by
  have hkR : 0 < (k : ℝ) := Nat.cast_pos.mpr hk
  exact variance_balance (by positivity : 0 < 2 * (k : ℝ)) hδ
    (sub_pos.mpr hsep) hprob hσ hcheb hcw

end Qatlib.Papers.TensorPCA19.MainResults
