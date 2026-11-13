/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Data.Int.Order.Lemmas
import Lean.Elab.Tactic.NormCast
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Real.StarOrdered
import Mathlib.Tactic.Ext
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.NormNum.BigOperators
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Qatlib.Papers.HamLCUSim12.Multiproduct.Lemma12IntegerNodesCorrectedStat

/-!
# Bounds for rounded multiproduct nodes

This module proves `lemma12IntegerNodesCorrected`, collecting separation and growth estimates
for `integerNode`, bounds for `correctedGamma`, coefficient-mass estimates, and repetition and
cost bounds. Auxiliary exponential and logarithmic inequalities control the rounding when 0.305
< η < 0.312 and k ≥ 1. See [ChildsWiebe2012] for the multiproduct and linear-combination
simulation framework.

## Main statements

* `lemma12IntegerNodesCorrected`: Establishes the rounded-node parameter, coefficient,
  repetition, and cost bounds in `Lemma12IntegerNodesCorrected`, supporting the analysis of
  Lemma 12 in [ChildsWiebe2012].
* `coeff_consequences`: Under normalization and the stated coefficient bounds, with 0.305 < η <
  0.312 and k ≥ 1, the first k absolute coefficients sum to at most 1 / 8, every coefficient has
  magnitude at most 2, and eight times the negative mass is at most the positive mass.
* `retry_bounds`: For k ≥ 1, m ≥ 1, positive h, t, ε, and 0 < β < 1, `retryCount` is at least 1
  and dominates both the accuracy-dependent bound and 13 log(2 / β).

## References

* [Childs and Wiebe, 2012][ChildsWiebe2012]
-/

namespace Qatlib.Papers.HamLCUSim12.Multiproduct

open Real
open scoped BigOperators

/-- For nonnegative x, each finite initial sum of the exponential series is at most exp x. -/
private lemma exp_ge_partial (x : ℝ) (hx : 0 ≤ x) (n : ℕ) :
    (∑ i ∈ Finset.range n, x ^ i / (i.factorial : ℝ)) ≤ Real.exp x :=
  Real.sum_le_exp_of_nonneg hx n

/-- For nonnegative x, the quadratic Taylor polynomial 1 + x + x² / 2 is at most exp x. -/
private lemma exp_ge_three_terms {x : ℝ} (hx : 0 ≤ x) :
    1 + x + x ^ 2 / 2 ≤ Real.exp x :=
  Real.quadratic_le_exp_of_nonneg hx

/-- For nonnegative x, the cubic Taylor polynomial of the exponential at zero is at most exp x. -/
private lemma exp_ge_four_terms {x : ℝ} (hx : 0 ≤ x) :
    1 + x + x ^ 2 / 2 + x ^ 3 / 6 ≤ Real.exp x := by
  have h := exp_ge_partial x hx 4
  simpa [Finset.sum_range_succ] using! h

/-- For nonnegative x, the degree-four Taylor polynomial of the exponential at zero is at most
exp x. -/
private lemma exp_ge_five_terms {x : ℝ} (hx : 0 ≤ x) :
    1 + x + x ^ 2 / 2 + x ^ 3 / 6 + x ^ 4 / 24 ≤ Real.exp x := by
  have h := exp_ge_partial x hx 5
  simpa [Finset.sum_range_succ] using! h

/-- The exponential at 4 / 5 is at least 2. -/
private lemma two_le_exp_four_fifths : (2:ℝ) ≤ Real.exp (4/5) := by
  have h := exp_ge_three_terms (by norm_num : (0:ℝ) ≤ 4/5)
  norm_num at h
  linarith

/-- The exponential at 6 / 5 is at least 200 / 61. -/
private lemma exp_six_fifths_ge : (200:ℝ)/61 ≤ Real.exp (6/5) := by
  have h := exp_ge_five_terms (by norm_num : (0:ℝ) ≤ 6/5)
  norm_num at h
  linarith

/-- The exponential at 7 / 10 is at least 2. -/
private lemma two_le_exp_seven_tenths : (2:ℝ) ≤ Real.exp (7/10) := by
  have h := exp_ge_four_terms (by norm_num : (0:ℝ) ≤ 7/10)
  norm_num at h
  linarith

/-- The exponential at 1 is at least 543 / 200. -/
private lemma exp_one_ge : (543:ℝ)/200 ≤ Real.exp 1 := by
  have h := exp_ge_partial 1 zero_le_one 7
  norm_num [Finset.sum_range_succ, Nat.factorial] at h
  linarith

/-- The exponential at 1 is at least 163 / 60. -/
private lemma exp_one_ge163 : (163:ℝ)/60 ≤ Real.exp 1 := by
  have h := exp_ge_partial 1 zero_le_one 6
  norm_num [Finset.sum_range_succ, Nat.factorial] at h
  linarith

/-- The exponential at 1 / 4 is at least 985 / 768. -/
private lemma exp_quarter_ge : (985:ℝ)/768 ≤ Real.exp (1/4) := by
  have h := exp_ge_four_terms (by norm_num : (0:ℝ) ≤ 1/4)
  norm_num at h
  linarith

/-- The exponential at 1 is at most 1699 / 625. -/
private lemma exp_one_le : Real.exp 1 ≤ (1699:ℝ)/625 := by
  have h := Real.exp_bound' zero_le_one (le_refl 1) (n := 8) (by norm_num)
  norm_num [Finset.sum_range_succ, Nat.factorial] at h
  linarith

/-- The exponential at 4 / 25 is at most 7335 / 6250. -/
private lemma exp_four25_le : Real.exp (4/25) ≤ (7335:ℝ)/6250 := by
  have h := Real.exp_bound' (by norm_num : (0:ℝ) ≤ 4/25) (by norm_num) (n := 6) (by norm_num)
  norm_num [Finset.sum_range_succ, Nat.factorial] at h
  linarith

/-- The exponential at 431 / 2500 is at most 5941 / 5000. -/
private lemma exp_1704_le : Real.exp (431/2500) ≤ (5941:ℝ)/5000 := by
  have h := Real.exp_bound' (by norm_num : (0:ℝ) ≤ 431/2500) (by norm_num) (n := 5) (by norm_num)
  norm_num [Finset.sum_range_succ, Nat.factorial] at h
  linarith

/-- The exponential at 29 / 25 is at most 125 / 39. -/
private lemma exp_29_25_le : Real.exp (29/25) ≤ (125:ℝ)/39 := by
  have h1 : Real.exp (29/25) = Real.exp 1 * Real.exp (4/25) := by
    rw [← Real.exp_add]
    norm_num
  have hA : (0:ℝ) ≤ (1699:ℝ)/625 := by norm_num
  have hF : (0:ℝ) ≤ (7335:ℝ)/6250 := by norm_num
  rw [h1]
  calc Real.exp 1 * Real.exp (4/25) ≤ ((1699:ℝ)/625) * Real.exp (4/25) :=
        mul_le_mul_of_nonneg_right exp_one_le (Real.exp_pos (4/25)).le
    _ ≤ ((1699:ℝ)/625) * ((7335:ℝ)/6250) :=
        mul_le_mul_of_nonneg_left exp_four25_le hA
    _ ≤ (125:ℝ)/39 := by norm_num

/-- The exponential at 54 / 25 is at most 9. -/
private lemma exp_54_25_le : Real.exp (54/25) ≤ (9:ℝ) := by
  have h1 : Real.exp (54/25) = Real.exp 2 * Real.exp (4/25) := by
    rw [← Real.exp_add]
    norm_num
  have h2 : Real.exp 2 = Real.exp 1 * Real.exp 1 := by
    rw [← Real.exp_add]
    norm_num
  have hA : (0:ℝ) ≤ (1699:ℝ)/625 := by norm_num
  have hAA : (0:ℝ) ≤ ((1699:ℝ)/625) * ((1699:ℝ)/625) := by positivity
  rw [h1, h2]
  calc Real.exp 1 * Real.exp 1 * Real.exp (4/25)
      ≤ ((1699:ℝ)/625) * ((1699:ℝ)/625) * Real.exp (4/25) := by
        refine mul_le_mul_of_nonneg_right ?_ (Real.exp_pos (4/25)).le
        calc Real.exp 1 * Real.exp 1 ≤ ((1699:ℝ)/625) * Real.exp 1 :=
              mul_le_mul_of_nonneg_right exp_one_le (Real.exp_pos 1).le
          _ ≤ ((1699:ℝ)/625) * ((1699:ℝ)/625) :=
              mul_le_mul_of_nonneg_left exp_one_le hA
    _ ≤ ((1699:ℝ)/625) * ((1699:ℝ)/625) * ((7335:ℝ)/6250) :=
        mul_le_mul_of_nonneg_left exp_four25_le hAA
    _ ≤ 9 := by norm_num

/-- The exponential at 21 / 4 is at least 882 / 5. -/
private lemma exp_21_4_ge : (882:ℝ)/5 ≤ Real.exp (21/4) := by
  have h1 : Real.exp (21/4) = Real.exp 5 * Real.exp (1/4) := by
    rw [← Real.exp_add]
    norm_num
  have h5 : Real.exp 5 = (Real.exp 1) ^ 5 := by
    rw [← Real.exp_nat_mul]
    norm_num
  have hQ : (0:ℝ) ≤ (985:ℝ)/768 := by norm_num
  have hE : (0:ℝ) ≤ (Real.exp 1) ^ 5 := pow_nonneg (Real.exp_pos 1).le 5
  have hp : ((543:ℝ)/200) ^ 5 ≤ (Real.exp 1) ^ 5 :=
    pow_le_pow_left₀ (by norm_num : (0:ℝ) ≤ (543:ℝ)/200) exp_one_ge 5
  have hlow : ((543:ℝ)/200) ^ 5 * ((985:ℝ)/768) ≤ (Real.exp 1) ^ 5 * Real.exp (1/4) := by
    calc ((543:ℝ)/200) ^ 5 * ((985:ℝ)/768) ≤ (Real.exp 1) ^ 5 * ((985:ℝ)/768) :=
          mul_le_mul_of_nonneg_right hp hQ
      _ ≤ (Real.exp 1) ^ 5 * Real.exp (1/4) :=
          mul_le_mul_of_nonneg_left exp_quarter_ge hE
  calc (882:ℝ)/5 ≤ ((543:ℝ)/200) ^ 5 * ((985:ℝ)/768) := by norm_num
    _ ≤ (Real.exp 1) ^ 5 * Real.exp (1/4) := hlow
    _ = Real.exp (21/4) := by rw [h1, h5]

/-- The natural logarithm of 2 is at most 7 / 10. -/
private lemma log_two_le : Real.log 2 ≤ 7/10 := by
  rw [Real.log_le_iff_le_exp two_pos]
  exact two_le_exp_seven_tenths

/-- For every positive natural number k, twice k is at most 2^k. -/
private lemma two_mul_le_two_pow : ∀ k : ℕ, 1 ≤ k → 2 * k ≤ 2 ^ k
  | 1, _ => by norm_num
  | k + 2, _ => by
      have ih : 2 * (k + 1) ≤ 2 ^ (k + 1) := two_mul_le_two_pow (k + 1) (by omega)
      have h : 2 ^ (k + 1) + 2 ^ (k + 1) = 2 ^ (k + 2) := by ring
      calc 2 * (k + 2) = (2 * (k + 1)) + 2 := by ring
        _ ≤ 2 ^ (k + 1) + 2 ^ (k + 1) := by omega
        _ = 2 ^ (k + 2) := h

/-- If 0.305 < η < 0.312, then −6 / 5 ≤ log η ≤ −29 / 25. -/
private lemma eta_log_bounds {η : ℝ} (h1 : 305/1000 < η) (h2 : η < 312/1000) :
    -(6/5:ℝ) ≤ Real.log η ∧ Real.log η ≤ -(29/25:ℝ) := by
  constructor
  · have hiv : (Real.exp (6/5))⁻¹ ≤ ((200:ℝ)/61)⁻¹ :=
      (inv_le_inv₀ (by positivity) (by positivity)).mpr exp_six_fifths_ge
    have h3 : Real.exp (-(6/5:ℝ)) = (Real.exp (6/5))⁻¹ := Real.exp_neg _
    have h4 : ((200:ℝ)/61)⁻¹ = 305/1000 := by norm_num
    have hle : Real.exp (-(6/5:ℝ)) ≤ 305/1000 := by
      rw [h3]
      rw [h4] at hiv
      exact hiv
    exact le_trans (by rw [Real.log_exp])
      (Real.log_le_log (by positivity) (le_trans hle h1.le))
  · rw [Real.log_le_iff_le_exp (by linarith : (0:ℝ) < η)]
    have hiv : ((125:ℝ)/39)⁻¹ ≤ (Real.exp (29/25))⁻¹ :=
      (inv_le_inv₀ (by positivity) (by positivity)).mpr exp_29_25_le
    rw [show ((125:ℝ)/39)⁻¹ = 312/1000 by norm_num] at hiv
    rw [Real.exp_neg]
    exact h2.le.trans hiv

/-- If 0.305 < η < 0.312, then 1 + log η / 2 is at least 2 / 5. -/
private lemma one_add_half_ge {η : ℝ} (h1 : 305/1000 < η) (h2 : η < 312/1000) :
    (2:ℝ)/5 ≤ 1 + Real.log η/2 := by
  have := (eta_log_bounds h1 h2).1
  linarith

/-- If 0.305 < η < 0.312 and k ≥ 1, then `gammaReq η k` is at most 329 / 200. -/
private lemma gammaReq_le {η : ℝ} (h1 : 305/1000 < η) (h2 : η < 312/1000) {k : ℕ} (hk : 1 ≤ k) :
    gammaReq η k ≤ 329/200 := by
  have hlog := (eta_log_bounds h1 h2).2
  have hK : (1:ℝ) ≤ (k:ℝ) := by exact_mod_cast hk
  have hK0 : (0:ℝ) < (k:ℝ) := lt_of_lt_of_le zero_lt_one hK
  have hlog2k : Real.log ((2*(k:ℝ)):ℝ) ≤ (k:ℝ) * Real.log 2 := by
    have h1' : Real.log ((2*(k:ℝ)):ℝ) ≤ Real.log (((2^k : ℕ):ℝ)) :=
      Real.log_le_log (mul_pos (by norm_num) hK0)
        (by exact_mod_cast two_mul_le_two_pow k hk)
    rw [Nat.cast_pow, Real.log_pow] at h1'
    exact h1'
  have ht : (1/(2*(k:ℝ))) * Real.log (2 * ((2*(k:ℝ)):ℝ)^(5/2:ℝ)) ≤ (49:ℝ)/40 := by
    have hL : Real.log (2 * ((2*(k:ℝ)):ℝ)^(5/2:ℝ))
        = Real.log 2 + (5/2) * Real.log ((2*(k:ℝ)):ℝ) := by
      rw [Real.log_mul (by norm_num) (by positivity),
        Real.log_rpow (mul_pos (by norm_num) hK0)]
    have hB : (5/2) * Real.log ((2*(k:ℝ)):ℝ) ≤ (5/2) * ((k:ℝ) * Real.log 2) :=
      mul_le_mul_of_nonneg_left hlog2k (by norm_num : (0:ℝ) ≤ 5/2)
    have hstep1 : (1/(2*(k:ℝ))) * Real.log (2 * ((2*(k:ℝ)):ℝ)^(5/2:ℝ))
        ≤ (1/(2*(k:ℝ))) * (Real.log 2 + (5/2) * ((k:ℝ) * Real.log 2)) :=
      mul_le_mul_of_nonneg_left (by rw [hL]; exact add_le_add (le_refl _) hB) (by positivity)
    have hlog2nn : (0:ℝ) ≤ Real.log 2 := Real.log_nonneg (by norm_num : (1:ℝ) ≤ 2)
    have hstep2 : (1/(2*(k:ℝ))) * (Real.log 2 + (5/2) * ((k:ℝ) * Real.log 2))
        ≤ (7/4) * Real.log 2 := by
      rw [div_mul_eq_mul_div, div_mul_eq_mul_div,
        div_le_iff₀ (mul_pos (by norm_num) hK0)]
      nlinarith [hK, hlog2nn]
    calc (1/(2*(k:ℝ))) * Real.log (2 * ((2*(k:ℝ)):ℝ)^(5/2:ℝ))
        ≤ (1/(2*(k:ℝ))) * (Real.log 2 + (5/2) * ((k:ℝ) * Real.log 2)) := hstep1
      _ ≤ (7/4) * Real.log 2 := hstep2
      _ ≤ (7/4) * (7/10) := mul_le_mul_of_nonneg_left log_two_le (by norm_num : (0:ℝ) ≤ 7/4)
      _ = 49/40 := by norm_num
  have hbase : 1 + Real.log η/2 ≤ 21/50 := by linarith
  unfold gammaReq
  linarith

/-- For k ≥ 1, expands (k + 1) · `gammaReq η k` into its base term and logarithmic correction. -/
private lemma kp1_gammaReq_split (η : ℝ) {k : ℕ} (hk : 1 ≤ k) :
    ((k+1:ℕ):ℝ) * gammaReq η k
      = ((k+1:ℕ):ℝ) * (1 + Real.log η/2)
        + (((k+1:ℕ):ℝ)/(2*(k:ℝ)))
          * Real.log (2 * ((2*(k:ℝ)):ℝ)^(5/2:ℝ)) := by
  have hK0 : (0:ℝ) < (k:ℝ) := by
    have : (1:ℝ) ≤ (k:ℝ) := by exact_mod_cast hk
    linarith
  unfold gammaReq
  field_simp

/-- For k ≥ 1, exponentiating half of log(2 (2k)^(5/2)) gives 2^(1/2) (2k)^(5/4). -/
private lemma exp_half_log (k : ℕ) (hk : 1 ≤ k) :
    Real.exp (((1:ℝ)/2) * Real.log (2 * ((2*(k:ℝ)):ℝ)^(5/2:ℝ)))
      = ((2:ℝ)^(1/2:ℝ)) * ((2*(k:ℝ)):ℝ)^(5/4:ℝ) := by
  have hK1 : (1:ℝ) ≤ (k:ℝ) := by exact_mod_cast hk
  have hpos : (0:ℝ) < ((2*(k:ℝ)):ℝ)^(5/2:ℝ) := Real.rpow_pos_of_pos (by nlinarith) _
  have hpos2 : (0:ℝ) < 2 * ((2*(k:ℝ)):ℝ)^(5/2:ℝ) := mul_pos (by norm_num) hpos
  have hstep1 : Real.exp (((1:ℝ)/2) * Real.log (2 * ((2*(k:ℝ)):ℝ)^(5/2:ℝ)))
      = (2 * ((2*(k:ℝ)):ℝ)^(5/2:ℝ))^(1/2:ℝ) := by
    rw [mul_comm, Real.exp_mul, Real.exp_log hpos2]
  have hstep2 : (2 * ((2*(k:ℝ)):ℝ)^(5/2:ℝ))^(1/2:ℝ)
      = ((2:ℝ)^(1/2:ℝ)) * (((2*(k:ℝ)):ℝ)^(5/2:ℝ))^(1/2:ℝ) :=
    Real.mul_rpow (by norm_num) (Real.rpow_nonneg (by nlinarith) _)
  have hstep3 : (((2*(k:ℝ)):ℝ)^(5/2:ℝ))^(1/2:ℝ) = ((2*(k:ℝ)):ℝ)^(5/4:ℝ) := by
    rw [← Real.rpow_mul (show (0:ℝ) ≤ (2*(k:ℝ)) by nlinarith),
      show ((5:ℝ)/2)*((1:ℝ)/2) = (5:ℝ)/4 by norm_num]
  rw [hstep1, hstep2, hstep3]

/-- If 0.305 < η < 0.312 and k ≥ 1, the unrounded terminal node exp((k + 1) · `gammaReq η k`) is
at least 4k. -/
private lemma exp_gammaReq_node_ge {η : ℝ} (h1 : 305/1000 < η) (h2 : η < 312/1000) {k : ℕ}
    (hk : 1 ≤ k) : (4:ℝ)*(k:ℝ) ≤ Real.exp (((k+1:ℕ):ℝ) * gammaReq η k) := by
  have hK1 : (1:ℝ) ≤ (k:ℝ) := by exact_mod_cast hk
  have hK0 : (0:ℝ) < (k:ℝ) := lt_of_lt_of_le zero_lt_one hK1
  have hbase : (2:ℝ)/5 ≤ 1 + Real.log η/2 := one_add_half_ge h1 h2
  have hLnn : (0:ℝ) ≤ Real.log (2 * ((2*(k:ℝ)):ℝ)^(5/2:ℝ)) := by
    apply Real.log_nonneg
    have hrw : (1:ℝ) ≤ ((2*(k:ℝ)):ℝ)^(5/2:ℝ) := Real.one_le_rpow (by nlinarith) (by norm_num)
    have hpos : (0:ℝ) < ((2*(k:ℝ)):ℝ)^(5/2:ℝ) := Real.rpow_pos_of_pos (by nlinarith) _
    nlinarith [hrw, mul_pos (by norm_num : (0:ℝ) < 2) hpos]
  have hsplit := kp1_gammaReq_split η hk
  have hA : (4:ℝ)/5 ≤ ((k+1:ℕ):ℝ) * (1 + Real.log η/2) := by
    have hkp1 : (2:ℝ) ≤ ((k+1:ℕ):ℝ) := by
      have hn : (2:ℕ) ≤ k+1 := by omega
      exact_mod_cast hn
    calc (4:ℝ)/5 = (2:ℝ) * ((2:ℝ)/5) := by ring
      _ ≤ ((k+1:ℕ):ℝ) * ((2:ℝ)/5) := mul_le_mul_of_nonneg_right hkp1 (by norm_num)
      _ ≤ ((k+1:ℕ):ℝ) * (1 + Real.log η/2) := mul_le_mul_of_nonneg_left hbase (by nlinarith)
  have hratio : ((1:ℝ)/2) ≤ ((k+1:ℕ):ℝ)/(2*(k:ℝ)) := by
    rw [le_div_iff₀ (mul_pos (by norm_num) hK0)]
    have hcast : ((k+1:ℕ):ℝ) = (k:ℝ) + 1 := by
      push_cast
      ring
    rw [hcast]
    linarith
  have hB : ((1:ℝ)/2) * Real.log (2 * ((2*(k:ℝ)):ℝ)^(5/2:ℝ))
      ≤ (((k+1:ℕ):ℝ)/(2*(k:ℝ))) * Real.log (2 * ((2*(k:ℝ)):ℝ)^(5/2:ℝ)) :=
    mul_le_mul_of_nonneg_right hratio hLnn
  have hsum : (4:ℝ)/5 + ((1:ℝ)/2)
      * Real.log (2 * ((2*(k:ℝ)):ℝ)^(5/2:ℝ)) ≤ ((k+1:ℕ):ℝ) * gammaReq η k := by
    rw [hsplit]
    linarith
  have hsqr : (1:ℝ) ≤ ((2:ℝ)^(1/2:ℝ)) :=
    Real.one_le_rpow (by norm_num : (1:ℝ) ≤ 2) (by norm_num : (0:ℝ) ≤ 1/2)
  have h54 : ((2*(k:ℝ)):ℝ)^(5/4:ℝ) ≥ ((2*(k:ℝ)):ℝ) := by
    have hmono := Real.rpow_le_rpow_left_iff (by nlinarith : (1:ℝ) < 2*(k:ℝ)) |>.mpr
      (by norm_num : (1:ℝ) ≤ 5/4)
    rwa [Real.rpow_one] at hmono
  have hmid : (2:ℝ)*(k:ℝ) ≤ ((2:ℝ)^(1/2:ℝ)) * ((2*(k:ℝ)):ℝ)^(5/4:ℝ) := by
    have h := mul_le_mul hsqr h54 (mul_nonneg (by norm_num : (0:ℝ) ≤ (2:ℝ)) hK0.le)
      (Real.rpow_nonneg (by norm_num) _)
    simpa using h
  have hexp45 : (2:ℝ) ≤ Real.exp ((4:ℝ)/5) := two_le_exp_four_fifths
  have hcand : (0:ℝ) ≤ ((2:ℝ)^(1/2:ℝ)) * ((2*(k:ℝ)):ℝ)^(5/4:ℝ) := by
    have h1 : (0:ℝ) ≤ ((2:ℝ)^(1/2:ℝ)) :=
      Real.rpow_nonneg (by norm_num) _
    have h2 : (0:ℝ) ≤ ((2*(k:ℝ)):ℝ)^(5/4:ℝ) :=
      Real.rpow_nonneg (by nlinarith) _
    exact mul_nonneg h1 h2
  have hmono : Real.exp ((4:ℝ)/5) * (((2:ℝ)^(1/2:ℝ)) * ((2*(k:ℝ)):ℝ)^(5/4:ℝ))
      ≤ Real.exp (((k+1:ℕ):ℝ) * gammaReq η k) := by
    have h0 : Real.exp ((4:ℝ)/5 + ((1:ℝ)/2)
        * Real.log (2 * ((2*(k:ℝ)):ℝ)^(5/2:ℝ)))
        ≤ Real.exp (((k+1:ℕ):ℝ) * gammaReq η k) := Real.exp_le_exp.mpr hsum
    rw [Real.exp_add, exp_half_log k hk] at h0
    exact h0
  calc (4:ℝ)*(k:ℝ) = (2:ℝ) * ((2:ℝ)*(k:ℝ)) := by ring
    _ ≤ (2:ℝ) * (((2:ℝ)^(1/2:ℝ)) * ((2*(k:ℝ)):ℝ)^(5/4:ℝ)) :=
          mul_le_mul_of_nonneg_left hmid (by norm_num : (0:ℝ) ≤ (2:ℝ))
    _ ≤ Real.exp ((4:ℝ)/5) * (((2:ℝ)^(1/2:ℝ)) * ((2*(k:ℝ)):ℝ)^(5/4:ℝ)) :=
          mul_le_mul_of_nonneg_right hexp45 hcand
    _ ≤ Real.exp (((k+1:ℕ):ℝ) * gammaReq η k) := hmono

/-- If 0.305 < η < 0.312 and k ≥ 1, `integerNode η k` is at least 2, exceeds k, and has square
at least 2k². -/
private lemma node_bounds {η : ℝ} (h1 : 305/1000 < η) (h2 : η < 312/1000) {k : ℕ} (hk : 1 ≤ k) :
    (2:ℝ) ≤ ((integerNode η k : ℤ):ℝ) ∧ (k:ℝ) < ((integerNode η k : ℤ):ℝ)
    ∧ 2*((k:ℝ))^2 ≤ ((integerNode η k : ℤ):ℝ)^2 := by
  have hK1 : (1:ℝ) ≤ (k:ℝ) := by exact_mod_cast hk
  have h4k : (4:ℝ)*(k:ℝ) ≤ ((integerNode η k : ℤ):ℝ) := by
    have hx : (4:ℝ)*(k:ℝ) ≤ Real.exp (((k+1:ℕ):ℝ) * gammaReq η k) :=
      exp_gammaReq_node_ge h1 h2 hk
    exact le_trans hx (Int.le_ceil _)
  constructor
  · nlinarith
  · constructor
    · nlinarith
    · nlinarith [h4k, hK1]

/-- If 0.305 < η < 0.312 and k ≥ 1, rounding the terminal node gives `gammaReq η k ≤
correctedGamma η k`. -/
private lemma gamma_ge_gammaReq {η : ℝ} (h1 : 305/1000 < η) (h2 : η < 312/1000) {k : ℕ}
    (hk : 1 ≤ k) : gammaReq η k ≤ correctedGamma η k := by
  have hpos : (0:ℝ) < ((integerNode η k : ℤ):ℝ) := by
    have := (node_bounds h1 h2 hk).1
    linarith
  have hlog : ((k+1:ℕ):ℝ) * gammaReq η k ≤ Real.log ((integerNode η k : ℤ):ℝ) := by
    have hstep := Real.log_le_log (Real.exp_pos (((k+1:ℕ):ℝ) * gammaReq η k)) (Int.le_ceil _)
    rwa [Real.log_exp] at hstep
  have hkp1 : (0:ℝ) < ((k+1:ℕ):ℝ) := by
    have hn : (0:ℕ) < k+1 := Nat.succ_pos k
    exact_mod_cast hn
  unfold correctedGamma
  rw [le_div_iff₀ hkp1, mul_comm]
  exact hlog

/-- If 0.305 < η < 0.312 and k ≥ 1, the corrected exponent is at most 2. -/
private lemma gamma_le_two {η : ℝ} (h1 : 305/1000 < η) (h2 : η < 312/1000) {k : ℕ} (hk : 1 ≤ k) :
    correctedGamma η k ≤ 2 := by
  have hpos : (0:ℝ) < ((integerNode η k : ℤ):ℝ) := by
    have := (node_bounds h1 h2 hk).1
    linarith
  have hxe : (2:ℝ) ≤ Real.exp (((k+1:ℕ):ℝ) * gammaReq η k) := by
    have h4k := exp_gammaReq_node_ge h1 h2 hk
    have hK1 : (1:ℝ) ≤ (k:ℝ) := by exact_mod_cast hk
    nlinarith
  have hceil : ((integerNode η k : ℤ):ℝ) < Real.exp (((k+1:ℕ):ℝ) * gammaReq η k) + 1 :=
    Int.ceil_lt_add_one _
  have h15 : ((integerNode η k : ℤ):ℝ) ≤ (3:ℝ)/2 * Real.exp (((k+1:ℕ):ℝ) * gammaReq η k) := by
    nlinarith [hxe, hceil]
  have hkp1 : (0:ℝ) < ((k+1:ℕ):ℝ) := by
    have hn : (0:ℕ) < k+1 := Nat.succ_pos k
    exact_mod_cast hn
  have hlog : Real.log ((integerNode η k : ℤ):ℝ)
      ≤ Real.log ((3:ℝ)/2) + ((k+1:ℕ):ℝ) * gammaReq η k := by
    refine le_trans (Real.log_le_log hpos h15) ?_
    rw [Real.log_mul (by norm_num : ((3:ℝ)/2) ≠ 0) (Real.exp_ne_zero _), Real.log_exp]
  have hlog32 : Real.log ((3:ℝ)/2) ≤ 7/10 :=
    le_trans (Real.log_le_log (by norm_num : (0:ℝ) < 3/2) (by norm_num : (3:ℝ)/2 ≤ 2)) log_two_le
  have hgR : gammaReq η k ≤ 329/200 := gammaReq_le h1 h2 hk
  unfold correctedGamma
  rw [div_le_iff₀ hkp1]
  have hkp1' : ((k+1:ℕ):ℝ) = (k:ℝ) + 1 := by
    push_cast
    ring
  rw [hkp1']
  have hG := mul_le_mul_of_nonneg_left hgR hkp1.le
  have hP2 : (2:ℝ) ≤ (k:ℝ) + 1 := by
    have hK1 : (1:ℝ) ≤ (k:ℝ) := by exact_mod_cast hk
    linarith
  linarith [hlog, hlog32, hG]

/-- If 0.305 < η < 0.312 and k ≥ 1, exponentiating (k + 1) · `correctedGamma η k` recovers the
rounded integer node. -/
private lemma exp_log_node {η : ℝ} (h1 : 305/1000 < η) (h2 : η < 312/1000) {k : ℕ} (hk : 1 ≤ k) :
    Real.exp (correctedGamma η k * ((k+1:ℕ):ℝ)) = ((integerNode η k : ℤ):ℝ) := by
  have hpos : (0:ℝ) < ((integerNode η k : ℤ):ℝ) := by
    have := (node_bounds h1 h2 hk).1
    linarith
  have hkp1 : ((k+1:ℕ):ℝ) ≠ 0 := by
    have : (0:ℝ) < ((k+1:ℕ):ℝ) := by
      have hn : (1:ℕ) ≤ k+1 := by omega
      exact_mod_cast hn
    linarith
  rw [correctedGamma, div_mul_cancel₀ _ hkp1, Real.exp_log hpos]

/-- For k ≥ 1, rewrites 2^(1/2) (2k)^(5/4) as 2^(7/4) k^(5/4). -/
private lemma rpow_two_k (k : ℕ) (hk : 1 ≤ k) :
    ((2:ℝ)^(1/2:ℝ))*((2*(k:ℝ)):ℝ)^(5/4:ℝ) = (2:ℝ)^(7/4:ℝ)*(k:ℝ)^(5/4:ℝ) := by
  have hK0 : (0:ℝ) < (k:ℝ) := by
    have : (1:ℝ) ≤ (k:ℝ) := by exact_mod_cast hk
    linarith
  have h1 : ((2*(k:ℝ)):ℝ)^(5/4:ℝ) = ((2:ℝ)^(5/4:ℝ))*((k:ℝ)^(5/4:ℝ)) :=
    Real.mul_rpow (by norm_num) hK0.le
  rw [h1, ← mul_assoc, ← Real.rpow_add two_pos, show (1:ℝ)/2 + 5/4 = 7/4 by norm_num]

/-- For k ≥ 1, rewrites 2 (2k)^(5/2) as 2^(7/2) k^(5/2). -/
private lemma two_pow_term (k : ℕ) (hk : 1 ≤ k) :
    (2:ℝ)*((2*(k:ℝ)):ℝ)^(5/2:ℝ) = (2:ℝ)^(7/2:ℝ)*(k:ℝ)^(5/2:ℝ) := by
  have hK0 : (0:ℝ) < (k:ℝ) := by
    have : (1:ℝ) ≤ (k:ℝ) := by exact_mod_cast hk
    linarith
  have h1 : ((2*(k:ℝ)):ℝ)^(5/2:ℝ) = ((2:ℝ)^(5/2:ℝ))*((k:ℝ)^(5/2:ℝ)) :=
    Real.mul_rpow (by norm_num) hK0.le
  have h2 : (2:ℝ) * ((2:ℝ)^(5/2:ℝ)) = ((2:ℝ)^(7/2:ℝ)) := by
    have h3 : ((2:ℝ)^(7/2:ℝ)) = ((2:ℝ)^((1:ℝ)+(5/2:ℝ))) := by norm_num
    rw [h3, Real.rpow_add two_pos]
    norm_num
  rw [h1, ← mul_assoc, h2]

/-- For k ≥ 1, the quotient 2^(1/2) k^(3/2) / (2 (2k)^(5/2)) equals 1 / (8k). -/
private lemma coeff_bound_identity (k : ℕ) (hk : 1 ≤ k) :
    ((2:ℝ)^(1/2:ℝ))*((k:ℝ)^(3/2:ℝ)) / (2*((2*(k:ℝ)):ℝ)^(5/2:ℝ)) = 1/(8*(k:ℝ)) := by
  have hK1 : (1:ℝ) ≤ (k:ℝ) := by exact_mod_cast hk
  have hK0 : (0:ℝ) < (k:ℝ) := lt_of_lt_of_le zero_lt_one hK1
  have h8d : (0:ℝ) < 8*(k:ℝ) := by nlinarith
  have h8 : ((2:ℝ)^((3:ℕ):ℝ)) = ((8:ℝ):ℝ) := by norm_num [Real.rpow_natCast]
  have e2 : ((2:ℝ)^(1/2:ℝ))*((8:ℝ):ℝ) = ((2:ℝ)^(7/2:ℝ)) := by
    have h3 : ((2:ℝ)^(7/2:ℝ)) = ((2:ℝ)^((1/2:ℝ)+((3:ℕ):ℝ))) := by norm_num
    rw [h3, Real.rpow_add two_pos, h8]
  have e1 : ((k:ℝ)^(3/2:ℝ))*((k:ℝ):ℝ) = ((k:ℝ)^(5/2:ℝ)) := by
    have h3 : ((k:ℝ)^(5/2:ℝ)) = ((k:ℝ)^((3/2:ℝ)+(1:ℝ))) := by norm_num
    rw [h3, Real.rpow_add hK0, Real.rpow_one]
  rw [two_pow_term k hk]
  have hd : (0:ℝ) < ((2:ℝ)^(7/2:ℝ))*((k:ℝ)^(5/2:ℝ)) :=
    mul_pos (Real.rpow_pos_of_pos two_pos _) (Real.rpow_pos_of_pos hK0 _)
  rw [div_eq_div_iff (ne_of_gt hd) (ne_of_gt h8d),
    show ((2:ℝ)^(7/2:ℝ)) = ((2:ℝ)^(1/2:ℝ))*((8:ℝ):ℝ) from e2.symm,
    show ((k:ℝ)^(5/2:ℝ)) = ((k:ℝ)^(3/2:ℝ))*((k:ℝ):ℝ) from e1.symm]
  ring

/-- If 0.305 < η < 0.312 and k ≥ 1, exp(k · `correctedGamma η k`) is at most 2^(11/4) k^(5/4)
exp(k(1 + log η / 2)). -/
private lemma exp_gammak_le {η : ℝ} (h1 : 305/1000 < η) (h2 : η < 312/1000) {k : ℕ} (hk : 1 ≤ k) :
    Real.exp (correctedGamma η k * (k:ℝ))
      ≤ ((2:ℝ)^(11/4:ℝ))*((k:ℝ)^(5/4:ℝ))*Real.exp ((k:ℝ)*(1 + Real.log η/2)) := by
  have hK1 : (1:ℝ) ≤ (k:ℝ) := by exact_mod_cast hk
  have hK0 : (0:ℝ) < (k:ℝ) := lt_of_lt_of_le zero_lt_one hK1
  have hkp1 : (0:ℝ) < ((k+1:ℕ):ℝ) := by
    have hn : (0:ℕ) < k+1 := Nat.succ_pos k
    exact_mod_cast hn
  have hkp1cast : ((k+1:ℕ):ℝ) = (k:ℝ) + 1 := by
    push_cast
    ring
  have hpos : (0:ℝ) < ((integerNode η k : ℤ):ℝ) := by
    have := (node_bounds h1 h2 hk).1
    linarith
  have hxe : (2:ℝ) ≤ Real.exp (((k+1:ℕ):ℝ) * gammaReq η k) := by
    have h4k := exp_gammaReq_node_ge h1 h2 hk
    nlinarith
  have hceil : ((integerNode η k : ℤ):ℝ) < Real.exp (((k+1:ℕ):ℝ) * gammaReq η k) + 1 :=
    Int.ceil_lt_add_one _
  have h15 : ((integerNode η k : ℤ):ℝ) ≤ (3:ℝ)/2 * Real.exp (((k+1:ℕ):ℝ) * gammaReq η k) := by
    nlinarith [hxe, hceil]
  have hlogN : Real.log ((integerNode η k : ℤ):ℝ)
      ≤ Real.log ((3:ℝ)/2) + ((k+1:ℕ):ℝ) * gammaReq η k := by
    refine le_trans (Real.log_le_log hpos h15) ?_
    rw [Real.log_mul (by norm_num : ((3:ℝ)/2) ≠ 0) (Real.exp_ne_zero _), Real.log_exp]
  have hsplit0 : correctedGamma η k * ((k:ℝ) + 1) = Real.log ((integerNode η k : ℤ):ℝ) := by
    rw [correctedGamma, ← hkp1cast, div_mul_cancel₀ _ (ne_of_gt hkp1)]
  have hgk : correctedGamma η k * (k:ℝ)
      ≤ gammaReq η k * (k:ℝ) + Real.log ((3:ℝ)/2) := by
    have hgR : gammaReq η k ≤ correctedGamma η k := gamma_ge_gammaReq h1 h2 hk
    have e1 : correctedGamma η k * (k:ℝ)
        = correctedGamma η k * ((k:ℝ) + 1) - correctedGamma η k := by ring
    have e2 : gammaReq η k * ((k:ℝ) + 1) = gammaReq η k * (k:ℝ) + gammaReq η k := by ring
    rw [hkp1cast] at hlogN
    rw [e1, hsplit0]
    linarith [hgR, hlogN, e2]
  have hmono : Real.exp (correctedGamma η k * (k:ℝ))
      ≤ Real.exp (gammaReq η k * (k:ℝ) + Real.log ((3:ℝ)/2)) :=
    Real.exp_le_exp.mpr hgk
  rw [Real.exp_add, Real.exp_log (by norm_num : (0:ℝ) < 3/2)] at hmono
  have hsplitk : gammaReq η k * (k:ℝ)
      = (k:ℝ)*(1 + Real.log η/2) + ((1:ℝ)/2)
        * Real.log (2 * ((2*(k:ℝ)):ℝ)^(5/2:ℝ)) := by
    unfold gammaReq
    field_simp
  rw [hsplitk, Real.exp_add, exp_half_log k hk, rpow_two_k k hk] at hmono
  have hconv : ((2:ℝ)^(11/4:ℝ)) = (2:ℝ)*((2:ℝ)^(7/4:ℝ)) := by
    have h3 : ((2:ℝ)^(11/4:ℝ)) = ((2:ℝ)^((1:ℝ)+(7/4:ℝ))) := by norm_num
    rw [h3, Real.rpow_add two_pos, Real.rpow_one]
  have hAE : (0:ℝ) ≤ Real.exp ((k:ℝ)*(1 + Real.log η/2))
      *(((2:ℝ)^(7/4:ℝ))*((k:ℝ)^(5/4:ℝ))) := by
    exact mul_nonneg (Real.exp_pos _).le
      (mul_nonneg (Real.rpow_nonneg (by norm_num) _) (Real.rpow_nonneg hK0.le _))
  calc Real.exp (correctedGamma η k * (k:ℝ))
      ≤ Real.exp ((k:ℝ)*(1 + Real.log η/2))
        *(((2:ℝ)^(7/4:ℝ))*((k:ℝ)^(5/4:ℝ)))*((3:ℝ)/2) := hmono
    _ ≤ Real.exp ((k:ℝ)*(1 + Real.log η/2))
        *(((2:ℝ)^(7/4:ℝ))*((k:ℝ)^(5/4:ℝ)))*((2:ℝ)) :=
          mul_le_mul_of_nonneg_left (by norm_num) hAE
    _ = ((2:ℝ)^(11/4:ℝ))*((k:ℝ)^(5/4:ℝ))*Real.exp ((k:ℝ)*(1 + Real.log η/2)) := by
          rw [hconv]
          ring

/-- For k ≥ 1, exp(2k · `gammaReq η k`) factors as exp(2k(1 + log η / 2)) times 2 (2k)^(5/2). -/
private lemma exp_2k_gammaReq (η : ℝ) {k : ℕ} (hk : 1 ≤ k) :
    Real.exp (2*(k:ℝ) * gammaReq η k)
      = Real.exp (2*(k:ℝ)*(1 + Real.log η/2)) * (2*((2*(k:ℝ)):ℝ)^(5/2:ℝ)) := by
  have hK0 : (0:ℝ) < (k:ℝ) := by
    have : (1:ℝ) ≤ (k:ℝ) := by exact_mod_cast hk
    linarith
  have hsplit : 2*(k:ℝ) * gammaReq η k
      = 2*(k:ℝ)*(1 + Real.log η/2)
        + Real.log (2 * ((2*(k:ℝ)):ℝ)^(5/2:ℝ)) := by
    unfold gammaReq
    field_simp
  have hpos : (0:ℝ) < 2 * ((2*(k:ℝ)):ℝ)^(5/2:ℝ) :=
    mul_pos (by norm_num) (Real.rpow_pos_of_pos (by nlinarith) _)
  rw [hsplit, Real.exp_add, Real.exp_log hpos]

/-- If 0.305 < η < 0.312 and k ≥ 1, the rounded node is at most (3 / 2) 2^(7/4) k^(5/4) exp(k(1
+ log η / 2)) exp 2. -/
private lemma node_le_exp_bound {η : ℝ} (h1 : 305/1000 < η) (h2 : η < 312/1000) {k : ℕ}
    (hk : 1 ≤ k) : ((integerNode η k : ℤ):ℝ)
      ≤ (3:ℝ)/2 * (((2:ℝ)^(7/4:ℝ))*((k:ℝ)^(5/4:ℝ))
        * Real.exp ((k:ℝ)*(1 + Real.log η/2)) * Real.exp 2) := by
  have hK1 : (1:ℝ) ≤ (k:ℝ) := by exact_mod_cast hk
  have hK0 : (0:ℝ) < (k:ℝ) := lt_of_lt_of_le zero_lt_one hK1
  have hxe : (2:ℝ) ≤ Real.exp (((k+1:ℕ):ℝ) * gammaReq η k) := by
    have h4k := exp_gammaReq_node_ge h1 h2 hk
    nlinarith
  have hceil : ((integerNode η k : ℤ):ℝ) < Real.exp (((k+1:ℕ):ℝ) * gammaReq η k) + 1 :=
    Int.ceil_lt_add_one _
  have h15 : ((integerNode η k : ℤ):ℝ) ≤ (3:ℝ)/2 * Real.exp (((k+1:ℕ):ℝ) * gammaReq η k) := by
    nlinarith [hxe, hceil]
  have hgR : gammaReq η k ≤ correctedGamma η k := gamma_ge_gammaReq h1 h2 hk
  have hg2 : correctedGamma η k ≤ 2 := gamma_le_two h1 h2 hk
  have hgRle : Real.exp (gammaReq η k) ≤ Real.exp 2 := Real.exp_le_exp.mpr (le_trans hgR hg2)
  have hsplitk : (k:ℝ)*gammaReq η k
      = (k:ℝ)*(1 + Real.log η/2) + ((1:ℝ)/2)
        * Real.log (2 * ((2*(k:ℝ)):ℝ)^(5/2:ℝ)) := by
    unfold gammaReq
    field_simp
  have hsum : ((k+1:ℕ):ℝ)*gammaReq η k = (k:ℝ)*gammaReq η k + gammaReq η k := by
    push_cast
    ring
  have hprod : Real.exp ((k:ℝ)*gammaReq η k) * Real.exp (gammaReq η k)
      = Real.exp ((k:ℝ)*(1 + Real.log η/2))
        * (((2:ℝ)^(7/4:ℝ))*((k:ℝ)^(5/4:ℝ))) * Real.exp (gammaReq η k) := by
    rw [hsplitk, Real.exp_add, exp_half_log k hk, rpow_two_k k hk]
  calc ((integerNode η k : ℤ):ℝ)
      ≤ (3:ℝ)/2 * Real.exp (((k+1:ℕ):ℝ) * gammaReq η k) := h15
    _ = (3:ℝ)/2 * (Real.exp ((k:ℝ)*gammaReq η k) * Real.exp (gammaReq η k)) := by
          rw [hsum, Real.exp_add]

    _ = (3:ℝ)/2 * (Real.exp ((k:ℝ)*(1 + Real.log η/2))
        * (((2:ℝ)^(7/4:ℝ))*((k:ℝ)^(5/4:ℝ))) * Real.exp (gammaReq η k)) := by
          rw [hprod]
    _ ≤ (3:ℝ)/2 * (Real.exp ((k:ℝ)*(1 + Real.log η/2))
        * (((2:ℝ)^(7/4:ℝ))*((k:ℝ)^(5/4:ℝ))) * Real.exp 2) := by
          have h32 : (0:ℝ) ≤ 3/2 := by norm_num
          have hX : (0:ℝ) ≤ Real.exp ((k:ℝ)*(1 + Real.log η/2))
              * (((2:ℝ)^(7/4:ℝ))*((k:ℝ)^(5/4:ℝ))) :=
            mul_nonneg (Real.exp_pos _).le
              (mul_nonneg (Real.rpow_nonneg (by norm_num) _) (Real.rpow_nonneg hK0.le _))
          exact mul_le_mul_of_nonneg_left
            (mul_le_mul (le_refl _) hgRle (Real.exp_pos _).le hX) h32
    _ = (3:ℝ)/2 * (((2:ℝ)^(7/4:ℝ))*((k:ℝ)^(5/4:ℝ))
        * Real.exp ((k:ℝ)*(1 + Real.log η/2)) * Real.exp 2) := by ring

/-- For k ≥ 1, splits the sum over the integer interval from 1 to k + 1 into its last term and
the sum from 1 to k. -/
private lemma Icc_split {k : ℕ} (hk : 1 ≤ k) (C : ℕ → ℝ) :
    ∑ q ∈ Finset.Icc 1 (k+1), C q = C (k+1) + ∑ q ∈ Finset.Icc 1 k, C q := by
  have hset : Finset.Icc 1 (k+1) = insert (k+1) (Finset.Icc 1 k) := by
    rw [← Finset.Ico_insert_right (by omega : (1:ℕ) ≤ k)]
    ext q
    simp only [Finset.mem_Icc, Finset.mem_Ico, Finset.mem_insert]
    omega
  rw [hset, Finset.sum_insert (by simp [Finset.mem_Icc])]

/-- Under normalization and the stated coefficient bounds, with 0.305 < η < 0.312 and k ≥ 1, the
first k absolute coefficients sum to at most 1 / 8, every coefficient has magnitude at most
2, and eight times the negative mass is at most the positive mass. -/
private lemma coeff_consequences {η : ℝ} (h1 : 305/1000 < η) (h2 : η < 312/1000) {k : ℕ}
    (hk : 1 ≤ k) {C : ℕ → ℝ} (hsum : ∑ q ∈ Finset.Icc 1 (k+1), C q = 1)
    (hbd : ∀ q ∈ Finset.Icc 1 k, |C q| ≤ 2^(1/2:ℝ) * (k:ℝ)^(3/2:ℝ)
      * Real.exp (2*(k:ℝ)*(1 + Real.log η/2 - correctedGamma η k))) :
    (∑ q ∈ Finset.Icc 1 k, |C q| ≤ 1/8)
    ∧ (∀ q ∈ Finset.Icc 1 (k+1), |C q| ≤ 2)
    ∧ (8 * ∑ q ∈ Finset.filter (fun q => C q < 0) (Finset.Icc 1 (k+1)), |C q|
      ≤ ∑ q ∈ Finset.filter (fun q => 0 < C q) (Finset.Icc 1 (k+1)), C q) := by
  have hK1 : (1:ℝ) ≤ (k:ℝ) := by exact_mod_cast hk
  have hK0 : (0:ℝ) < (k:ℝ) := lt_of_lt_of_le zero_lt_one hK1
  have hgR : gammaReq η k ≤ correctedGamma η k := gamma_ge_gammaReq h1 h2 hk
  have hcal : Real.exp (2*(k:ℝ)*(1 + Real.log η/2 - correctedGamma η k))
      ≤ 1 / (2*((2*(k:ℝ)):ℝ)^(5/2:ℝ)) := by
    have h2k : 2*(k:ℝ) * gammaReq η k = 2*(k:ℝ)*(1 + Real.log η/2)
        + Real.log (2 * ((2*(k:ℝ)):ℝ)^(5/2:ℝ)) := by
      unfold gammaReq
      field_simp
    have hmono : 2*(k:ℝ)*(1 + Real.log η/2 - correctedGamma η k)
        ≤ -Real.log (2 * ((2*(k:ℝ)):ℝ)^(5/2:ℝ)) := by
      have hge : 2*(k:ℝ)*gammaReq η k ≤ 2*(k:ℝ)*correctedGamma η k :=
        mul_le_mul_of_nonneg_left hgR (mul_nonneg (by norm_num : (0:ℝ) ≤ 2) hK0.le)
      rw [mul_sub]
      linarith
    calc Real.exp (2*(k:ℝ)*(1 + Real.log η/2 - correctedGamma η k))
        ≤ Real.exp (-Real.log (2 * ((2*(k:ℝ)):ℝ)^(5/2:ℝ))) := Real.exp_le_exp.mpr hmono
      _ = 1 / (2*((2*(k:ℝ)):ℝ)^(5/2:ℝ)) := by
          rw [Real.exp_neg, inv_eq_one_div, Real.exp_log (by positivity)]
  have hper : ∀ q ∈ Finset.Icc 1 k, |C q| ≤ 1/(8*(k:ℝ)) := by
    intro q hq
    have hb := hbd q hq
    have hnn : (0:ℝ) ≤ 2^(1/2:ℝ) * (k:ℝ)^(3/2:ℝ) :=
      mul_nonneg (Real.rpow_nonneg (by norm_num) _) (Real.rpow_nonneg hK0.le _)
    have hcal' : Real.exp (2*(k:ℝ)*(1 + Real.log η/2 - correctedGamma η k))
        ≤ ((2*((2*(k:ℝ)):ℝ)^(5/2:ℝ)))⁻¹ := by
      rw [one_div] at hcal
      exact hcal
    have hstep3 : 2^(1/2:ℝ) * (k:ℝ)^(3/2:ℝ)
        * Real.exp (2*(k:ℝ)*(1 + Real.log η/2 - correctedGamma η k))
        ≤ 2^(1/2:ℝ) * (k:ℝ)^(3/2:ℝ) * ((2*((2*(k:ℝ)):ℝ)^(5/2:ℝ)))⁻¹ :=
      mul_le_mul_of_nonneg_left hcal' hnn
    rw [inv_eq_one_div, mul_one_div, coeff_bound_identity k hk] at hstep3
    exact le_trans hb hstep3
  have hsum8 : ∑ q ∈ Finset.Icc 1 k, |C q| ≤ 1/8 := by
    have hle : ∑ q ∈ Finset.Icc 1 k, |C q| ≤ ∑ _q ∈ Finset.Icc 1 k, 1/(8*(k:ℝ)) :=
      Finset.sum_le_sum hper
    have hc : (Finset.Icc 1 k).card = k := by simp
    refine le_trans hle ?_
    rw [Finset.sum_const, hc]
    rw [show ((k:ℕ) • ((1:ℝ)/(8*(k:ℝ)))) = (k:ℝ)*((1:ℝ)/(8*(k:ℝ))) from by simp,
      mul_one_div,
      div_le_div_iff₀ (by nlinarith : (0:ℝ) < 8*(k:ℝ)) (by norm_num : (0:ℝ) < 8)]
    linarith
  have hClast : C (k+1) = 1 - ∑ q ∈ Finset.Icc 1 k, C q := by
    rw [← hsum, Icc_split hk C]
    ring
  have habs := Finset.abs_sum_le_sum_abs C (Finset.Icc 1 k)
  have hsumCdown : -(1:ℝ)/8 ≤ ∑ q ∈ Finset.Icc 1 k, C q := by
    have := (abs_le.mp habs).1
    linarith [this, hsum8]
  have hsumCup : ∑ q ∈ Finset.Icc 1 k, C q ≤ 1/8 := by
    have := (abs_le.mp habs).2
    linarith [this, hsum8]
  have hCpos : (7:ℝ)/8 ≤ C (k+1) := by
    rw [hClast]
    linarith
  have hCle : C (k+1) ≤ 9/8 := by
    rw [hClast]
    linarith

  have hfeq : (Finset.Icc 1 (k+1)).filter (fun q => C q < 0)
      = (Finset.Icc 1 k).filter (fun q => C q < 0) := by
    ext q
    simp only [Finset.mem_filter, Finset.mem_Icc]
    constructor
    · rintro ⟨⟨hq1, hq2⟩, hqneg⟩
      refine ⟨⟨hq1, ?_⟩, hqneg⟩
      by_contra hcon
      push Not at hcon
      have hlast : C (k+1) < 0 := by rw [show (k+1:ℕ) = q by omega]; exact hqneg
      linarith
    · rintro ⟨hq1, hq2⟩
      exact ⟨by omega, hq2⟩
  have hSneg8 : ∑ q ∈ (Finset.Icc 1 (k+1)).filter (fun q => C q < 0), |C q| ≤ 1/8 := by
    rw [hfeq, Finset.sum_filter]
    have hmono : ∑ q ∈ Finset.Icc 1 k, (if C q < 0 then |C q| else 0)
        ≤ ∑ q ∈ Finset.Icc 1 k, |C q| :=
      Finset.sum_le_sum (fun q _ => by
        by_cases hq : C q < 0
        · rw [if_pos hq]
        · rw [if_neg hq]
          exact abs_nonneg _)
    exact le_trans hmono hsum8
  have hpart1 := Finset.sum_filter_add_sum_filter_not (Finset.Icc 1 (k+1))
    (fun q => 0 < C q) C
  rw [hsum] at hpart1

  have hstep : ∑ q ∈ (Finset.Icc 1 (k+1)).filter (fun q => ¬(0 < C q)), |C q|
      = ∑ q ∈ (Finset.Icc 1 (k+1)).filter (fun q => C q < 0), |C q| := by
    rw [Finset.sum_filter, Finset.sum_filter]
    refine Finset.sum_congr rfl ?_
    intro q _
    rcases lt_trichotomy (C q) 0 with hq | hq | hq
    · rw [if_pos (not_lt.mpr (le_of_lt hq)), if_pos hq]
    · simp [hq]
    · rw [if_neg (fun h => h hq), if_neg (fun h => absurd hq (not_lt.mpr (le_of_lt h)))]
  have hneg : ∑ q ∈ (Finset.Icc 1 (k+1)).filter (fun q => ¬(0 < C q)), C q
      = -∑ q ∈ (Finset.Icc 1 (k+1)).filter (fun q => C q < 0), |C q| := by
    have h1' : ∀ q ∈ (Finset.Icc 1 (k+1)).filter (fun q => ¬(0 < C q)),
        C q = -|C q| := by
      intro q hq
      have h0 : C q ≤ 0 := by
        have := (Finset.mem_filter.mp hq).2
        by_contra hpos
        push Not at hpos
        exact absurd hpos this
      rw [abs_of_nonpos h0]
      ring
    rw [Finset.sum_congr rfl h1', Finset.sum_neg_distrib, hstep]
  refine ⟨hsum8, ?_, ?_⟩
  · intro q hq
    by_cases hqk : q ∈ Finset.Icc 1 k
    · exact le_trans (hper q hqk) (by field_simp; linarith)
    · have hqk1 : q = k+1 := by
        simp only [Finset.mem_Icc] at hq hqk
        push Not at hqk
        omega
      rw [hqk1, abs_of_nonneg (by linarith : (0:ℝ) ≤ C (k+1))]
      linarith
  · linarith [hpart1, hneg]

/-- For k ≥ 1, m ≥ 1, positive h, t, ε, and 0 < β < 1, `retryCount` is at least 1 and dominates
both the accuracy-dependent bound and 13 log(2 / β). -/
private lemma retry_bounds {m h t ε β : ℝ} (hm : 1 ≤ m) (hh : 0 < h) (ht : 0 < t)
    (hε : 0 < ε) (hβ : 0 < β) (hβ1 : β < 1) {k : ℕ} (hk : 1 ≤ k) :
    1 ≤ retryCount m h t ε β k
    ∧ ((4*m*((5:ℝ)/3)^(k-1)*h*t)^(1 + 1/((4:ℝ)*(k:ℝ)))
        / ((errorBudget m h t ε β k/5)^(1/((4:ℝ)*(k:ℝ)))))
      ≤ ((retryCount m h t ε β k : ℤ):ℝ)
    ∧ 13*Real.log (2/β) ≤ ((retryCount m h t ε β k : ℤ):ℝ) := by
  have hceil := Int.le_ceil
    (max ((4*m*((5:ℝ)/3)^(k-1)*h*t)^(1 + 1/((4:ℝ)*(k:ℝ)))
      / ((errorBudget m h t ε β k/5)^(1/((4:ℝ)*(k:ℝ))))) (13*Real.log (2/β)))
  have hv : 13*Real.log (2/β) ≤ ((retryCount m h t ε β k : ℤ):ℝ) :=
    le_trans (le_max_right _ _) hceil
  refine ⟨?_, le_trans (le_max_left _ _) hceil, hv⟩
  have hlogpos : 0 < Real.log (2/β) := by
    refine Real.log_pos ?_
    rw [one_lt_div₀ hβ]
    exact hβ1.trans (by norm_num : (1:ℝ) < 2)
  have : (0:ℝ) < ((retryCount m h t ε β k : ℤ):ℝ) := by
    refine lt_of_lt_of_le ?_ hv
    positivity
  exact_mod_cast this

/-- For 0.305 < η < 0.312, k ≥ 1, m ≥ 1, and integer r ≥ 1, bounds 10m · 5^(k − 1) · k ·
`integerNode η k` · r by 1000m · 5^(k − 1) · k^(9/4) · exp((1 + log η / 2)k) · r. -/
private lemma cost_67 {η : ℝ} (h1 : 305/1000 < η) (h2 : η < 312/1000) {k : ℕ} (hk : 1 ≤ k)
    {m : ℝ} (hm : 1 ≤ m) {r : ℤ} (hr : 1 ≤ r) :
    10 * m * ((5:ℝ)^(k-1)) * (k:ℝ) * ((integerNode η k : ℤ):ℝ) * ((r:ℤ):ℝ)
      ≤ 1000 * m * ((5:ℝ)^(k-1)) * ((k:ℝ)^(9/4:ℝ))
        * Real.exp ((1 + Real.log η/2) * (k:ℝ)) * ((r:ℤ):ℝ) := by
  have hK1 : (1:ℝ) ≤ (k:ℝ) := by exact_mod_cast hk
  have hK0 : (0:ℝ) < (k:ℝ) := lt_of_lt_of_le zero_lt_one hK1
  have h274 : ((2:ℝ)^(7/4:ℝ)) ≤ 4 := by
    have hmono := Real.rpow_le_rpow_left_iff (by norm_num : (1:ℝ) < 2) |>.mpr
      (by norm_num : ((7:ℝ)/4) ≤ (2:ℝ))
    rw [Real.rpow_two] at hmono
    norm_num at hmono
    exact hmono
  have he2 : Real.exp 2 ≤ 9 := by
    have he : Real.exp 1 * Real.exp 1 = Real.exp 2 := by
      rw [← Real.exp_add]
      norm_num
    have h3 : Real.exp 1 ≤ 3 := exp_one_le.trans (by norm_num : (1699:ℝ)/625 ≤ 3)
    have hprod := mul_le_mul h3 h3 (Real.exp_pos 1).le (by norm_num : (0:ℝ) ≤ 3)
    rw [← he]
    linarith [hprod]
  have hN := node_le_exp_bound h1 h2 hk
  have hk94 : ((k:ℝ)^(9/4:ℝ)) = ((k:ℝ):ℝ) * ((k:ℝ)^(5/4:ℝ)) := by
    rw [show ((9:ℝ)/4) = 1 + 5/4 by norm_num, Real.rpow_add hK0, Real.rpow_one]
  have hconst : (15:ℝ) * ((2:ℝ)^(7/4:ℝ)) * (Real.exp 2) ≤ 540 := by
    have hX : (0:ℝ) ≤ ((2:ℝ)^(7/4:ℝ)) := Real.rpow_nonneg (by norm_num) _
    have hY : (0:ℝ) ≤ Real.exp 2 := (Real.exp_pos 2).le
    have hstep := mul_le_mul h274 he2 hY (by norm_num : (0:ℝ) ≤ 4)
    norm_num at hstep
    nlinarith [hstep]
  have hEform : Real.exp ((k:ℝ)*(1 + Real.log η/2))
      = Real.exp ((1 + Real.log η/2) * (k:ℝ)) := by rw [mul_comm]
  have hK54 : (0:ℝ) ≤ ((k:ℝ)^(5/4:ℝ)) := Real.rpow_nonneg hK0.le _
  have key : 10*(k:ℝ)*((integerNode η k : ℤ):ℝ)
      ≤ 1000*((k:ℝ)^(9/4:ℝ))*Real.exp ((1 + Real.log η/2) * (k:ℝ)) := by
    calc 10*(k:ℝ)*((integerNode η k : ℤ):ℝ)
        ≤ 10*(k:ℝ)*((3:ℝ)/2 * (((2:ℝ)^(7/4:ℝ))*((k:ℝ)^(5/4:ℝ))
          * Real.exp ((k:ℝ)*(1 + Real.log η/2)) * Real.exp 2)) :=
          mul_le_mul_of_nonneg_left hN (mul_nonneg (by norm_num : (0:ℝ) ≤ 10) hK0.le)
      _ = ((15:ℝ)*((2:ℝ)^(7/4:ℝ))*(Real.exp 2))*(((k:ℝ)^(9/4:ℝ))
          * Real.exp ((k:ℝ)*(1 + Real.log η/2))) := by
          rw [hk94]
          ring
      _ ≤ 540*(((k:ℝ)^(9/4:ℝ))*Real.exp ((k:ℝ)*(1 + Real.log η/2))) := by
          refine mul_le_mul_of_nonneg_right hconst ?_
          exact mul_nonneg (Real.rpow_nonneg hK0.le _) (Real.exp_pos _).le
      _ ≤ 1000*((k:ℝ)^(9/4:ℝ))*Real.exp ((1 + Real.log η/2) * (k:ℝ)) := by
          have hX : (0:ℝ) ≤ ((k:ℝ)^(9/4:ℝ))*Real.exp ((k:ℝ)*(1 + Real.log η/2)) :=
            mul_nonneg (Real.rpow_nonneg hK0.le _) (Real.exp_pos _).le
          have hX2 : ((k:ℝ)^(9/4:ℝ))*Real.exp ((k:ℝ)*(1 + Real.log η/2))
              = ((k:ℝ)^(9/4:ℝ))*Real.exp ((1 + Real.log η/2) * (k:ℝ)) := by
            rw [hEform]
          rw [hX2] at hX ⊢
          linarith [hX]
  have hF : (0:ℝ) ≤ m*((5:ℝ)^(k-1))*((r:ℤ):ℝ) := by
    refine mul_nonneg (mul_nonneg ?_ ?_) ?_
    · exact_mod_cast (show (0:ℝ) ≤ m by linarith)
    · exact pow_nonneg (by norm_num) _
    · exact_mod_cast (show (0:ℤ) ≤ r by omega)
  have hstep := mul_le_mul_of_nonneg_right key hF
  calc 10 * m * ((5:ℝ)^(k-1)) * (k:ℝ) * ((integerNode η k : ℤ):ℝ) * ((r:ℤ):ℝ)
      = (10*(k:ℝ)*((integerNode η k : ℤ):ℝ))*(m*((5:ℝ)^(k-1))*((r:ℤ):ℝ)) := by ring
    _ ≤ (1000*((k:ℝ)^(9/4:ℝ))*Real.exp ((1 + Real.log η/2) * (k:ℝ)))
        *(m*((5:ℝ)^(k-1))*((r:ℤ):ℝ)) := hstep
    _ = 1000 * m * ((5:ℝ)^(k-1)) * ((k:ℝ)^(9/4:ℝ))
        * Real.exp ((1 + Real.log η/2) * (k:ℝ)) * ((r:ℤ):ℝ) := by ring

/-- Establishes the rounded-node parameter, coefficient, repetition, and cost bounds in
`Lemma12IntegerNodesCorrected`, supporting the analysis of Lemma 12 in [ChildsWiebe2012]. -/
theorem lemma12IntegerNodesCorrected : Lemma12IntegerNodesCorrected := by
  intro η hηlo hηhi k hk m h t ε β hm hh ht hε hβ0 hβ1 C hCsum hCbd
  obtain ⟨hN2, hkN, hN2k2⟩ := node_bounds hηlo hηhi hk
  obtain ⟨hsum8, hle2, hkappa⟩ := coeff_consequences hηlo hηhi hk hCsum hCbd
  obtain ⟨hr1, hrw, hrv⟩ := retry_bounds hm hh ht hε hβ0 hβ1 hk
  refine ⟨?_, hkN, exp_log_node hηlo hηhi hk, gamma_ge_gammaReq hηlo hηhi hk,
    gamma_le_two hηlo hηhi hk, exp_gammak_le hηlo hηhi hk, hN2k2, hsum8, hle2, hkappa,
    ⟨hr1, hrw, hrv, cost_67 hηlo hηhi hk hm hr1⟩⟩
  exact_mod_cast (show ((1:ℝ)) ≤ ((integerNode η k : ℤ):ℝ) by linarith)

/-- The exponential at 22 / 25 is at most 603 / 250. -/
private lemma exp_22_25_le : Real.exp (22/25) ≤ (603:ℝ)/250 := by
  have h := Real.exp_bound' (by norm_num : (0:ℝ) ≤ 22/25) (by norm_num) (n := 6) (by norm_num)
  norm_num [Finset.sum_range_succ, Nat.factorial] at h
  linarith

/-- The exponential at 43 / 250 is at most 11877 / 10000. -/
private lemma exp_43_250_le : Real.exp (43/250) ≤ (11877:ℝ)/10000 := by
  have h := Real.exp_bound' (by norm_num : (0:ℝ) ≤ 43/250) (by norm_num) (n := 5) (by norm_num)
  norm_num [Finset.sum_range_succ, Nat.factorial] at h
  linarith

/-- The exponential at 12 / 5 is at least 10. -/
private lemma exp_12_5_ge : (10:ℝ) ≤ Real.exp (12/5) := by
  have h := exp_ge_partial (12/5) (by norm_num) 6
  norm_num [Finset.sum_range_succ, Nat.factorial] at h
  linarith

/-- The natural logarithm of 6 is at most 91 / 50. -/
private lemma log_6_le : Real.log 6 ≤ (91:ℝ)/50 := by
  rw [Real.log_le_iff_le_exp (by norm_num : (0:ℝ) < 6)]
  have h := exp_ge_partial (91/50) (by norm_num) 6
  norm_num [Finset.sum_range_succ, Nat.factorial] at h
  linarith

/-- For k ≥ 1, the factor 2 (2k)^(5/2) is at least 1. -/
private lemma one_le_node_term (k : ℕ) (hk : 1 ≤ k) :
    (1:ℝ) ≤ 2 * ((2*(k:ℝ)):ℝ)^(5/2:ℝ) := by
  have hK1 : (1:ℝ) ≤ (k:ℝ) := by exact_mod_cast hk
  have h1 : (1:ℝ) ≤ ((2*(k:ℝ)):ℝ) := by nlinarith
  have h2 : (1:ℝ) ≤ ((2*(k:ℝ)):ℝ)^(5/2:ℝ) := Real.one_le_rpow h1 (by norm_num)
  nlinarith [h2]

example (η : ℝ) (h1 : 305/1000 < η) (h2 : η < 312/1000) :
    Int.ceil (Real.exp (2 * gammaReq η 2)) = 19
    ∧ ¬ ∃ z : ℤ, (19:ℝ)^(3/2:ℝ) = ((z:ℤ):ℝ) := by
  have h42 : ((2*(2:ℝ)):ℝ)^(5/2:ℝ) = 32 := by norm_num
  have hsplit : 2 * gammaReq η 2 = 2 + Real.log η + (1/2) * Real.log (64:ℝ) := by
    unfold gammaReq
    push_cast
    rw [h42]
    norm_num1
    ring
  have hhalf : Real.exp ((1/2) * Real.log (64:ℝ)) = 8 := by
    rw [mul_comm, Real.exp_mul, Real.exp_log (by norm_num : (0:ℝ) < 64)]
    norm_num
  have hE : Real.exp (2 * gammaReq η 2) = 8 * Real.exp 1 * Real.exp 1 * η := by
    rw [hsplit, Real.exp_add, Real.exp_add, Real.exp_log (by positivity : (0:ℝ) < η), hhalf]
    have he2 : Real.exp 2 = Real.exp 1 * Real.exp 1 := by
      rw [← Real.exp_add]
      norm_num
    rw [he2]
    ring
  have hlow : (18:ℝ) < 8 * Real.exp 1 * Real.exp 1 * η := by
    have hge : (163:ℝ)/60 ≤ Real.exp 1 := exp_one_ge163
    have hposE : (0:ℝ) < Real.exp 1 := Real.exp_pos 1
    have hpp : ((163:ℝ)/60)*((163:ℝ)/60) ≤ Real.exp 1 * Real.exp 1 :=
      mul_le_mul hge hge (by norm_num : (0:ℝ) ≤ 163/60) hposE.le
    have hηpos : (0:ℝ) < η := by linarith
    have hXpos : (0:ℝ) < (163:ℝ)/60*((163:ℝ)/60) := by norm_num
    have hd1 : (0:ℝ) ≤ (Real.exp 1 * Real.exp 1 - (163:ℝ)/60*((163:ℝ)/60))*η := by
      exact mul_nonneg (by nlinarith [hpp]) hηpos.le
    have hd2 : (0:ℝ) < ((163:ℝ)/60*((163:ℝ)/60))*(η - 305/1000) := by
      exact mul_pos hXpos (by nlinarith)
    have hfull : ((163:ℝ)/60)*((163:ℝ)/60)*(305/1000)
        < Real.exp 1 * Real.exp 1 * η := by
      nlinarith [hd1, hd2, hpp]
    have hnum : (18:ℝ)/8 ≤ ((163:ℝ)/60)*((163:ℝ)/60)*(305/1000) := by norm_num
    nlinarith [hfull, hnum]
  have hup : 8 * Real.exp 1 * Real.exp 1 * η ≤ (19:ℝ) := by
    have hle : Real.exp 1 ≤ (1699:ℝ)/625 := exp_one_le
    have hposE : (0:ℝ) < Real.exp 1 := Real.exp_pos 1
    have hposY : (0:ℝ) < (1699:ℝ)/625 := by norm_num
    have hpp : Real.exp 1 * Real.exp 1 ≤ ((1699:ℝ)/625)*((1699:ℝ)/625) :=
      mul_le_mul hle hle hposE.le hposY.le
    have hηpos : (0:ℝ) < η := by linarith
    have hfull := mul_le_mul hpp h2.le hηpos.le
      (mul_nonneg hposY.le hposY.le)
    have hnum : 8*((1699:ℝ)/625)*((1699:ℝ)/625)*(312/1000) ≤ 19 := by norm_num
    nlinarith [hfull, hnum]
  refine ⟨Int.ceil_eq_iff.mpr ⟨by rw [hE]; norm_num1; exact hlow,
    by rw [hE]; exact hup⟩, ?_⟩
  rintro ⟨z, hz⟩
  have hz2 : z * z = 6859 := by
    have e1 : ((z:ℤ):ℝ) * ((z:ℤ):ℝ) = (19:ℝ)^((3:ℝ)/2) * (19:ℝ)^((3:ℝ)/2) := by
      rw [hz]
    have e2 : (19:ℝ)^((3:ℝ)/2) * (19:ℝ)^((3:ℝ)/2) = (6859:ℝ) := by
      rw [← Real.rpow_add (by norm_num : (0:ℝ) < 19)]
      norm_num
    have hcast : ((z:ℤ):ℝ) * ((z:ℤ):ℝ) = ((((z:ℤ)*(z:ℤ)):ℤ):ℝ) := by
      rw [Int.cast_mul]
    have hfinal : ((((z:ℤ)*(z:ℤ)):ℤ):ℝ) = (6859:ℝ) := by rw [← hcast, e1, e2]
    exact_mod_cast hfinal
  have hb1 : -(83:ℤ) ≤ z := by
    by_contra hcon
    push Not at hcon
    nlinarith [hz2]
  have hb2 : z ≤ 83 := by
    by_contra hcon
    push Not at hcon
    nlinarith [hz2]
  have hnat : z.natAbs * z.natAbs = 6859 := by
    have h1 : (z*z).natAbs = z.natAbs * z.natAbs := Int.natAbs_mul z z
    rw [hz2] at h1
    norm_num at h1
    exact h1.symm
  have hdec : ∀ n ∈ Finset.range 84, n * n ≠ 6859 := by decide
  have hb3 : z.natAbs ≤ 83 := by
    have key := (Int.natAbs_le_iff_mul_self_le (a := z) (b := 83)).mpr (by
      linarith [hz2])
    have h83n : ((83:ℤ)).natAbs = 83 := by norm_num
    rwa [h83n] at key
  exact hdec z.natAbs (Finset.mem_range.mpr (Nat.lt_succ_of_le hb3)) hnat

example (η : ℝ) (h1 : 305/1000 < η) (h2 : η < 312/1000) :
    ((Int.ceil (Real.exp ((gammaReq η 3)^(3:ℝ))) : ℤ):ℝ)^2 ≤ 81
    ∧ (81:ℝ) < 2^(1/2:ℝ) * (3:ℝ)^(5/2:ℝ) * Real.exp (6*(1 + Real.log η/2)) := by
  have hlog := (eta_log_bounds h1 h2).2
  have hhalf : 1 + Real.log η/2 ≤ 21/50 := by linarith

  have hterm : (1/(2*(3:ℝ))) * Real.log (2 * ((2*(3:ℝ)):ℝ)^(5/2:ℝ)) ≤ 7/8 := by
    have hsplit : Real.log (2 * ((2*(3:ℝ)):ℝ)^(5/2:ℝ))
        = Real.log 2 + (5/2) * Real.log 6 := by
      rw [Real.log_mul (by norm_num : ((2:ℝ)) ≠ 0) (by positivity),
        Real.log_rpow (by norm_num : (0:ℝ) < 2*(3:ℝ))]
      norm_num
    rw [hsplit]
    have h1' : Real.log 2 ≤ 7/10 := log_two_le
    have h2' : Real.log 6 ≤ 91/50 := log_6_le
    norm_num
    linarith
  have hB : gammaReq η 3 ≤ 259/200 := by
    unfold gammaReq
    push_cast
    norm_num
    linarith
  have hBnn : (0:ℝ) ≤ gammaReq η 3 := by
    have hbase := one_add_half_ge h1 h2
    unfold gammaReq
    push_cast
    have hlognn : (0:ℝ) ≤ Real.log (2 * ((2*(3:ℝ)):ℝ)^(5/2:ℝ)) :=
      Real.log_nonneg (one_le_node_term 3 (by norm_num))
    nlinarith [hlognn, mul_nonneg (by norm_num : (0:ℝ) ≤ 1/(2*(3:ℝ))) hlognn]
  have hB3 : (gammaReq η 3)^(3:ℝ) ≤ 2 + 43/250 := by
    refine le_trans (Real.rpow_le_rpow hBnn hB (by norm_num : (0:ℝ) ≤ 3)) ?_
    norm_num
  have hexp : Real.exp ((gammaReq η 3)^(3:ℝ)) ≤ 9 := by
    have he2 : Real.exp 2 = Real.exp 1 * Real.exp 1 := by
      rw [← Real.exp_add]
      norm_num
    calc Real.exp ((gammaReq η 3)^(3:ℝ))
        ≤ Real.exp (2 + 43/250) := Real.exp_le_exp.mpr hB3
      _ = Real.exp 2 * Real.exp (43/250) := by rw [← Real.exp_add]
      _ ≤ ((1699:ℝ)/625)*((1699:ℝ)/625)*(11877/10000) := by
          refine mul_le_mul ?_ exp_43_250_le (Real.exp_pos _).le ?_
          · rw [he2]
            exact mul_le_mul exp_one_le exp_one_le (Real.exp_pos 1).le
              (by norm_num : (0:ℝ) ≤ 1699/625)
          · exact mul_nonneg (by norm_num : (0:ℝ) ≤ 1699/625) (by norm_num : (0:ℝ) ≤ 1699/625)
      _ ≤ 9 := by norm_num
  constructor
  · have hceil9 : (Int.ceil (Real.exp ((gammaReq η 3)^(3:ℝ))) : ℤ) ≤ 9 :=
      Int.ceil_le.mpr (by exact_mod_cast hexp)
    have hpos : (0:ℝ) ≤ ((Int.ceil (Real.exp ((gammaReq η 3)^(3:ℝ))) : ℤ):ℝ) := by
      have h0 : (0:ℝ) ≤ Real.exp ((gammaReq η 3)^(3:ℝ)) := (Real.exp_pos _).le
      exact_mod_cast le_trans h0 (Int.le_ceil _)
    have hcast : ((Int.ceil (Real.exp ((gammaReq η 3)^(3:ℝ))) : ℤ):ℝ) ≤ 9 := by
      exact_mod_cast hceil9
    nlinarith [hpos, hcast]
  · have hbase : (2:ℝ)/5 ≤ 1 + Real.log η/2 := one_add_half_ge h1 h2
    have he : (10:ℝ) ≤ Real.exp (6*(1 + Real.log η/2)) := by
      have hmono : Real.exp (12/5) ≤ Real.exp (6*(1 + Real.log η/2)) :=
        Real.exp_le_exp.mpr (by nlinarith)
      exact le_trans exp_12_5_ge hmono
    have hs2 : ((7:ℝ)/5) ≤ 2^(1/2:ℝ) := by
      have hX : ((2:ℝ)^(1/2:ℝ)) = Real.sqrt 2 := (Real.sqrt_eq_rpow 2).symm
      rw [hX]
      exact (Real.le_sqrt (by norm_num : (0:ℝ) ≤ 7/5) (by norm_num : (0:ℝ) ≤ 2)).mpr
        (by norm_num)
    have hs3 : ((17:ℝ)/10) ≤ 3^(1/2:ℝ) := by
      have hX : ((3:ℝ)^(1/2:ℝ)) = Real.sqrt 3 := (Real.sqrt_eq_rpow 3).symm
      rw [hX]
      exact (Real.le_sqrt (by norm_num : (0:ℝ) ≤ 17/10) (by norm_num : (0:ℝ) ≤ 3)).mpr
        (by norm_num)
    have h352 : (3:ℝ)^(5/2:ℝ) = 3^(1/2:ℝ) * 9 := by
      rw [show ((5:ℝ)/2) = (1/2) + 2 by norm_num, Real.rpow_add (by norm_num : (0:ℝ) < 3)]
      norm_num
    have hA : (1071:ℝ)/50 ≤ 2^(1/2:ℝ) * (3:ℝ)^(5/2:ℝ) := by
      rw [h352]
      have hY : (0:ℝ) ≤ 3^(1/2:ℝ) := Real.rpow_nonneg (by norm_num) _
      calc (1071:ℝ)/50 = (7/5) * ((17/10) * 9) := by norm_num
        _ ≤ (7/5) * (3^(1/2:ℝ) * 9) := by linarith [hs3]
        _ ≤ 2^(1/2:ℝ) * (3^(1/2:ℝ) * 9) := by nlinarith [hs2, hY]
    have hnnE : (0:ℝ) ≤ Real.exp (6*(1 + Real.log η/2)) := (Real.exp_pos _).le
    have hnnA : (0:ℝ) ≤ 2^(1/2:ℝ) * (3:ℝ)^(5/2:ℝ) :=
      mul_nonneg (Real.rpow_nonneg (by norm_num) _) (Real.rpow_nonneg (by norm_num) _)
    have hprod := mul_le_mul hA he (by norm_num : (0:ℝ) ≤ 10) hnnA
    norm_num at hprod
    linarith

example (η : ℝ) (h1 : 305/1000 < η) (h2 : η < 312/1000) :
    2 ≤ Int.ceil (Real.exp ((gammaReq η 4)^(4:ℝ)))
    ∧ (Int.ceil (Real.exp ((gammaReq η 4)^(4:ℝ))) : ℤ) ≤ 15
    ∧ ¬ ∃ z : ℤ, ((Int.ceil (Real.exp ((gammaReq η 4)^(4:ℝ))) : ℤ):ℝ)^(5/4:ℝ)
      = ((z:ℤ):ℝ) := by
  have hlog := (eta_log_bounds h1 h2).2
  have hhalf : 1 + Real.log η/2 ≤ 21/50 := by linarith

  have hterm : (1/(2*(4:ℝ))) * Real.log (2 * ((2*(4:ℝ)):ℝ)^(5/2:ℝ)) ≤ 3/4 := by
    have hsplit : Real.log (2 * ((2*(4:ℝ)):ℝ)^(5/2:ℝ))
        = Real.log 2 + (5/2) * Real.log 8 := by
      rw [Real.log_mul (by norm_num : ((2:ℝ)) ≠ 0) (by positivity),
        Real.log_rpow (by norm_num : (0:ℝ) < 2*(4:ℝ))]
      norm_num
    have h8 : Real.log 8 = 3 * Real.log 2 := by
      rw [show ((8:ℝ)) = ((2:ℝ)^(3:ℕ)) by norm_num, Real.log_pow]
      push_cast
      norm_num
    have h1' : Real.log 2 ≤ 7/10 := log_two_le
    rw [hsplit, h8]
    norm_num
    linarith
  have hB : gammaReq η 4 ≤ 117/100 := by
    unfold gammaReq
    push_cast
    norm_num
    linarith
  have hBpos : (0:ℝ) < gammaReq η 4 := by
    have hbase := one_add_half_ge h1 h2
    unfold gammaReq
    push_cast
    have hlognn : (0:ℝ) ≤ Real.log (2 * ((2*(4:ℝ)):ℝ)^(5/2:ℝ)) :=
      Real.log_nonneg (one_le_node_term 4 (by norm_num))
    nlinarith [hlognn]
  have hB4 : (gammaReq η 4)^(4:ℝ) ≤ 1 + 22/25 := by
    refine le_trans (Real.rpow_le_rpow hBpos.le hB (by norm_num : (0:ℝ) ≤ 4)) ?_
    norm_num
  have hexp : Real.exp ((gammaReq η 4)^(4:ℝ)) ≤ 15 := by
    calc Real.exp ((gammaReq η 4)^(4:ℝ))
        ≤ Real.exp (1 + 22/25) := Real.exp_le_exp.mpr hB4
      _ = Real.exp 1 * Real.exp (22/25) := by rw [← Real.exp_add]
      _ ≤ (1699:ℝ)/625 * (603/250) :=
          mul_le_mul exp_one_le exp_22_25_le (Real.exp_pos _).le
            (by norm_num : (0:ℝ) ≤ 1699/625)
      _ ≤ 15 := by norm_num
  have hlow : (1:ℝ) < Real.exp ((gammaReq η 4)^(4:ℝ)) := by
    have hpos : (0:ℝ) < (gammaReq η 4)^(4:ℝ) := Real.rpow_pos_of_pos hBpos _
    calc (1:ℝ) = Real.exp 0 := by norm_num
      _ < Real.exp ((gammaReq η 4)^(4:ℝ)) := Real.exp_lt_exp.mpr hpos
  have h1' : (1:ℝ) < ((Int.ceil (Real.exp ((gammaReq η 4)^(4:ℝ))) : ℤ):ℝ) := by
    have hle := Int.le_ceil (Real.exp ((gammaReq η 4)^(4:ℝ)))
    linarith
  have hNge2 : (2:ℤ) ≤ Int.ceil (Real.exp ((gammaReq η 4)^(4:ℝ))) := by
    have h2' : (1:ℤ) < Int.ceil (Real.exp ((gammaReq η 4)^(4:ℝ))) := by
      exact_mod_cast h1'
    omega
  have hNle15 : (Int.ceil (Real.exp ((gammaReq η 4)^(4:ℝ))) : ℤ) ≤ 15 :=
    Int.ceil_le.mpr (by exact_mod_cast hexp)
  refine ⟨hNge2, hNle15, ?_⟩
  rintro ⟨z, hz⟩
  have hposN : (0:ℝ) < ((Int.ceil (Real.exp ((gammaReq η 4)^(4:ℝ))) : ℤ):ℝ) := by
    have hle := Int.le_ceil (Real.exp ((gammaReq η 4)^(4:ℝ)))
    linarith
  have p2 : ((Int.ceil (Real.exp ((gammaReq η 4)^(4:ℝ))) : ℤ):ℝ)^((5:ℝ)/4)
      * ((Int.ceil (Real.exp ((gammaReq η 4)^(4:ℝ))) : ℤ):ℝ)^((5:ℝ)/4)
      = ((Int.ceil (Real.exp ((gammaReq η 4)^(4:ℝ))) : ℤ):ℝ)^((5:ℝ)/2) := by
    rw [← Real.rpow_add hposN]
    norm_num
  have p1 : ((Int.ceil (Real.exp ((gammaReq η 4)^(4:ℝ))) : ℤ):ℝ)^((5:ℝ)/2)
      * ((Int.ceil (Real.exp ((gammaReq η 4)^(4:ℝ))) : ℤ):ℝ)^((5:ℝ)/2)
      = ((Int.ceil (Real.exp ((gammaReq η 4)^(4:ℝ))) : ℤ):ℝ)^((5:ℝ)) := by
    rw [← Real.rpow_add hposN]
    norm_num
  have h4' := congrArg (fun x : ℝ => x * x) hz
  try dsimp only at h4'
  rw [p2] at h4'
  have h5' := congrArg (fun x : ℝ => x * x) h4'
  (try dsimp only at h5')
  rw [p1] at h5'
  have ec := Real.rpow_natCast ((Int.ceil (Real.exp ((gammaReq η 4)^(4:ℝ))) : ℤ):ℝ) 5
  rw [show ((5:ℝ)) = (((5:ℕ)):ℝ) from by push_cast; norm_num] at h5'
  rw [ec] at h5'
  rw [← Int.cast_pow, ← Int.cast_mul, ← Int.cast_mul] at h5'
  have hz4 : (z:ℤ)*z*(z*z)
      = (Int.ceil (Real.exp ((gammaReq η 4)^(4:ℝ))))^5 :=
    (Int.cast_injective h5').symm
  have hna : z.natAbs^4
      = (Int.ceil (Real.exp ((gammaReq η 4)^(4:ℝ)))).natAbs^5 := by
    rw [← Int.natAbs_pow, ← Int.natAbs_pow, ← hz4, show z^4 = z*z*(z*z) from by ring]
  have hNnn : (0:ℤ) ≤ Int.ceil (Real.exp ((gammaReq η 4)^(4:ℝ))) := by omega
  have hN15 : (Int.ceil (Real.exp ((gammaReq η 4)^(4:ℝ)))).natAbs ≤ 15 := by
    have key := (Int.natAbs_le_iff_mul_self_le
      (a := (Int.ceil (Real.exp ((gammaReq η 4)^(4:ℝ))) : ℤ)) (b := 15)).mpr (by
        nlinarith [hNnn, hNle15])
    have h15n : ((15:ℤ)).natAbs = 15 := by norm_num
    rwa [h15n] at key
  have hz29 : z.natAbs ≤ 29 := by
    by_contra hcon
    push Not at hcon
    have hpow : (30:ℕ)^4 ≤ z.natAbs^4 := Nat.pow_le_pow_left hcon 4
    have hN5 : (Int.ceil (Real.exp ((gammaReq η 4)^(4:ℝ)))).natAbs^5 ≤ 15^5 :=
      Nat.pow_le_pow_left hN15 5
    rw [hna] at hpow
    norm_num at hpow hN5
    omega
  have hdec : ∀ n ∈ Finset.Icc 2 15, ∀ w ∈ Finset.range 30, w^4 ≠ n^5 := by decide
  have h2n : (2:ℕ) ≤ (Int.ceil (Real.exp ((gammaReq η 4)^(4:ℝ)))).natAbs := by
    have h := hNge2
    omega
  refine hdec _ (Finset.mem_Icc.mpr ⟨h2n, hN15⟩) _
    (Finset.mem_range.mpr (Nat.lt_succ_of_le hz29)) hna

end Qatlib.Papers.HamLCUSim12.Multiproduct
