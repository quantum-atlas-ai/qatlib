/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Analysis.Analytic.Binomial
import Mathlib.Topology.Algebra.InfiniteSum.Real
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith

/-!
# Rational square-root series and truncation bounds

`RationalSqrtSeries` defines positive rational coefficients for the expansion of `1 - sqrt (1 -
x)` and rational truncation polynomials for `sqrt (1 - x)`. On `0 ≤ x ≤ q < 1`, the real
polynomial overestimates the square root by at most `q ^ (L + 1)`, with coefficient summability
and tail bounds supporting the estimate.

For general analytic background on convergence and series methods, see [ReedSimon1980I].

## Main statements

* `sqrtCoeff_eq_choose` and `sqrtCoeff_hasSum`: binomial-series identification.
* `realSqrtPolynomial_error`: one-sided truncation error.
* `realSqrtPolynomial_mem_Icc`: the approximating polynomial lies between zero and one.

## References

* [Reed and Simon, 1980][ReedSimon1980I]
-/

set_option autoImplicit false

open scoped BigOperators

namespace Qatlib.Concepts.FinitePrecision.ComputableInput.RationalSqrtSeries

/-- The rational coefficient sequence starting at one half with recurrence `c[k + 1] = c[k] * (2
* k + 1) / (2 * k + 4)`. -/
def sqrtCoeff : ℕ → ℚ
  | 0 => 1 / 2
  | k + 1 => sqrtCoeff k * (2 * (k : ℚ) + 1) / (2 * (k : ℚ) + 4)

/-- Every rational square-root series coefficient is strictly positive. -/
theorem sqrtCoeff_pos (k : ℕ) : 0 < sqrtCoeff k := by
  induction k with
  | zero => norm_num [sqrtCoeff]
  | succ k ih =>
    rw [sqrtCoeff]
    positivity

/-- The first `L` coefficients sum to `1 - 2 * (L + 1) * sqrtCoeff L`. -/
theorem sqrtCoeff_partial_sum (L : ℕ) :
    (∑ k ∈ Finset.range L, sqrtCoeff k) = 1 - 2 * ((L : ℚ) + 1) * sqrtCoeff L := by
  induction L with
  | zero => norm_num [sqrtCoeff]
  | succ L ih =>
    rw [Finset.sum_range_succ, ih, sqrtCoeff]
    push_cast
    have hd : 2 * (L : ℚ) + 4 ≠ 0 := by positivity
    field_simp [hd]
    ring

/-- Every finite initial sum of the square-root series coefficients is at most one. -/
theorem sqrtCoeff_partial_sum_le (L : ℕ) :
    (∑ k ∈ Finset.range L, sqrtCoeff k) ≤ 1 := by
  rw [sqrtCoeff_partial_sum]
  have hp := sqrtCoeff_pos L
  have hn : (0 : ℚ) ≤ L := Nat.cast_nonneg L
  nlinarith

/-- The real casts of the square-root series coefficients form a summable sequence. -/
theorem sqrtCoeff_summable : Summable (fun k => (sqrtCoeff k : ℝ)) := by
  apply summable_of_sum_range_le (c := 1)
    (fun k => (Rat.cast_pos.mpr (sqrtCoeff_pos k)).le)
  intro L
  exact_mod_cast sqrtCoeff_partial_sum_le L

/-- The infinite sum of the real coefficient sequence is at most one. -/
theorem sqrtCoeff_tsum_le : (∑' k, (sqrtCoeff k : ℝ)) ≤ 1 := by
  apply Real.tsum_le_of_sum_range_le (fun k => (Rat.cast_pos.mpr (sqrtCoeff_pos k)).le)
  intro L
  exact_mod_cast sqrtCoeff_partial_sum_le L

/-- The generalized binomial coefficients satisfy `choose a (k + 1) = choose a k * (a - k) / (k
+ 1)`. -/
private theorem choose_succ (a : ℝ) (k : ℕ) :
    Ring.choose a (k + 1) = Ring.choose a k * (a - k) / (k + 1) := by
  rw [Ring.choose_eq_smul, Ring.choose_eq_smul, descPochhammer_succ_right]
  simp only [Polynomial.smeval_mul, Polynomial.smeval_sub, Polynomial.smeval_X,
    Polynomial.smeval_natCast, smul_eq_mul, Nat.factorial_succ, Nat.cast_mul,
    Nat.cast_add, Nat.cast_one]
  have hk : (k : ℝ) + 1 ≠ 0 := by positivity
  have hf : (k.factorial : ℝ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero k
  field_simp
  ring

/-- The real cast of `sqrtCoeff k` equals the negative of `(-1) ^ (k + 1)` times the generalized
binomial coefficient with upper argument one half. -/
theorem sqrtCoeff_eq_choose (k : ℕ) :
    (sqrtCoeff k : ℝ) = -((-1 : ℝ) ^ (k + 1) * Ring.choose (1 / 2 : ℝ) (k + 1)) := by
  induction k with
  | zero => norm_num [sqrtCoeff]
  | succ k ih =>
    rw [sqrtCoeff]
    push_cast
    rw [ih, choose_succ (1 / 2) (k + 1), pow_succ]
    push_cast
    have hd : 2 * (k : ℝ) + 4 ≠ 0 := by positivity
    have hd' : (k : ℝ) + 1 + 1 ≠ 0 := by positivity
    field_simp [hd, hd']
    ring

/-- The rational polynomial `1 - ∑ k < L, sqrtCoeff k * x ^ (k + 1)` approximating `sqrt (1 -
x)`. -/
def sqrtPolynomial (L : ℕ) (x : ℚ) : ℚ :=
  1 - ∑ k ∈ Finset.range L, sqrtCoeff k * x ^ (k + 1)

/-- For `0 ≤ x < 1`, the weighted coefficient series sums to `1 - Real.sqrt (1 - x)`. -/
theorem sqrtCoeff_hasSum {x : ℝ} (hx : 0 ≤ x) (hx1 : x < 1) :
    HasSum (fun k => (sqrtCoeff k : ℝ) * x ^ (k + 1)) (1 - Real.sqrt (1 - x)) := by
  have hm : (-x : ℝ) ∈ Metric.eball 0 1 := by
    rw [← ENNReal.ofReal_one, Metric.eball_ofReal]
    simpa only [Metric.mem_ball, dist_zero_right, norm_neg, Real.norm_eq_abs,
      abs_of_nonneg hx] using hx1
  have hs := (Real.one_add_rpow_hasFPowerSeriesOnBall_zero (a := (1 / 2 : ℝ))).hasSum_sub hm
  simp only [binomialSeries_apply, sub_zero, List.ofFn_const, List.prod_replicate,
    smul_eq_mul] at hs
  have ht : HasSum (fun k => Ring.choose (1 / 2 : ℝ) (k + 1) * (-x) ^ (k + 1))
      (Real.sqrt (1 - x) - 1) := by
    have h := (hasSum_nat_add_iff' 1).mpr hs
    simpa only [Finset.sum_range_one, Ring.choose_zero_right, pow_zero, mul_one,
      ← sub_eq_add_neg, Real.sqrt_eq_rpow] using h
  have hc (k : ℕ) : (sqrtCoeff k : ℝ) * x ^ (k + 1) =
      -(Ring.choose (1 / 2 : ℝ) (k + 1) * (-x) ^ (k + 1)) := by
    rw [sqrtCoeff_eq_choose, neg_pow]
    ring
  simp_rw [hc]
  simpa only [neg_sub] using ht.neg

/-- The real polynomial obtained by truncating the square-root coefficient expansion after `L`
terms. -/
noncomputable def realSqrtPolynomial (L : ℕ) (x : ℝ) : ℝ :=
  1 - ∑ k ∈ Finset.range L, (sqrtCoeff k : ℝ) * x ^ (k + 1)

/-- Casting the rational square-root polynomial to the reals gives the corresponding real
polynomial at the cast input. -/
theorem sqrtPolynomial_cast (L : ℕ) (x : ℚ) :
    (sqrtPolynomial L x : ℝ) = realSqrtPolynomial L (x : ℝ) := by
  simp [sqrtPolynomial, realSqrtPolynomial]

/-- Every tail of the real coefficient series has sum at most one. -/
theorem sqrtCoeff_tail_le (L : ℕ) : (∑' k, (sqrtCoeff (k + L) : ℝ)) ≤ 1 := by
  have h := sqrtCoeff_summable.sum_add_tsum_nat_add L
  have hp : 0 ≤ ∑ k ∈ Finset.range L, (sqrtCoeff k : ℝ) :=
    Finset.sum_nonneg (fun k _ => (Rat.cast_pos.mpr (sqrtCoeff_pos k)).le)
  linarith [sqrtCoeff_tsum_le]

/-- For `0 ≤ x ≤ q < 1`, the truncation polynomial overestimates `Real.sqrt (1 - x)` with error
at most `q ^ (L + 1)`. -/
theorem realSqrtPolynomial_error (L : ℕ) {x q : ℝ}
    (hx : 0 ≤ x) (hxq : x ≤ q) (hq : q < 1) :
    0 ≤ realSqrtPolynomial L x - Real.sqrt (1 - x) ∧
      realSqrtPolynomial L x - Real.sqrt (1 - x) ≤ q ^ (L + 1) := by
  have hx1 : x < 1 := hxq.trans_lt hq
  have hq0 : 0 ≤ q := hx.trans hxq
  have hs := sqrtCoeff_hasSum hx hx1
  have ht := (hasSum_nat_add_iff' L).mpr hs
  have heq : realSqrtPolynomial L x - Real.sqrt (1 - x) =
      ∑' k, (sqrtCoeff (k + L) : ℝ) * x ^ (k + L + 1) := by
    rw [ht.tsum_eq]
    unfold realSqrtPolynomial
    ring
  have hcs : Summable (fun k => (sqrtCoeff (k + L) : ℝ)) :=
    (summable_nat_add_iff L).mpr sqrtCoeff_summable
  have hp (k : ℕ) : x ^ (k + L + 1) ≤ q ^ (L + 1) := by
    calc
      _ = x ^ k * x ^ (L + 1) := by rw [← pow_add]; congr 1
      _ ≤ 1 * q ^ (L + 1) := mul_le_mul (pow_le_one₀ hx hx1.le)
        (pow_le_pow_left₀ hx hxq _) (pow_nonneg hx _) (by norm_num)
      _ = _ := one_mul _
  rw [heq]
  constructor
  · exact tsum_nonneg (fun k => mul_nonneg
      (Rat.cast_pos.mpr (sqrtCoeff_pos (k + L))).le (pow_nonneg hx _))
  · calc
      _ ≤ ∑' k, (sqrtCoeff (k + L) : ℝ) * q ^ (L + 1) :=
        ht.summable.tsum_le_tsum (fun k => mul_le_mul_of_nonneg_left (hp k)
          (Rat.cast_pos.mpr (sqrtCoeff_pos (k + L))).le) (hcs.mul_right _)
      _ = (∑' k, (sqrtCoeff (k + L) : ℝ)) * q ^ (L + 1) := tsum_mul_right
      _ ≤ 1 * q ^ (L + 1) :=
        mul_le_mul_of_nonneg_right (sqrtCoeff_tail_le L) (pow_nonneg hq0 _)
      _ = _ := one_mul _

/-- For `0 ≤ x < 1`, the real square-root truncation polynomial lies in the closed interval from
zero to one. -/
theorem realSqrtPolynomial_mem_Icc (L : ℕ) {x : ℝ} (hx : 0 ≤ x) (hx1 : x < 1) :
    realSqrtPolynomial L x ∈ Set.Icc (0 : ℝ) 1 := by
  have hlow := (realSqrtPolynomial_error L hx le_rfl hx1).1
  have hsum : 0 ≤ ∑ k ∈ Finset.range L, (sqrtCoeff k : ℝ) * x ^ (k + 1) :=
    Finset.sum_nonneg (fun k _ => mul_nonneg
      (Rat.cast_pos.mpr (sqrtCoeff_pos k)).le (pow_nonneg hx _))
  constructor
  · linarith [Real.sqrt_nonneg (1 - x)]
  · unfold realSqrtPolynomial
    linarith

/-- For `0 ≤ q ≤ 1`, the power `q ^ m` is at most `1 / (1 + m * (1 - q))`. -/
theorem geometric_power_bound (m : ℕ) {q : ℝ} (hq0 : 0 ≤ q) (hq1 : q ≤ 1) :
    q ^ m ≤ 1 / (1 + (m : ℝ) * (1 - q)) := by
  have hprod : ∀ k : ℕ, q ^ k * (1 + (k : ℝ) * (1 - q)) ≤ 1 := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      have hs : q * (1 + ((k : ℝ) + 1) * (1 - q)) ≤
          1 + (k : ℝ) * (1 - q) := by
        nlinarith [mul_nonneg (show (0 : ℝ) ≤ (k : ℝ) + 1 by positivity)
          (sq_nonneg (1 - q))]
      have hm := mul_le_mul_of_nonneg_left hs (pow_nonneg hq0 k)
      simpa only [pow_succ, Nat.cast_add, Nat.cast_one, mul_assoc] using hm.trans ih
  have hd : 0 < 1 + (m : ℝ) * (1 - q) := by
    have hmul := mul_nonneg (Nat.cast_nonneg (α := ℝ) m) (sub_nonneg.mpr hq1)
    linarith
  exact (le_div_iff₀ hd).mpr (hprod m)

end Qatlib.Concepts.FinitePrecision.ComputableInput.RationalSqrtSeries
