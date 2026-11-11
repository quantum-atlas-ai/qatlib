/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.RingTheory.Polynomial.Bernstein
import Mathlib.Algebra.Polynomial.BigOperators
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# Bernstein majority polynomials for error amplification

`majorityPolynomial` sums the Bernstein terms of degree `2 * m` with indices at least `m`. It
preserves `[0, 1]`, has degree at most `2 * m`, and satisfies the geometric error estimates
`majorityPolynomial_low` and `majorityPolynomial_high` on `[0, 1 / 8]` and `[7 / 8, 1]`.

These estimates provide the polynomial amplification used in the CBMD approximation construction
associated with [WangEtAl2026].

## Main statements

* `majorityPolynomial_degree` bounds the degree by `2 * m`.
* `majorityPolynomial_unit_interval` proves preservation of `[0, 1]`.
* `majorityPolynomial_low` and `majorityPolynomial_high` give geometric error bounds.

## References

* [Wang et al., 2026][WangEtAl2026]
-/

namespace Qatlib.Papers.Cbmd26.Algorithms

set_option autoImplicit false
set_option maxHeartbeats 200000

namespace CBMD

open Polynomial
open scoped BigOperators Classical

/-- The sum of Bernstein basis polynomials of degree `2 * m` with indices from `m` through `2 *
m`, representing the binomial probability of at least `m` successes in `2 * m` trials. -/
noncomputable def majorityPolynomial (m : ℕ) : Polynomial ℝ :=
  ∑ j ∈ Finset.range (2 * m + 1),
    if m ≤ j then bernsteinPolynomial ℝ (2 * m) j else 0

/-- Every real Bernstein basis polynomial evaluates to a nonnegative number on `[0, 1]`. -/
theorem bernstein_eval_nonneg (n j : ℕ) (x : ℝ) (hx : x ∈ Set.Icc (0 : ℝ) 1) :
    0 ≤ (bernsteinPolynomial ℝ n j).eval x := by
  simp only [bernsteinPolynomial, eval_mul, eval_natCast, eval_pow, eval_X,
    eval_sub, eval_one]
  exact mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (pow_nonneg hx.1 _))
    (pow_nonneg (sub_nonneg.mpr hx.2) _)

/-- The majority polynomial with parameter `m` has natural degree at most `2 * m`. -/
theorem majorityPolynomial_degree (m : ℕ) : (majorityPolynomial m).natDegree ≤ 2 * m := by
  unfold majorityPolynomial
  apply natDegree_sum_le_of_forall_le
  intro j hj
  split_ifs
  · have hjn : j ≤ 2 * m := Nat.le_of_lt_succ (Finset.mem_range.mp hj)
    have hdeg : (1 - X : Polynomial ℝ).natDegree ≤ 1 := by
      exact (natDegree_sub_le (1 : Polynomial ℝ) X).trans (by simp)
    calc
      _ ≤ ((2 * m).choose j : Polynomial ℝ).natDegree + (X ^ j : Polynomial ℝ).natDegree +
          ((1 - X : Polynomial ℝ) ^ (2 * m - j)).natDegree :=
        natDegree_mul_le.trans (Nat.add_le_add_right natDegree_mul_le _)
      _ ≤ 0 + j + (2 * m - j) := by
        gcongr
        · simp
        · simp
        · exact (natDegree_pow_le_of_le _ hdeg).trans_eq (mul_one _)
      _ = 2 * m := by omega
  · simp

/-- The majority polynomial maps `[0, 1]` into `[0, 1]`. -/
theorem majorityPolynomial_unit_interval (m : ℕ) (x : ℝ)
    (hx : x ∈ Set.Icc (0 : ℝ) 1) :
    (majorityPolynomial m).eval x ∈ Set.Icc (0 : ℝ) 1 := by
  have hsum : (∑ j ∈ Finset.range (2 * m + 1),
      (bernsteinPolynomial ℝ (2 * m) j).eval x) = 1 := by
    simpa only [eval_finsetSum, eval_one] using
      congrArg (Polynomial.eval x) (bernsteinPolynomial.sum ℝ (2 * m))
  rw [majorityPolynomial, eval_finsetSum]
  constructor
  · apply Finset.sum_nonneg
    intro j _
    split_ifs
    · exact bernstein_eval_nonneg _ _ _ hx
    · simp
  · rw [← hsum]
    apply Finset.sum_le_sum
    intro j _
    split_ifs
    · exact le_rfl
    · simpa using bernstein_eval_nonneg (2 * m) j x hx

/-- On `[0, 1]`, the majority polynomial is bounded above by `(4 * x) ^ m`. -/
private theorem binomial_tail_bound (m : ℕ) (x : ℝ)
    (hx : x ∈ Set.Icc (0 : ℝ) 1) :
    (majorityPolynomial m).eval x ≤ (4 * x) ^ m := by
  have hx0 : 0 ≤ x := hx.1
  have hx1 : 0 ≤ 1 - x := sub_nonneg.mpr hx.2
  rw [majorityPolynomial, eval_finsetSum]
  calc
    _ ≤ ∑ j ∈ Finset.range (2 * m + 1), ((2 * m).choose j : ℝ) * x ^ m := by
      apply Finset.sum_le_sum
      intro j _
      split_ifs with hj
      · simp only [bernsteinPolynomial, eval_mul, eval_natCast, eval_pow, eval_X,
          eval_sub, eval_one]
        have hp : x ^ j ≤ x ^ m := pow_le_pow_of_le_one hx.1 hx.2 hj
        have hq : (1 - x) ^ (2 * m - j) ≤ 1 :=
          pow_le_one₀ (by linarith [hx.2]) (by linarith [hx.1])
        calc
          _ ≤ ((2 * m).choose j : ℝ) * x ^ m * 1 := by gcongr
          _ = _ := mul_one _
      · simp only [eval_zero]
        positivity
    _ = (4 * x) ^ m := by
      rw [← Finset.sum_mul]
      have hc : (∑ j ∈ Finset.range (2 * m + 1), ((2 * m).choose j : ℝ)) =
          (2 : ℝ) ^ (2 * m) := by exact_mod_cast Nat.sum_range_choose (2 * m)
      rw [hc, pow_mul, mul_pow]
      norm_num

/-- On `[0, 1]`, the complement of the majority polynomial is bounded above by `(4 * (1 - x)) ^
m`. -/
private theorem binomial_complement_bound (m : ℕ) (x : ℝ)
    (hx : x ∈ Set.Icc (0 : ℝ) 1) :
    1 - (majorityPolynomial m).eval x ≤ (4 * (1 - x)) ^ m := by
  have hsum : (∑ j ∈ Finset.range (2 * m + 1),
      (bernsteinPolynomial ℝ (2 * m) j).eval x) = 1 := by
    simpa only [eval_finsetSum, eval_one] using
      congrArg (Polynomial.eval x) (bernsteinPolynomial.sum ℝ (2 * m))
  have hx0 : 0 ≤ x := hx.1
  have hx1 : 0 ≤ 1 - x := sub_nonneg.mpr hx.2
  conv_lhs => rw [← hsum, majorityPolynomial, eval_finsetSum, ← Finset.sum_sub_distrib]
  calc
    _ ≤ ∑ j ∈ Finset.range (2 * m + 1), ((2 * m).choose j : ℝ) * (1 - x) ^ m := by
      apply Finset.sum_le_sum
      intro j hjrange
      split_ifs with hj
      · simp only [sub_self]
        positivity
      · simp only [eval_zero, sub_zero, bernsteinPolynomial, eval_mul, eval_natCast,
          eval_pow, eval_X, eval_sub, eval_one]
        have hp : x ^ j ≤ 1 := pow_le_one₀ hx.1 hx.2
        have hq : (1 - x) ^ (2 * m - j) ≤ (1 - x) ^ m :=
          pow_le_pow_of_le_one (by linarith [hx.2]) (by linarith [hx.1]) (by omega)
        calc
          _ ≤ ((2 * m).choose j : ℝ) * 1 * (1 - x) ^ m := by gcongr
          _ = _ := by rw [mul_one]
    _ = (4 * (1 - x)) ^ m := by
      rw [← Finset.sum_mul]
      have hc : (∑ j ∈ Finset.range (2 * m + 1), ((2 * m).choose j : ℝ)) =
          (2 : ℝ) ^ (2 * m) := by exact_mod_cast Nat.sum_range_choose (2 * m)
      rw [hc, pow_mul, mul_pow]
      norm_num

/-- On `[0, 1 / 8]`, the majority polynomial is at most `(1 / 2) ^ m`. -/
theorem majorityPolynomial_low (m : ℕ) (x : ℝ)
    (hx : x ∈ Set.Icc (0 : ℝ) (1 / 8)) :
    (majorityPolynomial m).eval x ≤ (1 / 2 : ℝ) ^ m := by
  exact (binomial_tail_bound m x ⟨hx.1, by linarith [hx.2]⟩).trans
    (pow_le_pow_left₀ (by linarith [hx.1]) (by linarith [hx.2]) m)

/-- On `[7 / 8, 1]`, the majority polynomial differs from `1` by at most `(1 / 2) ^ m`. -/
theorem majorityPolynomial_high (m : ℕ) (x : ℝ)
    (hx : x ∈ Set.Icc (7 / 8 : ℝ) 1) :
    1 - (majorityPolynomial m).eval x ≤ (1 / 2 : ℝ) ^ m := by
  exact (binomial_complement_bound m x ⟨by linarith [hx.1], hx.2⟩).trans
    (pow_le_pow_left₀ (by linarith [hx.2]) (by linarith [hx.1]) m)

end CBMD

end Qatlib.Papers.Cbmd26.Algorithms
