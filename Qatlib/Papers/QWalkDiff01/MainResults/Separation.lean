/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.QWalkDiff01.MainResults.ClassicalBound
import Qatlib.Papers.QWalkDiff01.MainResults.LimitingDistribution

/-!
# Classical and quantum propagation separation

This module compares the exponential classical root-probability bound with the reciprocal lower
bound for a quantum limiting distribution in [ChildsFarhiGutmann2002]. The separation results
take the classical estimate as a hypothesis and use elementary exponential inequalities and
equal-magnitude endpoint overlaps.

## Main statements

* `classical_below_quantum_limiting_of_bound`: compares a supplied classical bound with the
  quantum limiting distribution.
* `main_exponential_separation_of_bound`: chooses a depth separating any fixed multiple of the
  exponential bound from the reciprocal bound.

## References

* [Childs et al., 2002][ChildsFarhiGutmann2002]
-/

set_option autoImplicit false
noncomputable section

open Matrix
open scoped Matrix.Norms.L2Operator BigOperators InnerProductSpace RealInnerProductSpace

namespace Qatlib.Papers.QWalkDiff01.MainResults

/-- For `n ≥ 3`, the exponential `2^n` exceeds `2 * n + 1`. -/
theorem two_mul_add_one_lt_two_pow (n : ℕ) (hn : 3 ≤ n) : 2 * n + 1 < 2 ^ n := by
  induction n, hn using Nat.le_induction with
  | base => norm_num
  | succ k hk ih =>
    have hpow : 2 ^ (k + 1) = 2 * 2 ^ k := by rw [pow_succ]; ring
    rw [hpow]
    omega

/-- For `n ≥ 3`, `(1 / 2)^n` is strictly smaller than `1 / (2 * n + 1)`. -/
theorem half_pow_lt_one_div_two_mul_add_one (n : ℕ) (hn : 3 ≤ n) :
    (1 / 2 : ℝ) ^ n < 1 / ((2 * n + 1 : ℕ) : ℝ) := by
  have hnat := two_mul_add_one_lt_two_pow n hn
  have hcast : ((2 * n + 1 : ℕ) : ℝ) < (2 : ℝ) ^ n := by
    have h' : ((2 ^ n : ℕ) : ℝ) = (2 : ℝ) ^ n := by push_cast; ring
    rw [← h']
    exact_mod_cast hnat
  rw [show (1 / 2 : ℝ) ^ n = 1 / (2 : ℝ) ^ n by rw [one_div, inv_pow, one_div]]
  rw [div_lt_div_iff₀ (by positivity) (by positivity)]
  simpa using hcast

/-- For every natural number `j`, `4 * j + 7` is strictly smaller than `2^(j + 3)` over the
reals. -/
theorem four_mul_add_seven_lt_two_pow (j : ℕ) :
    (4 * j + 7 : ℝ) < (2 : ℝ) ^ (j + 3) := by
  induction j with
  | zero => norm_num
  | succ j ih =>
    have hpow : (2 : ℝ) ^ (j + 1 + 3) = 2 * (2 : ℝ) ^ (j + 3) := by
      rw [show j + 1 + 3 = j + 3 + 1 by omega, pow_succ]
      ring
    rw [hpow]
    push_cast at ih ⊢
    nlinarith [ih]

/-- For every nonnegative real `B`, some depth `n ≥ 3` satisfies `B * (1 / 2)^n < 1 / (2 * n +
1)`. -/
theorem exists_half_pow_lt (B : ℝ) (_hB : 0 ≤ B) :
    ∃ n : ℕ, 3 ≤ n ∧ B * (1 / 2 : ℝ) ^ n < 1 / ((2 * n + 1 : ℕ) : ℝ) := by
  obtain ⟨j, hj⟩ := pow_unbounded_of_one_lt B (by norm_num : (1 : ℝ) < 2)
  refine ⟨2 * j + 3, by omega, ?_⟩
  have hval : ((2 * (2 * j + 3) + 1 : ℕ) : ℝ) = 4 * (j : ℝ) + 7 := by
    push_cast; ring
  have hgrow : ((2 * (2 * j + 3) + 1 : ℕ) : ℝ) < (2 : ℝ) ^ (j + 3) := by
    rw [hval]
    exact four_mul_add_seven_lt_two_pow j
  have hcpos : (0 : ℝ) < ((2 * (2 * j + 3) + 1 : ℕ) : ℝ) := by positivity
  have hmul : B * ((2 * (2 * j + 3) + 1 : ℕ) : ℝ) < (2 : ℝ) ^ (2 * j + 3) := by
    calc B * ((2 * (2 * j + 3) + 1 : ℕ) : ℝ)
        < (2 : ℝ) ^ j * ((2 * (2 * j + 3) + 1 : ℕ) : ℝ) :=
          mul_lt_mul_of_pos_right hj hcpos
      _ < (2 : ℝ) ^ j * (2 : ℝ) ^ (j + 3) :=
          mul_lt_mul_of_pos_left hgrow (by positivity)
      _ = (2 : ℝ) ^ (2 * j + 3) := by
          rw [← pow_add]
          congr 1
          omega
  rw [show (1 / 2 : ℝ) ^ (2 * j + 3) = 1 / (2 : ℝ) ^ (2 * j + 3) by
    rw [one_div, inv_pow, one_div]]
  rw [mul_one_div, div_lt_div_iff₀ (by positivity) (by positivity)]
  simpa using hmul

/-- At depth `n ≥ 3`, a classical root probability below `(1 / 2)^n` is smaller than the
limiting distribution of a unit source with equal-magnitude source and target basis
overlaps. -/
theorem classical_below_quantum_limiting_of_bound (n : ℕ) (hn : 3 ≤ n) (γ : ℝ)
    (t : ℝ)
    (hclassical : classicalColumnProb n γ t (rightRoot n) < (1 / 2 : ℝ) ^ n)
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (basis : OrthonormalBasis (Fin (2 * n + 1)) ℝ E) (a c : E) (ha : ‖a‖ = 1)
    (hparity : ∀ r : Fin (2 * n + 1), |⟪basis r, a⟫_ℝ| = |⟪basis r, c⟫_ℝ|) :
    classicalColumnProb n γ t (rightRoot n) < limitingDistribution basis a c := by
  have hq := limitingDistribution_rightRoot_lower_bound n basis a c ha hparity
  have harith := half_pow_lt_one_div_two_mul_add_one n hn
  exact lt_of_lt_of_le (lt_trans hclassical harith) hq

/-- Given the classical exponential bound at every positive depth and nonnegative time, some
depth `n ≥ 3` satisfies that bound and separates `B * (1 / 2)^n` from `1 / (2 * n + 1)`.
This is the numerical separation used in [ChildsFarhiGutmann2002]. -/
theorem main_exponential_separation_of_bound (γ : ℝ) (B : ℝ) (hB : 0 ≤ B)
    (hclassical : ∀ n : ℕ, 1 ≤ n → ∀ t : ℝ, 0 ≤ t →
      classicalColumnProb n γ t (rightRoot n) < (1 / 2 : ℝ) ^ n) :
    ∃ n : ℕ, 3 ≤ n ∧
      (∀ t : ℝ, 0 ≤ t → classicalColumnProb n γ t (rightRoot n) < (1 / 2 : ℝ) ^ n) ∧
      B * (1 / 2 : ℝ) ^ n < 1 / ((2 * n + 1 : ℕ) : ℝ) := by
  obtain ⟨n, hn, hsep⟩ := exists_half_pow_lt B hB
  exact ⟨n, hn, fun t ht => hclassical n (by omega) t ht, hsep⟩

end Qatlib.Papers.QWalkDiff01.MainResults
