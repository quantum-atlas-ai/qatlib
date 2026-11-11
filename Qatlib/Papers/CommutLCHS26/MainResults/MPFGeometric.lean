/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.CommutLCHS26.MainResults.MPFRootProfile

/-!
# Geometric estimates for multi-product tails

This module supplies scalar factorial and geometric inequalities used to bound
commutator-profile tails in the multi-product analysis of [AftabAnTrivisa2026]. The partial
reciprocal-factorial sum `factorialMass` is bounded by 2, and higher powers at arguments at most
1/2 are controlled by a geometric sequence.

## Main statements

* `factorialMass_le`: bounds the reciprocal-factorial partial sum.
* `power_tail_le`: dominates the higher-order tail by powers of 1/4.

## References

* [Aftab et al., 2026][AftabAnTrivisa2026]
-/

set_option backward.isDefEq.respectTransparency false
set_option warningAsError false

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.CommutLCHS26.MainResults.MPFGeometric

open scoped BigOperators

/-- The reciprocal of (r + 1) factorial is at most (1/2)^r. -/
theorem inv_factorial_le (r : ℕ) : 1 / ((r + 1).factorial : ℝ) ≤ (1 / 2 : ℝ) ^ r := by
  have hf : (2 : ℕ) ^ r ≤ (r + 1).factorial := by
    induction r with
    | zero => norm_num
    | succ r ih =>
      rw [Nat.factorial_succ, pow_succ]
      calc
        _ = 2 * 2 ^ r := by ring
        _ ≤ (r + 1 + 1) * (r + 1).factorial := Nat.mul_le_mul (by omega) ih
  have hfr : (2 : ℝ) ^ r ≤ ((r + 1).factorial : ℝ) := by exact_mod_cast hf
  calc
    _ ≤ 1 / (2 : ℝ) ^ r := one_div_le_one_div_of_le (by positivity) hfr
    _ = _ := by simp only [div_pow, one_pow]

/-- The sum of 1/(j + 1)! over j < m. -/
def factorialMass (m : ℕ) : ℝ := ∑ j ∈ Finset.range m, 1 / ((j + 1).factorial : ℝ)

/-- Increasing the factorial-mass cutoff by one adds 1/(m + 1)!. -/
theorem factorialMass_succ (m : ℕ) :
    factorialMass (m + 1) = factorialMass m + 1 / ((m + 1).factorial : ℝ) := by
  exact Finset.sum_range_succ _ _

/-- Every factorial-mass partial sum is at most 2. -/
theorem factorialMass_le (m : ℕ) : factorialMass m ≤ 2 := by
  have hs := summable_geometric_of_norm_lt_one (by norm_num : ‖(1 / 2 : ℝ)‖ < 1)
  calc
    _ ≤ ∑ j ∈ Finset.range m, (1 / 2 : ℝ) ^ j :=
      Finset.sum_le_sum fun j _ => inv_factorial_le j
    _ ≤ ∑' j, (1 / 2 : ℝ) ^ j :=
      hs.sum_le_tsum _ (fun j _ => pow_nonneg (by norm_num) j)
    _ = _ := by rw [tsum_geometric_of_norm_lt_one (by norm_num : ‖(1 / 2 : ℝ)‖ < 1)]; norm_num

/-- For 0 ≤ b ≤ 1/2 and l ≥ 1, the power b^(2(k + m) + l) is bounded by b^(2m + 1)(1/4)^k. -/
theorem power_tail_le (b : ℝ) (hb : 0 ≤ b) (hhalf : b ≤ 1 / 2)
    (m k l : ℕ) (hl : 1 ≤ l) :
    b ^ (2 * (k + m) + l) ≤ b ^ (2 * m + 1) * (1 / 4 : ℝ) ^ k := by
  have hb1 : b ≤ 1 := by linarith
  have hq : (b ^ 2) ^ k ≤ (1 / 4 : ℝ) ^ k :=
    pow_le_pow_left₀ (sq_nonneg b) (by nlinarith) k
  have hp : b ^ (l - 1) ≤ 1 := pow_le_one₀ hb hb1
  calc
    _ = (b ^ (2 * m + 1) * (b ^ 2) ^ k) * b ^ (l - 1) := by
      rw [← pow_mul, ← pow_add, ← pow_add]
      congr 1
      omega
    _ ≤ (b ^ (2 * m + 1) * (1 / 4 : ℝ) ^ k) * 1 :=
      mul_le_mul (mul_le_mul_of_nonneg_left hq (pow_nonneg hb _)) hp
        (pow_nonneg hb _) (mul_nonneg (pow_nonneg hb _) (by positivity))
    _ = _ := mul_one _

end Qatlib.Papers.CommutLCHS26.MainResults.MPFGeometric
