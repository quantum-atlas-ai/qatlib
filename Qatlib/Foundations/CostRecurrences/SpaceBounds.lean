/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Foundations.CostRecurrences.UniformCosts
import Mathlib.Data.Nat.Size
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

/-!
# Binary-size workspace bounds

Defines `shorBits` as the binary size of a squared integer and bounds the storage of distinct
prime factors and auxiliary registers. For `2 ≤ M ≤ N`, `peak_workspace_le` bounds the stated
storage expression by five times the squared binary size of `N`.

These explicit estimates support the quadratic-logarithmic workspace analysis associated with
[ChauLo1995].

## Main statements

* `factor_table_bits_le`: For `M ≥ 2`, the sum of binary sizes of its distinct prime factors is
  at most `(Nat.size M)²`, supporting the workspace analysis of [ChauLo1995].
* `extra_workspace_with_ancillas`: Including `Nat.size M` additional bits raises the stated
  workspace bound to five times the squared binary size of `M`, for `M ≥ 2`; see [ChauLo1995].
* `peak_workspace_le`: For `2 ≤ M ≤ N`, the prime-factor table size, three `shorBits M`
  registers, and `Nat.size M` additional bits total at most five times the squared binary size
  of `N`; see [ChauLo1995].

## References

* [Chau and Lo, 1995][ChauLo1995]
-/

set_option autoImplicit false
noncomputable section
open scoped BigOperators
namespace Qatlib.Foundations.CostRecurrences.SpaceBounds

/-- The binary size of `M * M`, used as an arithmetic workspace parameter. -/
def shorBits (M : ℕ) : ℕ := Nat.size (M * M)

/-- For `M ≥ 2`, the sum of binary sizes of its distinct prime factors is at most `(Nat.size
M)²`, supporting the workspace analysis of [ChauLo1995]. -/
theorem factor_table_bits_le (M : ℕ) (hM : 2 ≤ M) :
    (∑ p ∈ M.primeFactors, Nat.size p) ≤ Nat.size M * Nat.size M := by
  have hs2 : 2 ≤ Nat.size M := by
    have h2 : Nat.size 2 = 2 := by decide
    have := Nat.size_le_size hM
    omega
  have hsum : (∑ p ∈ M.primeFactors, Nat.size p)
      ≤ ∑ _p ∈ M.primeFactors, Nat.size M := by
    apply Finset.sum_le_sum
    intro p hp
    exact Nat.size_le_size (Nat.le_of_dvd (by omega) (Nat.mem_primeFactors.mp hp).2.1)
  have hconst : (∑ _p ∈ M.primeFactors, Nat.size M)
      = M.primeFactors.card * Nat.size M := by
    rw [Finset.sum_const, Nat.nsmul_eq_mul]
  have hcard := Qatlib.Foundations.CostRecurrences.UniformCosts.card_primeFactors_le_log2 M hM
  have hlog_le : Nat.log 2 M ≤ Nat.size M := by
    have hlt := Nat.lt_size.mpr (Nat.pow_log_le_self 2 (by omega : M ≠ 0))
    omega
  calc (∑ p ∈ M.primeFactors, Nat.size p)
      ≤ M.primeFactors.card * Nat.size M := by rw [← hconst]; exact hsum
    _ ≤ Nat.log 2 M * Nat.size M := Nat.mul_le_mul_right _ hcard
    _ ≤ Nat.size M * Nat.size M := Nat.mul_le_mul_right _ hlog_le

/-- For `M ≥ 2`, `shorBits M` is at most twice the binary size of `M`; this supplies a workspace
estimate for [ChauLo1995]. -/
theorem shorBits_le_two_size (M : ℕ) (hM : 2 ≤ M) :
    shorBits M ≤ 2 * Nat.size M := by
  unfold shorBits
  have hMlt : M < 2 ^ Nat.size M := Nat.lt_size_self M
  have hsq : M * M < 2 ^ (2 * Nat.size M) := by
    have hpos : (0 : ℕ) < 2 ^ Nat.size M := pow_pos (by norm_num) _
    have hpow : (2 : ℕ) ^ (2 * Nat.size M) = 2 ^ Nat.size M * 2 ^ Nat.size M := by
      rw [show 2 * Nat.size M = Nat.size M + Nat.size M by ring, pow_add]
    rw [hpow]
    nlinarith
  exact Nat.size_le.mpr hsq

/-- For `M ≥ 2`, the prime-factor table size plus `3 * shorBits M` is at most four times the
squared binary size of `M`, as a workspace bound motivated by [ChauLo1995]. -/
theorem extra_workspace_le_four_log_sq (M : ℕ) (hM : 2 ≤ M) :
    (∑ p ∈ M.primeFactors, Nat.size p) + 3 * shorBits M
      ≤ 4 * Nat.size M * Nat.size M := by
  have hs2 : 2 ≤ Nat.size M := by
    have h2 : Nat.size 2 = 2 := by decide
    have := Nat.size_le_size hM
    omega
  have htable := factor_table_bits_le M hM
  have hreg := shorBits_le_two_size M hM
  have hthree : 3 * shorBits M ≤ 6 * Nat.size M := by linarith
  nlinarith

/-- Including `Nat.size M` additional bits raises the stated workspace bound to five times the
squared binary size of `M`, for `M ≥ 2`; see [ChauLo1995]. -/
theorem extra_workspace_with_ancillas (M : ℕ) (hM : 2 ≤ M) :
    (∑ p ∈ M.primeFactors, Nat.size p) + 3 * shorBits M + Nat.size M
      ≤ 5 * Nat.size M * Nat.size M := by
  have hs2 : 2 ≤ Nat.size M := by
    have h2 : Nat.size 2 = 2 := by decide
    have := Nat.size_le_size hM
    omega
  have h := extra_workspace_le_four_log_sq M hM
  nlinarith

/-- For `2 ≤ M ≤ N`, the prime-factor table size, three `shorBits M` registers, and `Nat.size M`
additional bits total at most five times the squared binary size of `N`; see [ChauLo1995]. -/
theorem peak_workspace_le (N M : ℕ) (hM : 2 ≤ M) (hMN : M ≤ N) :
    (∑ p ∈ M.primeFactors, Nat.size p) + 3 * shorBits M + Nat.size M
      ≤ 5 * Nat.size N * Nat.size N := by
  have hlocal := extra_workspace_with_ancillas M hM
  have hNM : Nat.size M ≤ Nat.size N := Nat.size_le_size hMN
  have hs2 : 2 ≤ Nat.size N := by
    have h2 : Nat.size 2 = 2 := by decide
    have := Nat.size_le_size (hM.trans hMN)
    omega
  nlinarith

end Qatlib.Foundations.CostRecurrences.SpaceBounds
