/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Papers.QDynamicProg18.MainResults.Model
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Push
public import Mathlib.Tactic.Ring

@[expose] public section


/-! A direct weighted-binomial proof of the source entropy bound. -/

set_option autoImplicit false

noncomputable section

open scoped BigOperators

namespace Qatlib.Papers.QDynamicProg18.MainResults

open Qatlib.Papers.QDynamicProg18.MainResults

/-- A Bernoulli monomial is decreasing with its index below the midpoint. -/
theorem bernoulli_weight_le {n k i : ℕ} {p : ℝ}
    (hp : 0 ≤ p) (hpq : p ≤ 1 - p) (hik : i ≤ k) (hkn : k ≤ n) :
    p ^ k * (1 - p) ^ (n - k) ≤ p ^ i * (1 - p) ^ (n - i) := by
  have hq : 0 ≤ 1 - p := hp.trans hpq
  have hsplit : n - i = (k - i) + (n - k) := by omega
  calc
    p ^ k * (1 - p) ^ (n - k)
        = p ^ i * p ^ (k - i) * (1 - p) ^ (n - k) := by
            rw [← pow_add, Nat.add_sub_of_le hik]
    _ ≤ p ^ i * (1 - p) ^ (k - i) * (1 - p) ^ (n - k) :=
          mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hp hpq _) (pow_nonneg hp _))
            (pow_nonneg hq _)
    _ = p ^ i * (1 - p) ^ (n - i) := by rw [hsplit, pow_add]; ring

/-- The lower binomial tail is bounded by the inverse of its endpoint Bernoulli weight. -/
theorem binomial_tail_weighted {n k : ℕ} {p : ℝ}
    (hp : 0 ≤ p) (hpq : p ≤ 1 - p) (hkn : k ≤ n) :
    (∑ i ∈ Finset.range (k + 1), (n.choose i : ℝ)) *
        (p ^ k * (1 - p) ^ (n - k)) ≤ 1 := by
  have hq : 0 ≤ 1 - p := hp.trans hpq
  calc
    (∑ i ∈ Finset.range (k + 1), (n.choose i : ℝ)) *
          (p ^ k * (1 - p) ^ (n - k))
        = ∑ i ∈ Finset.range (k + 1),
            (n.choose i : ℝ) * (p ^ k * (1 - p) ^ (n - k)) :=
              Finset.sum_mul _ _ _
    _ ≤ ∑ i ∈ Finset.range (k + 1),
            p ^ i * (1 - p) ^ (n - i) * (n.choose i : ℝ) := by
          apply Finset.sum_le_sum
          intro i hi
          have hik : i ≤ k := Nat.le_of_lt_succ (Finset.mem_range.mp hi)
          have hw := bernoulli_weight_le hp hpq hik hkn
          have hc : 0 ≤ (n.choose i : ℝ) := Nat.cast_nonneg _
          simpa [mul_comm, mul_left_comm, mul_assoc] using
            mul_le_mul_of_nonneg_left hw hc
    _ ≤ ∑ i ∈ Finset.range (n + 1),
            p ^ i * (1 - p) ^ (n - i) * (n.choose i : ℝ) := by
          apply Finset.sum_le_sum_of_subset_of_nonneg
          · exact Finset.range_mono (Nat.succ_le_succ hkn)
          · intro i _ _
            positivity
    _ = (p + (1 - p)) ^ n := (add_pow p (1 - p) n).symm
    _ = 1 := by simp

end Qatlib.Papers.QDynamicProg18.MainResults
