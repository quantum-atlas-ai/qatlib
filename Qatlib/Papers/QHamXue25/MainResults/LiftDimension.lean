/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Mathlib.Data.Nat.Choose.Sum

@[expose] public section

/-!
# Lifted variable and discretized dimension counts

For each homotopy order, summing over the auxiliary-variable count is an ordinary
binomial expansion. Summing across orders gives the two size identities.
-/

set_option autoImplicit false

open scoped BigOperators

namespace Qatlib.Papers.QHamXue25.MainResults

/-- The fixed-order dimension contribution is a binomial expansion. -/
private theorem binomial_block (n m j : ℕ) (hj : j < m + 1) :
    (∑ i ∈ Finset.range (m + 1), (if i ≤ j then j.choose i else 0) * n ^ (i + 1)) =
      n * (n + 1) ^ j := by
  have hs : (∑ i ∈ Finset.range (j + 1), (if i ≤ j then j.choose i else 0) * n ^ (i + 1)) =
      ∑ i ∈ Finset.range (m + 1), (if i ≤ j then j.choose i else 0) * n ^ (i + 1) :=
    Finset.sum_subset (Finset.range_mono (by omega)) (by
      intro i _ hi
      have : ¬i ≤ j := fun h => hi (Finset.mem_range.mpr (by omega))
      simp [this])
  rw [← hs, add_pow, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  have hle : i ≤ j := by have := Finset.mem_range.1 hi; omega
  simp only [ite_eq_left hle, one_pow, mul_one, pow_succ]
  ac_rfl

/-- The dimension from the higher variable blocks plus one is a power of `n + 1`. -/
private theorem auxiliary_dimension (n m : ℕ) :
    1 + ∑ i ∈ Finset.range m, ∑ j ∈ Finset.range m,
      (if i ≤ j then j.choose i else 0) * n ^ (i + 1) = (n + 1) ^ m := by
  rw [Finset.sum_comm]
  induction m with
  | zero => simp
  | succ m ih =>
    have houter : (∑ j ∈ Finset.range (m + 1), ∑ i ∈ Finset.range (m + 1),
        (if i ≤ j then j.choose i else 0) * n ^ (i + 1)) =
        ∑ j ∈ Finset.range (m + 1), n * (n + 1) ^ j := by
      exact Finset.sum_congr rfl (fun j hj => binomial_block n m j (Finset.mem_range.mp hj))
    have hprev : (∑ j ∈ Finset.range m, ∑ i ∈ Finset.range m,
        (if i ≤ j then j.choose i else 0) * n ^ (i + 1)) =
        ∑ j ∈ Finset.range m, n * (n + 1) ^ j := by
      cases m with
      | zero => simp
      | succ k =>
        exact Finset.sum_congr rfl (fun j hj => binomial_block n k j (Finset.mem_range.mp hj))
    rw [hprev] at ih
    rw [houter, Finset.sum_range_succ, ← add_assoc, ih, pow_succ]
    ring

/-- Equation (50) counts all variables, including the initial solution variable. -/
theorem variable_count (m : ℕ) :
    1 + ∑ i ∈ Finset.range (m + 1), ∑ j ∈ Finset.range (m + 1),
      (if i ≤ j then j.choose i else 0) = 2 ^ (m + 1) := by
  simpa using auxiliary_dimension 1 (m + 1)

/-- Equation (55) gives the dimension of the discretized lift. -/
theorem ode_dimension (n m : ℕ) :
    n + ∑ i ∈ Finset.range (m + 1), ∑ j ∈ Finset.range (m + 1),
      (if i ≤ j then j.choose i else 0) * n ^ (i + 1) = (n + 1) ^ (m + 1) + n - 1 := by
  have h := auxiliary_dimension n (m + 1)
  omega

end Qatlib.Papers.QHamXue25.MainResults
