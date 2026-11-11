/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.Asymptotics.Defs
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Nat.Cast.Order.Field
import Qatlib.Concepts.AmplitudeSearch.Amplification.QueryBudgetSuccess

/-!
# Periodic quantum Dijkstra work bounds

This module models the search and update costs of the periodically updated quantum Dijkstra
algorithm in [Heiligman2003]. The functions `quantumSearchWork` and `quantumUpdateWork` have
maximum `quantumDijkstraWork`, minimized at the update period `Real.sqrt n`.

The results give the exact optimal work n^(7/4), its asymptotic bound, and bounds on the
corresponding finite sums. The classical comparison uses `classicalDijkstraWork`.

## Main statements

* `quantum_dijkstra_optimal_work`: The square-root update period minimizes the work model.
* `quantum_search_sum_le_work`: The search sum is bounded by the search work model.
* `quantum_update_sum_le_work`: The update sum is bounded by the update work model.

## References

* [Heiligman, 2003][Heiligman2003]
-/

set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false
noncomputable section

open Filter
open scoped BigOperators

namespace Qatlib.Papers.LowWeightPath03.MainResults.PeriodicDijkstra

/-- The quantum search work model k^(1/2) n^(3/2) for size `n` and update period `k`. -/
def quantumSearchWork (n k : ℝ) : ℝ := k ^ (1 / 2 : ℝ) * n ^ (3 / 2 : ℝ)

/-- The quantum update work model k^(-1/2) n² for size `n` and update period `k`. -/
def quantumUpdateWork (n k : ℝ) : ℝ := k ^ (-(1 / 2) : ℝ) * n ^ (2 : ℝ)

/-- The maximum of the quantum search and update work models. -/
def quantumDijkstraWork (n k : ℝ) : ℝ :=
  max (quantumSearchWork n k) (quantumUpdateWork n k)

/-- The classical search work model k n². -/
def classicalSearchWork (n k : ℝ) : ℝ := k * n ^ 2

/-- The maximum of the classical search work and n². -/
def classicalDijkstraWork (n k : ℝ) : ℝ := max (classicalSearchWork n k) (n ^ 2)

/-- The minimum-finding query budget is O(√N) as the natural-number input size tends to
infinity. -/
theorem minimum_finding_budget_bigO_sqrt :
    Asymptotics.IsBigO Filter.atTop
      (fun N : ℕ =>
        (Qatlib.Concepts.AmplitudeSearch.Amplification.minimumQueryBudget N : ℝ))
      (fun N : ℕ => Real.sqrt (N : ℝ)) :=
  Qatlib.Concepts.AmplitudeSearch.Amplification.minimumQueryBudget_isBigO_sqrt

/-- For nonnegative `n`, the half power of √n equals n^(1/4). -/
theorem sqrt_rpow_half (n : ℝ) (hn : 0 ≤ n) :
    Real.sqrt n ^ (1 / 2 : ℝ) = n ^ (1 / 4 : ℝ) := by
  rw [Real.sqrt_eq_rpow, ← Real.rpow_mul hn]
  congr 1
  norm_num

/-- For positive `n`, the quantum search work at period √n is n^(7/4). -/
theorem search_at_sqrt (n : ℝ) (hn : 0 < n) :
    quantumSearchWork n (Real.sqrt n) = n ^ (7 / 4 : ℝ) := by
  unfold quantumSearchWork
  rw [sqrt_rpow_half n hn.le, ← Real.rpow_add hn]
  congr 1
  norm_num

/-- For positive `n`, the quantum update work at period √n is n^(7/4). -/
theorem update_at_sqrt (n : ℝ) (hn : 0 < n) :
    quantumUpdateWork n (Real.sqrt n) = n ^ (7 / 4 : ℝ) := by
  unfold quantumUpdateWork
  rw [Real.sqrt_eq_rpow, ← Real.rpow_mul hn.le, ← Real.rpow_add hn]
  congr 1
  norm_num

/-- For positive `n` and `k`, the product of the search and update work models is n^(7/2). -/
theorem search_mul_update (n k : ℝ) (hn : 0 < n) (hk : 0 < k) :
    quantumSearchWork n k * quantumUpdateWork n k = n ^ (7 / 2 : ℝ) := by
  have hk1 : k ^ (1 / 2 : ℝ) * k ^ (-(1 / 2) : ℝ) = 1 := by
    rw [← Real.rpow_add hk]
    norm_num
  have hn1 : n ^ (3 / 2 : ℝ) * n ^ (2 : ℝ) = n ^ (7 / 2 : ℝ) := by
    rw [← Real.rpow_add hn]
    norm_num
  unfold quantumSearchWork quantumUpdateWork
  calc k ^ (1 / 2 : ℝ) * n ^ (3 / 2 : ℝ) * (k ^ (-(1 / 2) : ℝ) * n ^ (2 : ℝ))
      = (k ^ (1 / 2 : ℝ) * k ^ (-(1 / 2) : ℝ)) *
          (n ^ (3 / 2 : ℝ) * n ^ (2 : ℝ)) := by ring
    _ = 1 * n ^ (7 / 2 : ℝ) := by rw [hk1, hn1]
    _ = n ^ (7 / 2 : ℝ) := one_mul _

/-- The geometric mean of two nonnegative real numbers is at most their maximum. -/
theorem sqrt_mul_le_max {A B : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B) :
    Real.sqrt (A * B) ≤ max A B := by
  rcases le_total A B with h | h
  · have hmul : A * B ≤ B * B := mul_le_mul_of_nonneg_right h hB
    have hs : Real.sqrt (A * B) ≤ Real.sqrt (B * B) := Real.sqrt_le_sqrt hmul
    rw [Real.sqrt_mul_self hB] at hs
    exact hs.trans (le_max_right A B)
  · have hmul : A * B ≤ A * A := mul_le_mul_of_nonneg_left h hA
    have hs : Real.sqrt (A * B) ≤ Real.sqrt (A * A) := Real.sqrt_le_sqrt hmul
    rw [Real.sqrt_mul_self hA] at hs
    exact hs.trans (le_max_left A B)

/-- For positive `n`, the quantum Dijkstra work at period √n equals n^(7/4). -/
theorem quantumDijkstraWork_at_sqrt (n : ℝ) (hn : 0 < n) :
    quantumDijkstraWork n (Real.sqrt n) = n ^ (7 / 4 : ℝ) := by
  unfold quantumDijkstraWork
  rw [search_at_sqrt n hn, update_at_sqrt n hn, max_self]

/-- For positive `n`, period √n minimizes `quantumDijkstraWork` among positive periods and gives
work n^(7/4) [Heiligman2003]. -/
theorem quantum_dijkstra_optimal_work (n : ℝ) (hn : 0 < n) :
    (∀ k : ℝ, 0 < k → quantumDijkstraWork n (Real.sqrt n) ≤ quantumDijkstraWork n k) ∧
      quantumDijkstraWork n (Real.sqrt n) = n ^ (7 / 4 : ℝ) := by
  refine ⟨fun k hk => ?_, quantumDijkstraWork_at_sqrt n hn⟩
  rw [quantumDijkstraWork_at_sqrt n hn]
  have hA : 0 ≤ quantumSearchWork n k :=
    mul_nonneg (Real.rpow_nonneg hk.le _) (Real.rpow_nonneg hn.le _)
  have hB : 0 ≤ quantumUpdateWork n k :=
    mul_nonneg (Real.rpow_nonneg hk.le _) (Real.rpow_nonneg hn.le _)
  have hprod := search_mul_update n k hn hk
  have hsq : n ^ (7 / 4 : ℝ) = Real.sqrt (n ^ (7 / 2 : ℝ)) := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_mul hn.le]
    congr 1
    norm_num
  calc n ^ (7 / 4 : ℝ)
      = Real.sqrt (quantumSearchWork n k * quantumUpdateWork n k) := by
        rw [hprod]
        exact hsq
    _ ≤ max (quantumSearchWork n k) (quantumUpdateWork n k) := sqrt_mul_le_max hA hB
    _ = quantumDijkstraWork n k := rfl

/-- The quantum Dijkstra work model at period √n is O(n^(7/4)) at infinity [Heiligman2003]. -/
theorem quantum_dijkstra_work_isBigO :
    Asymptotics.IsBigO Filter.atTop
      (fun n : ℝ => quantumDijkstraWork n (Real.sqrt n))
      (fun n : ℝ => n ^ (7 / 4 : ℝ)) := by
  refine Asymptotics.IsBigO.of_bound 1 ?_
  filter_upwards [Filter.eventually_gt_atTop (0 : ℝ)] with n hn
  rw [quantumDijkstraWork_at_sqrt n hn]
  simp [Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg hn.le _)]

/-- For positive `n` and `k`, the quantum search and update work models agree exactly when k =
√n [Heiligman2003]. -/
theorem quantum_dijkstra_balance (n k : ℝ) (hn : 0 < n) (hk : 0 < k) :
    quantumSearchWork n k = quantumUpdateWork n k ↔ k = Real.sqrt n := by
  constructor
  · intro h
    have hkpos : 0 < k ^ (1 / 2 : ℝ) := Real.rpow_pos_of_pos hk _
    have hnpos : 0 < n ^ (3 / 2 : ℝ) := Real.rpow_pos_of_pos hn _
    have hkp : 0 < k ^ (-(1 / 2) : ℝ) := Real.rpow_pos_of_pos hk _
    have hnp : 0 < n ^ (2 : ℝ) := Real.rpow_pos_of_pos hn _
    have hlog : Real.log (quantumSearchWork n k) = Real.log (quantumUpdateWork n k) := by
      rw [h]
    unfold quantumSearchWork quantumUpdateWork at hlog
    rw [Real.log_mul hkpos.ne' hnpos.ne', Real.log_mul hkp.ne' hnp.ne',
      Real.log_rpow hk, Real.log_rpow hn, Real.log_rpow hk, Real.log_rpow hn] at hlog
    have hlogk : Real.log k = (1 / 2 : ℝ) * Real.log n := by linarith
    have hsqrtpos : 0 < Real.sqrt n := Real.sqrt_pos.2 hn
    have hlogsqrt : Real.log (Real.sqrt n) = (1 / 2 : ℝ) * Real.log n := by
      rw [Real.sqrt_eq_rpow, Real.log_rpow hn]
    have hlogs : Real.log k = Real.log (Real.sqrt n) := by rw [hlogk, hlogsqrt]
    exact Real.log_injOn_pos (Set.mem_Ioi.mpr hk) (Set.mem_Ioi.mpr hsqrtpos) hlogs
  · intro h
    rw [h, search_at_sqrt n hn, update_at_sqrt n hn]

/-- For n > 1, the quantum work exponent gives n^(7/4) < n² [Heiligman2003]. -/
theorem quantum_beats_classical (n : ℝ) (hn : 1 < n) :
    n ^ (7 / 4 : ℝ) < n ^ 2 := by
  have h : (7 / 4 : ℝ) < 2 := by norm_num
  have hlt := Real.rpow_lt_rpow_of_exponent_lt hn h
  simpa [Real.rpow_two] using hlt

/-- For every real `n`, the classical work is at least n² for periods k ≥ 1 and equals n² at k =
1. -/
theorem classical_dijkstra_optimal (n : ℝ) :
    (∀ k : ℝ, 1 ≤ k → n ^ 2 ≤ classicalDijkstraWork n k) ∧
      classicalDijkstraWork n 1 = n ^ 2 := by
  constructor
  · intro k _
    exact le_max_right _ _
  · unfold classicalDijkstraWork classicalSearchWork
    rw [one_mul, max_self]

/-- The sum of √(k(n − i)) over i < n is at most n√(kn), with natural-number subtraction in each
summand. -/
theorem quantum_search_sum_le (n k : ℕ) :
    (∑ i ∈ Finset.range n, Real.sqrt ((k : ℝ) * ((n - i : ℕ) : ℝ)))
      ≤ (n : ℝ) * Real.sqrt ((k : ℝ) * (n : ℝ)) := by
  calc
    (∑ i ∈ Finset.range n, Real.sqrt ((k : ℝ) * ((n - i : ℕ) : ℝ)))
        ≤ ∑ _i ∈ Finset.range n, Real.sqrt ((k : ℝ) * (n : ℝ)) := by
          refine Finset.sum_le_sum (fun i _hi => ?_)
          refine Real.sqrt_le_sqrt ?_
          have hle : ((n - i : ℕ) : ℝ) ≤ (n : ℝ) := by
            exact_mod_cast Nat.sub_le n i
          exact mul_le_mul_of_nonneg_left hle (Nat.cast_nonneg k)
    _ = (n : ℝ) * Real.sqrt ((k : ℝ) * (n : ℝ)) := by
          rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]

/-- For natural `n` and `k`, the search bound n√(kn) equals √k n√n. -/
theorem search_bound_eq (n k : ℕ) :
    (n : ℝ) * Real.sqrt ((k : ℝ) * (n : ℝ)) =
      Real.sqrt (k : ℝ) * (n : ℝ) * Real.sqrt (n : ℝ) := by
  rw [Real.sqrt_mul (Nat.cast_nonneg k)]
  ring

/-- For positive `n`, the product n√n equals n^(3/2). -/
theorem mul_sqrt_eq_rpow (n : ℝ) (hn : 0 < n) :
    n * Real.sqrt n = n ^ (3 / 2 : ℝ) := by
  calc n * Real.sqrt n = n * n ^ (1 / 2 : ℝ) := by rw [Real.sqrt_eq_rpow]
    _ = n ^ (1 : ℝ) * n ^ (1 / 2 : ℝ) := by rw [Real.rpow_one]
    _ = n ^ ((1 : ℝ) + 1 / 2) := by rw [Real.rpow_add hn]
    _ = n ^ (3 / 2 : ℝ) := by norm_num

/-- For positive natural `n`, the finite search-cost sum is bounded by `quantumSearchWork n k`
[Heiligman2003]. -/
theorem quantum_search_sum_le_work (n k : ℕ) (hn : 0 < n) :
    (∑ i ∈ Finset.range n, Real.sqrt ((k : ℝ) * ((n - i : ℕ) : ℝ)))
      ≤ quantumSearchWork (n : ℝ) (k : ℝ) := by
  have hnR : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  calc
    (∑ i ∈ Finset.range n, Real.sqrt ((k : ℝ) * ((n - i : ℕ) : ℝ)))
        ≤ (n : ℝ) * Real.sqrt ((k : ℝ) * (n : ℝ)) := quantum_search_sum_le n k
    _ = Real.sqrt (k : ℝ) * (n : ℝ) * Real.sqrt (n : ℝ) := search_bound_eq n k
    _ = Real.sqrt (k : ℝ) * ((n : ℝ) * Real.sqrt (n : ℝ)) := by ring
    _ = Real.sqrt (k : ℝ) * (n : ℝ) ^ (3 / 2 : ℝ) := by
          rw [mul_sqrt_eq_rpow (n : ℝ) hnR]
    _ = quantumSearchWork (n : ℝ) (k : ℝ) := by
          unfold quantumSearchWork
          rw [Real.sqrt_eq_rpow (k : ℝ)]

/-- For positive natural `k`, the update-cost sum over h < n / k is at most n²√k / k. -/
theorem quantum_update_sum_le (n k : ℕ) (hk : 0 < k) :
    (∑ h ∈ Finset.range (n / k), ((n - k * h : ℕ) : ℝ) * Real.sqrt (k : ℝ))
      ≤ (n : ℝ) ^ 2 * Real.sqrt (k : ℝ) / (k : ℝ) := by
  have hkR : (0 : ℝ) < (k : ℝ) := by exact_mod_cast hk
  calc
    (∑ h ∈ Finset.range (n / k), ((n - k * h : ℕ) : ℝ) * Real.sqrt (k : ℝ))
        ≤ ∑ _h ∈ Finset.range (n / k), (n : ℝ) * Real.sqrt (k : ℝ) := by
          refine Finset.sum_le_sum (fun h _hh => ?_)
          have hle : ((n - k * h : ℕ) : ℝ) ≤ (n : ℝ) := by
            exact_mod_cast Nat.sub_le n (k * h)
          exact mul_le_mul_of_nonneg_right hle (Real.sqrt_nonneg _)
    _ = ((n / k : ℕ) : ℝ) * ((n : ℝ) * Real.sqrt (k : ℝ)) := by
          rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    _ ≤ ((n : ℝ) / (k : ℝ)) * ((n : ℝ) * Real.sqrt (k : ℝ)) := by
          refine mul_le_mul_of_nonneg_right Nat.cast_div_le ?_
          exact mul_nonneg (Nat.cast_nonneg n) (Real.sqrt_nonneg _)
    _ = (n : ℝ) ^ 2 * Real.sqrt (k : ℝ) / (k : ℝ) := by
          rw [div_eq_mul_inv]
          ring

/-- For positive `k`, the quotient √k / k equals k^(-1/2). -/
theorem sqrt_div_eq_rpow_neg_half (k : ℝ) (hk : 0 < k) :
    Real.sqrt k / k = k ^ (-(1 / 2) : ℝ) := by
  rw [Real.sqrt_eq_rpow, div_eq_mul_inv, ← Real.rpow_neg_one, ← Real.rpow_add hk]
  norm_num

/-- For positive natural `k`, the finite update-cost sum is bounded by `quantumUpdateWork n k`
[Heiligman2003]. -/
theorem quantum_update_sum_le_work (n k : ℕ) (hk : 0 < k) :
    (∑ h ∈ Finset.range (n / k), ((n - k * h : ℕ) : ℝ) * Real.sqrt (k : ℝ))
      ≤ quantumUpdateWork (n : ℝ) (k : ℝ) := by
  have hkR : (0 : ℝ) < (k : ℝ) := by exact_mod_cast hk
  calc
    (∑ h ∈ Finset.range (n / k), ((n - k * h : ℕ) : ℝ) * Real.sqrt (k : ℝ))
        ≤ (n : ℝ) ^ 2 * Real.sqrt (k : ℝ) / (k : ℝ) := quantum_update_sum_le n k hk
    _ = (n : ℝ) ^ 2 * (Real.sqrt (k : ℝ) / (k : ℝ)) := by ring
    _ = (n : ℝ) ^ 2 * (k : ℝ) ^ (-(1 / 2) : ℝ) := by
          rw [sqrt_div_eq_rpow_neg_half (k : ℝ) hkR]
    _ = quantumUpdateWork (n : ℝ) (k : ℝ) := by
          unfold quantumUpdateWork
          rw [Real.rpow_two]
          ring

end Qatlib.Papers.LowWeightPath03.MainResults.PeriodicDijkstra
