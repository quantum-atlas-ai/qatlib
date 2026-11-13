/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Nat.Cast.Order.Field
import Qatlib.Papers.LowWeightPath03.MainResults.PeriodicDijkstra

/-!
# Periodic quantum Prim work bounds

This module expresses the periodically updated quantum Prim work model from [Heiligman2003]
through the search and update models for periodic Dijkstra. The definitions
`quantumPrimSearchWork`, `quantumPrimUpdateWork`, and `quantumPrimWork` transfer the same
balancing calculation to Prim.

At period √n the work is exactly n^(7/4), and it is minimal among positive periods. The module
also bounds the finite search and update sums and compares the optimum with n².

## Main statements

* `quantum_prim_optimal_work`: Optimality and exact work at period √n.
* `quantum_prim_balance`: Characterization of the period balancing both phases.
* `quantum_prim_beats_classical`: Strict comparison with n² for n > 1.

## References

* [Heiligman, 2003][Heiligman2003]
-/

set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false
noncomputable section

open Filter
open scoped BigOperators

namespace Qatlib.Papers.LowWeightPath03.MainResults.PeriodicPrim

open Qatlib.Papers.LowWeightPath03.MainResults.PeriodicDijkstra

/-- The periodic quantum Prim work model, defined by the periodic quantum Dijkstra work model. -/
def quantumPrimWork (n k : ℝ) : ℝ := quantumDijkstraWork n k

/-- The periodic quantum Prim search work, using `quantumSearchWork`. -/
def quantumPrimSearchWork (n k : ℝ) : ℝ := quantumSearchWork n k

/-- The periodic quantum Prim update work, using `quantumUpdateWork`. -/
def quantumPrimUpdateWork (n k : ℝ) : ℝ := quantumUpdateWork n k

/-- The quantum Prim work is the maximum of its search and update work models. -/
theorem quantumPrimWork_eq_phases (n k : ℝ) :
    quantumPrimWork n k = max (quantumPrimSearchWork n k) (quantumPrimUpdateWork n k) :=
  rfl

/-- For positive `n`, period √n minimizes the quantum Prim work among positive periods and gives
n^(7/4) [Heiligman2003]. -/
theorem quantum_prim_optimal_work (n : ℝ) (hn : 0 < n) :
    (∀ k : ℝ, 0 < k → quantumPrimWork n (Real.sqrt n) ≤ quantumPrimWork n k) ∧
      quantumPrimWork n (Real.sqrt n) = n ^ (7 / 4 : ℝ) :=
  quantum_dijkstra_optimal_work n hn

/-- For positive `n` and `k`, the quantum Prim search and update work agree exactly when k = √n
[Heiligman2003]. -/
theorem quantum_prim_balance (n k : ℝ) (hn : 0 < n) (hk : 0 < k) :
    quantumPrimSearchWork n k = quantumPrimUpdateWork n k ↔ k = Real.sqrt n :=
  quantum_dijkstra_balance n k hn hk

/-- The quantum Prim work model at period √n is O(n^(7/4)) at infinity [Heiligman2003]. -/
theorem quantum_prim_work_isBigO :
    Asymptotics.IsBigO Filter.atTop
      (fun n : ℝ => quantumPrimWork n (Real.sqrt n))
      (fun n : ℝ => n ^ (7 / 4 : ℝ)) :=
  quantum_dijkstra_work_isBigO

/-- For n > 1, the quantum Prim work at period √n is strictly less than n² [Heiligman2003]. -/
theorem quantum_prim_beats_classical (n : ℝ) (hn : 1 < n) :
    quantumPrimWork n (Real.sqrt n) < n ^ 2 := by
  have hn0 : 0 < n := lt_trans zero_lt_one hn
  rw [quantumPrimWork, quantumDijkstraWork_at_sqrt n hn0]
  exact quantum_beats_classical n hn

/-- For positive natural `n`, the finite search-cost sum is bounded by the quantum Prim search
work [Heiligman2003]. -/
theorem quantum_prim_search_sum_le_work (n k : ℕ) (hn : 0 < n) :
    (∑ i ∈ Finset.range n, Real.sqrt ((k : ℝ) * ((n - i : ℕ) : ℝ)))
      ≤ quantumPrimSearchWork (n : ℝ) (k : ℝ) :=
  quantum_search_sum_le_work n k hn

/-- For positive natural `k`, the finite update-cost sum is bounded by the quantum Prim update
work [Heiligman2003]. -/
theorem quantum_prim_update_sum_le_work (n k : ℕ) (hk : 0 < k) :
    (∑ h ∈ Finset.range (n / k), ((n - k * h : ℕ) : ℝ) * Real.sqrt (k : ℝ))
      ≤ quantumPrimUpdateWork (n : ℝ) (k : ℝ) :=
  quantum_update_sum_le_work n k hk

end Qatlib.Papers.LowWeightPath03.MainResults.PeriodicPrim
