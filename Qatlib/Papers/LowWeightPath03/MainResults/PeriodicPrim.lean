/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Nat.Cast.Order.Field
import Qatlib.Papers.LowWeightPath03.MainResults.PeriodicDijkstra
set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false
noncomputable section

open Filter
open scoped BigOperators

namespace Qatlib.Papers.LowWeightPath03.MainResults.PeriodicPrim

open Qatlib.Papers.LowWeightPath03.MainResults.PeriodicDijkstra

def quantumPrimWork (n k : ℝ) : ℝ := quantumDijkstraWork n k

def quantumPrimSearchWork (n k : ℝ) : ℝ := quantumSearchWork n k

def quantumPrimUpdateWork (n k : ℝ) : ℝ := quantumUpdateWork n k

theorem quantumPrimWork_eq_phases (n k : ℝ) :
    quantumPrimWork n k = max (quantumPrimSearchWork n k) (quantumPrimUpdateWork n k) :=
  rfl

theorem quantum_prim_optimal_work (n : ℝ) (hn : 0 < n) :
    (∀ k : ℝ, 0 < k → quantumPrimWork n (Real.sqrt n) ≤ quantumPrimWork n k) ∧
      quantumPrimWork n (Real.sqrt n) = n ^ (7 / 4 : ℝ) :=
  quantum_dijkstra_optimal_work n hn

theorem quantum_prim_balance (n k : ℝ) (hn : 0 < n) (hk : 0 < k) :
    quantumPrimSearchWork n k = quantumPrimUpdateWork n k ↔ k = Real.sqrt n :=
  quantum_dijkstra_balance n k hn hk

theorem quantum_prim_work_isBigO :
    Asymptotics.IsBigO Filter.atTop
      (fun n : ℝ => quantumPrimWork n (Real.sqrt n))
      (fun n : ℝ => n ^ (7 / 4 : ℝ)) :=
  quantum_dijkstra_work_isBigO

theorem quantum_prim_beats_classical (n : ℝ) (hn : 1 < n) :
    quantumPrimWork n (Real.sqrt n) < n ^ 2 := by
  have hn0 : 0 < n := lt_trans zero_lt_one hn
  rw [quantumPrimWork, quantumDijkstraWork_at_sqrt n hn0]
  exact quantum_beats_classical n hn

theorem quantum_prim_search_sum_le_work (n k : ℕ) (hn : 0 < n) :
    (∑ i ∈ Finset.range n, Real.sqrt ((k : ℝ) * ((n - i : ℕ) : ℝ)))
      ≤ quantumPrimSearchWork (n : ℝ) (k : ℝ) :=
  quantum_search_sum_le_work n k hn

theorem quantum_prim_update_sum_le_work (n k : ℕ) (hk : 0 < k) :
    (∑ h ∈ Finset.range (n / k), ((n - k * h : ℕ) : ℝ) * Real.sqrt (k : ℝ))
      ≤ quantumPrimUpdateWork (n : ℝ) (k : ℝ) :=
  quantum_update_sum_le_work n k hk

end Qatlib.Papers.LowWeightPath03.MainResults.PeriodicPrim
