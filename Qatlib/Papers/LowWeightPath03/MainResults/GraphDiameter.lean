/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.LowWeightPath03.MainResults.PeriodicDijkstra

/-!
# Quantum graph-diameter work scaling

This module defines the graph-diameter work expression by multiplying the optimized periodic
quantum Dijkstra work by `Real.sqrt n`. It proves the exact `n ^ (9 / 4 : ℝ)` expression for
positive size, its asymptotic upper bound, and a comparison with cubic classical work, as in
[Heiligman2003].

## Main statements

* `diameter_quantum_work_eq`: Identifies the quantum work expression with `n ^ (9 / 4 : ℝ)`.
* `diameter_work_isBigO`: Establishes the corresponding bound as `n` tends to positive infinity.
* `diameter_quantum_beats_classical`: Compares quantum and classical work for `n > 1`.

## References

* [Heiligman, 2003][Heiligman2003]
-/

set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false
noncomputable section

open Filter

namespace Qatlib.Papers.LowWeightPath03.MainResults.GraphDiameter

open Qatlib.Papers.LowWeightPath03.MainResults.PeriodicDijkstra

/-- The graph-diameter quantum work expression `Real.sqrt n * quantumDijkstraWork n (Real.sqrt
n)`. -/
def diameterQuantumWork (n : ℝ) : ℝ :=
  Real.sqrt n * quantumDijkstraWork n (Real.sqrt n)

/-- The graph-diameter classical work comparison expression `n ^ (3 : ℝ)`. -/
def diameterClassicalWork (n : ℝ) : ℝ := n ^ (3 : ℝ)

/-- For positive `n`, the graph-diameter quantum work expression equals `n ^ (9 / 4 : ℝ)`
[Heiligman2003]. -/
theorem diameter_quantum_work_eq (n : ℝ) (hn : 0 < n) :
    diameterQuantumWork n = n ^ (9 / 4 : ℝ) := by
  unfold diameterQuantumWork
  rw [quantumDijkstraWork_at_sqrt n hn, Real.sqrt_eq_rpow, ← Real.rpow_add hn]
  congr 1
  norm_num

/-- The graph-diameter quantum work expression is `O(n ^ (9 / 4 : ℝ))` as the real size
parameter tends to positive infinity [Heiligman2003]. -/
theorem diameter_work_isBigO :
    Asymptotics.IsBigO Filter.atTop
      (fun n : ℝ => diameterQuantumWork n)
      (fun n : ℝ => n ^ (9 / 4 : ℝ)) := by
  refine Asymptotics.IsBigO.of_bound 1 ?_
  filter_upwards [Filter.eventually_gt_atTop (0 : ℝ)] with n hn
  rw [diameter_quantum_work_eq n hn]
  simp [Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg hn.le _)]

/-- For `n > 1`, the graph-diameter quantum work expression is strictly smaller than the cubic
classical work expression [Heiligman2003]. -/
theorem diameter_quantum_beats_classical (n : ℝ) (hn : 1 < n) :
    diameterQuantumWork n < diameterClassicalWork n := by
  have hn0 : 0 < n := lt_trans zero_lt_one hn
  rw [diameter_quantum_work_eq n hn0, diameterClassicalWork]
  exact Real.rpow_lt_rpow_of_exponent_lt hn (by norm_num : (9 / 4 : ℝ) < 3)

end Qatlib.Papers.LowWeightPath03.MainResults.GraphDiameter
