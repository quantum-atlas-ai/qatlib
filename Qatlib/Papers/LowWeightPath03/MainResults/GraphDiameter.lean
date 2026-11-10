/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.LowWeightPath03.MainResults.PeriodicDijkstra
set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false
noncomputable section

open Filter

namespace Qatlib.Papers.LowWeightPath03.MainResults.GraphDiameter

open Qatlib.Papers.LowWeightPath03.MainResults.PeriodicDijkstra

def diameterQuantumWork (n : ℝ) : ℝ :=
  Real.sqrt n * quantumDijkstraWork n (Real.sqrt n)

def diameterClassicalWork (n : ℝ) : ℝ := n ^ (3 : ℝ)

theorem diameter_quantum_work_eq (n : ℝ) (hn : 0 < n) :
    diameterQuantumWork n = n ^ (9 / 4 : ℝ) := by
  unfold diameterQuantumWork
  rw [quantumDijkstraWork_at_sqrt n hn, Real.sqrt_eq_rpow, ← Real.rpow_add hn]
  congr 1
  norm_num

theorem diameter_work_isBigO :
    Asymptotics.IsBigO Filter.atTop
      (fun n : ℝ => diameterQuantumWork n)
      (fun n : ℝ => n ^ (9 / 4 : ℝ)) := by
  refine Asymptotics.IsBigO.of_bound 1 ?_
  filter_upwards [Filter.eventually_gt_atTop (0 : ℝ)] with n hn
  rw [diameter_quantum_work_eq n hn]
  simp [Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg hn.le _)]

theorem diameter_quantum_beats_classical (n : ℝ) (hn : 1 < n) :
    diameterQuantumWork n < diameterClassicalWork n := by
  have hn0 : 0 < n := lt_trans zero_lt_one hn
  rw [diameter_quantum_work_eq n hn0, diameterClassicalWork]
  exact Real.rpow_lt_rpow_of_exponent_lt hn (by norm_num : (9 / 4 : ℝ) < 3)

end Qatlib.Papers.LowWeightPath03.MainResults.GraphDiameter
