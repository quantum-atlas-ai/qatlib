/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Papers.AdiabaticEvol00.MainResults.Ring2SAT

@[expose] public section

/-!
# Unconstrained minimum of the local ring block gap

The local block energies in Eq. (4.19) differ by twice the square root of a quadratic.
The cosine lies in the interval [-1, 1], so its quadratic coefficient is positive for
all angles. Completing the square gives a bound for every real interpolation parameter.
-/

set_option autoImplicit false

open Qatlib.Papers.AdiabaticEvol00.MainResults.Ring2SAT

namespace Qatlib.Papers.AdiabaticEvol00.MainResults

/-- The quadratic radicand is bounded below by its vertex for every angle and parameter. -/
theorem ringRadicand_vertex_le_all (θ s : ℝ) :
    ringRadicand θ ((6 - 2 * (1 - Real.cos θ)) / (9 - 4 * (1 - Real.cos θ))) ≤
      ringRadicand θ s := by
  rw [ringRadicand_vertex, ringRadicand_complete_square θ s]
  have hA : 0 ≤ 9 - 4 * (1 - Real.cos θ) := by linarith [Real.neg_one_le_cos θ]
  exact le_add_of_nonneg_left (mul_nonneg hA (sq_nonneg _))

/-- The minimum local ring gap from Eq. (4.19), with no sign restriction on the angle cosine. -/
theorem ringBlockGap_min_all (θ s : ℝ) :
    2 * Real.sqrt (4 * Real.sin θ ^ 2 / (5 + 4 * Real.cos θ)) ≤
      ringEnergyPlus θ s - ringEnergyMinus θ s := by
  rw [ringEnergy_gap]
  have hv := ringRadicand_vertex_le_all θ s
  rw [ringRadicand_vertex, ringRadicand_vertex_sin] at hv
  exact mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hv) two_pos.le

end Qatlib.Papers.AdiabaticEvol00.MainResults
