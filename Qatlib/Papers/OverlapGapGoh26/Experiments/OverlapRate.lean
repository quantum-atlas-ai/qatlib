/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Mathlib.Analysis.SpecialFunctions.Log.Base
public import Mathlib.Tactic.FieldSimp

@[expose] public section

/-!
# Ground-state inverse probability rate

Equation (35) of Goh and Müller (arXiv:2609.35131v1) defines the rate from
the optimized ground-state overlap. For any positive probability and system
size, the inverse transformation is precisely Eq. (34).
-/

set_option autoImplicit false

namespace Qatlib.Papers.OverlapGapGoh26.Experiments

/-- Equation (35): the base-two logarithm of the inverse overlap per site. -/
noncomputable def inverseOverlapRate (N : ℕ) (P : ℝ) : ℝ :=
  Real.logb 2 P⁻¹ / (N : ℝ)

/-- Equation (34) reconstructs the positive overlap probability from its rate. -/
theorem overlap_eq_two_rpow {N : ℕ} (hN : 0 < N) {P : ℝ} (hP : 0 < P) :
    P = (2 : ℝ) ^ (-(N : ℝ) * inverseOverlapRate N P) := by
  have hcast : (N : ℝ) ≠ 0 := ne_of_gt (Nat.cast_pos.mpr hN)
  have hexp : -(N : ℝ) * inverseOverlapRate N P = Real.logb 2 P := by
    rw [inverseOverlapRate, Real.logb_inv]
    field_simp
  rw [hexp, Real.rpow_logb (by norm_num) (by norm_num) hP]

end Qatlib.Papers.OverlapGapGoh26.Experiments
