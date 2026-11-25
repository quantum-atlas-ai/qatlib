/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Papers.UniversalWalk08.MainResults.Parameters.RunParameters
public import Mathlib.Analysis.Asymptotics.Theta

@[expose] public section

/-!
# Logarithmic scaling of the filter count

The integer count exceeds `log(m²)` by at most one. Once the logarithm
is at least one, this gives constant-factor bounds in both directions.
-/

set_option autoImplicit false

namespace Qatlib.Papers.UniversalWalk08.MainResults

open Qatlib.Papers.UniversalWalk08.MainResults.Parameters
open Filter

/-- The rounded filter count is of the same asymptotic order as `log(m²)`. -/
theorem filter_rate :
    Asymptotics.IsTheta atTop (fun m : ℕ => (filterCount m : ℝ))
      (fun m : ℕ => Real.log ((m : ℝ) ^ 2)) := by
  have hnat : Tendsto (fun m : ℕ => (m : ℝ)) atTop atTop := tendsto_natCast_atTop_atTop
  have hsq : Tendsto (fun m : ℕ => (m : ℝ) ^ 2) atTop atTop :=
    (tendsto_pow_atTop (by decide : 2 ≠ 0)).comp hnat
  have hlog : Tendsto (fun m : ℕ => Real.log ((m : ℝ) ^ 2)) atTop atTop :=
    Real.tendsto_log_atTop.comp hsq
  have hge : ∀ᶠ m : ℕ in atTop, 1 ≤ Real.log ((m : ℝ) ^ 2) := hlog.eventually_ge_atTop 1
  constructor
  · refine Asymptotics.IsBigO.of_bound 2 ?_
    filter_upwards [eventually_ge_atTop 1, hge] with m hm hl
    have hb := (filterCount_bounds hm).2
    have hc : 0 ≤ (filterCount m : ℝ) := Nat.cast_nonneg _
    have hl0 : 0 ≤ Real.log ((m : ℝ) ^ 2) := by linarith
    rw [Real.norm_eq_abs, abs_of_nonneg hc, Real.norm_eq_abs, abs_of_nonneg hl0]
    linarith
  · refine Asymptotics.IsBigO.of_bound 1 ?_
    filter_upwards [eventually_ge_atTop 1, hge] with m hm hl
    have hc : 0 ≤ (filterCount m : ℝ) := Nat.cast_nonneg _
    have hl0 : 0 ≤ Real.log ((m : ℝ) ^ 2) := by linarith
    simpa only [Real.norm_eq_abs, abs_of_nonneg hc, abs_of_nonneg hl0, one_mul] using
      (filterCount_bounds hm).1

end Qatlib.Papers.UniversalWalk08.MainResults
