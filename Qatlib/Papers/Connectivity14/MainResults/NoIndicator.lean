/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Analysis.Asymptotics.Theta
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Qatlib.Papers.Connectivity14.MainResults.SimplexComplete

/-!
# Runtime scales incompatible with a decreasing indicator

This module compares the scalar runtime scales `sqrt M` and `M * sqrt M` associated with the
connectivity examples in [MeyerWong2015]. It proves their strict asymptotic separation and rules
out an antitone real function taking the specified values at `1` and at any `M > 1`.

## Main statements

* `sqrt_littleO_mul_sqrt`: The square-root scale is little-o of the three-halves scale.
* `higher_connectivity_slower_runtime`: The specified runtime values contradict an antitone
  indicator.

## References

* [Meyer and Wong, 2015][MeyerWong2015]
-/

set_option warningAsError false

set_option autoImplicit false
noncomputable section

open Qatlib.Foundations.PureStateMath
open scoped Matrix Matrix.Norms.L2Operator

namespace Qatlib.Papers.Connectivity14.MainResults

/-- As `M` tends to infinity, `sqrt M` is little-o of `M * sqrt M`, separating the runtime
scales used in the examples of [MeyerWong2015]. -/
theorem sqrt_littleO_mul_sqrt :
    Asymptotics.IsLittleO Filter.atTop (fun M : ℝ => Real.sqrt M)
      (fun M : ℝ => M * Real.sqrt M) := by
  refine Asymptotics.IsLittleO.of_bound ?_
  intro c hc
  have hMc_one : c * (1 / c) = 1 := by
    field_simp
  filter_upwards [Filter.eventually_ge_atTop (1 / c)] with M hM
  have hMc : 1 ≤ c * M := by
    have h := mul_le_mul_of_nonneg_left hM (le_of_lt hc)
    rwa [hMc_one] at h
  have hMpos : 0 < M := by
    have hcpos : 0 < 1 / c := by positivity
    linarith
  have hMn : (0 : ℝ) ≤ Real.sqrt M := Real.sqrt_nonneg M
  have hgn : (0 : ℝ) ≤ M * Real.sqrt M := by positivity
  rw [Real.norm_of_nonneg hMn, Real.norm_of_nonneg hgn]
  calc Real.sqrt M = 1 * Real.sqrt M := (one_mul _).symm
    _ ≤ (c * M) * Real.sqrt M := mul_le_mul_of_nonneg_right hMc hMn
    _ = c * (M * Real.sqrt M) := by ring

/-- For `M > 1`, no antitone function `I : ℝ → ℝ` can satisfy both `I 1 = sqrt M` and `I M = M *
sqrt M`. This is a scalar obstruction to a decreasing runtime indicator in the comparison of
[MeyerWong2015]. -/
theorem higher_connectivity_slower_runtime
    (I : ℝ → ℝ) (hmono : ∀ a b : ℝ, a ≤ b → I b ≤ I a)
    (M : ℝ) (hM : 1 < M)
    (hjoin : I 1 = Real.sqrt M)
    (hslow : I M = M * Real.sqrt M) :
    False := by
  have hle : I M ≤ I 1 := hmono 1 M (le_of_lt hM)
  rw [hslow, hjoin] at hle
  have hsp : 0 < Real.sqrt M := Real.sqrt_pos.2 (by linarith)
  have hstrict : Real.sqrt M < M * Real.sqrt M := by nlinarith
  linarith

end Qatlib.Papers.Connectivity14.MainResults
