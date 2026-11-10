/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Analysis.Asymptotics.Theta
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Qatlib.Papers.Connectivity14.MainResults.SimplexComplete
set_option warningAsError false

set_option autoImplicit false
noncomputable section

open Qatlib.Foundations.PureStateMath
open scoped Matrix Matrix.Norms.L2Operator

namespace Qatlib.Papers.Connectivity14.MainResults

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
