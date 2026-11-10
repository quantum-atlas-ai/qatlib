/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Analysis.SpecialFunctions.Gamma.Beta
import Mathlib.Tactic
set_option autoImplicit false
noncomputable section
namespace Qatlib.Papers.RydbergMaxCut26.RatioBounds.Gamma

lemma bov_r3_gamma : (2/3:ℝ) * (Real.Gamma 2 / Real.Gamma (3/2))^2 = 8/(3*Real.pi) := by
  have hhalf : Real.Gamma (3/2) = (1/2:ℝ) * Real.sqrt Real.pi := by
    convert Real.Gamma_add_one (by norm_num : (1/2:ℝ) ≠ 0) using 1 <;>
      norm_num [Real.Gamma_one_half_eq]
  have htwo : Real.Gamma 2 = 1 := by
    convert Real.Gamma_nat_eq_factorial 1 using 1 <;> norm_num
  have hp : Real.sqrt Real.pi ≠ 0 := (Real.sqrt_pos.mpr Real.pi_pos).ne'
  rw [hhalf, htwo]
  field_simp
  nlinarith [Real.sq_sqrt Real.pi_pos.le]

end Qatlib.Papers.RydbergMaxCut26.RatioBounds.Gamma
