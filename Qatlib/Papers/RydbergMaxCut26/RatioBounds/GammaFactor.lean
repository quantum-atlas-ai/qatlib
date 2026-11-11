/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Analysis.SpecialFunctions.Gamma.Beta
import Mathlib.Tactic

/-!
# The rank-three Gamma prefactor

`bov_r3_gamma` evaluates the Gamma-function prefactor of the normalized Gaussian projection
kernel at rank three. The resulting constant 8/(3π) is the normalization used by the
hypergeometric rounding formula.

These results support the development of [CrostaSaubanereHuber2026].

## Main statements

* `bov_r3_gamma`: evaluates `(2/3) * (Γ(2)/Γ(3/2))^2`.

## References

* [Crosta et al., 2026][CrostaSaubanereHuber2026]
-/

set_option autoImplicit false
noncomputable section
namespace Qatlib.Papers.RydbergMaxCut26.RatioBounds.Gamma

/-- The rank-three Gamma prefactor `(2/3) * (Γ(2)/Γ(3/2))^2` equals `8/(3*π)`. -/
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
