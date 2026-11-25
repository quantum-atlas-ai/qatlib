/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Papers.AndersonLoc09.MainResults.Asymptotics
public import Mathlib.Analysis.Asymptotics.Theta

@[expose] public section

/-!
# Scale of the critical coupling

Equation (7) writes the modeled critical coupling as a fixed positive
coefficient times the inverse eighth power of the system size.
-/

set_option autoImplicit false

namespace Qatlib.Papers.AndersonLoc09.MainResults

open Qatlib.Papers.AndersonLoc09.MainResults

/-- At a fixed positive fourth-order coefficient, the modeled critical coupling
is of order `N⁻¹ᐟ⁸`. -/
theorem lambdaStar_rate (f2 : ℝ) (hf2 : 0 < f2) :
    Asymptotics.IsTheta Filter.atTop (fun N : ℝ => lambdaStar N f2)
      (fun N : ℝ => Real.rpow N (-(1 / 8))) := by
  have hc : Real.sqrt 2 * Real.rpow f2 (-(1 / 4)) ≠ 0 :=
    ne_of_gt (mul_pos (Real.sqrt_pos.2 (by norm_num)) (Real.rpow_pos_of_pos hf2 _))
  simpa only [lambdaStar] using
    (Asymptotics.isTheta_refl (fun N : ℝ => Real.rpow N (-(1 / 8))) Filter.atTop).const_mul_left hc

end Qatlib.Papers.AndersonLoc09.MainResults
