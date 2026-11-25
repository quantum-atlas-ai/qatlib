/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Concepts.SdpDuality.StrongDuality.SdpDuality

@[expose] public section

/-!
# Interior radius of the Choi dual program

Gives the interior ball of the represented Choi dual space with the radius from
[Watrous2013], Section 4.

## References

* [Watrous, 2013][Watrous2013]
-/

set_option autoImplicit false

open Qatlib.Concepts.SdpDuality.StrongDuality
open Qatlib.Concepts.SdpDuality.StrongDuality.Program
open Qatlib.Foundations.PureStateMath

namespace Qatlib.Papers.BddNormSDP12.MainResults

/-- In positive output dimension `E`, the Choi dual center in the represented space admits the radius
`(2 * E)⁻¹` of [Watrous2013], Section 4. -/
theorem choi_dual_center_interior_ball {D E : ℕ} (hE : 0 < E)
    (T : Operator D →ₗ[ℂ] Operator E) :
    (diamondProgram T).DualInteriorBall (diamondDualCenter T) (2 * (E : ℝ))⁻¹ := by
  simpa only [diamondInteriorRadius_eq_of_pos hE] using diamondDualCenter_interior_ball T

end Qatlib.Papers.BddNormSDP12.MainResults
