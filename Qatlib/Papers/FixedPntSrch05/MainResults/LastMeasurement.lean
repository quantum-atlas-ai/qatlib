/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Papers.FixedPntSrch05.MainResults.DeterministicProbability
public import Qatlib.Papers.FixedPntSrch05.MainResults.ErrorScaling

@[expose] public section

/-!
# The success contribution of the final register measurement

The discussion following Eq. (8) separates deterministic success on
earlier measurements from the remaining contribution of the last
measurement. Subtracting the former from total success gives the latter.
-/

set_option autoImplicit false

open Qatlib.Papers.FixedPntSrch05.MainResults.ErrorScaling
open Qatlib.Papers.FixedPntSrch05.MainResults.DeterministicProbability

namespace Qatlib.Papers.FixedPntSrch05.MainResults

/-- The unconditional contribution of the last register measurement is
the difference between total success and earlier deterministic success. -/
theorem probabilistic_success_eq (ε : ℝ) (hε0 : 0 ≤ ε) (hε1 : ε < 1)
    (q : ℕ) (hq : 1 ≤ q) :
    (1 - fixedPointError ε q) - deterministicProbability ε q =
      ε ^ (2 * q - 2) * (1 + ε - 2 * ε ^ 3) / 2 := by
  rw [fixedPointError_eq_pow, deterministic_probability_eq ε hε0 hε1 q hq,
    show 2 * q + 1 = (2 * q - 2) + 3 by omega, pow_add]
  ring

end Qatlib.Papers.FixedPntSrch05.MainResults
