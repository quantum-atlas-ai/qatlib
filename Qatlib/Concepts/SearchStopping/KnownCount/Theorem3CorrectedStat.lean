/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.SearchStopping.KnownCount.Corollary22RealRestrictedStat

/-!
# Corrected amplitude growth contract

`Theorem3Corrected` specifies the growth and positivity estimate for normalized real
two-amplitude data. The dimension threshold N ≥ 8 and the normalization equation are explicit
hypotheses.

For the mathematical background, see [Grover1997].

## Main statements

* `Theorem3Corrected`: The proposition that N ≥ 8, positive normalized amplitudes, and k < 1/√2
  imply `distinguishedAfter N (-k) l - k > 1/(2√N)` and `ordinaryAfter N (-k) l > 0`.

## References

* [Grover, 1997][Grover1997]
-/

namespace Qatlib.Concepts.SearchStopping.KnownCount

/-- The proposition that N ≥ 8, positive normalized amplitudes, and k < 1/√2 imply
`distinguishedAfter N (-k) l - k > 1/(2√N)` and `ordinaryAfter N (-k) l > 0`. -/
def Theorem3Corrected : Prop :=
  ∀ (N : ℕ), 8 ≤ N → ∀ (k l : ℝ),
    0 < k → k < 1 / Real.sqrt 2 → 0 < l → twoAmplitudeMass N k l = 1 →
      1 / (2 * Real.sqrt (N : ℝ)) < distinguishedAfter N (-k) l - k ∧
      0 < ordinaryAfter N (-k) l

end Qatlib.Concepts.SearchStopping.KnownCount
