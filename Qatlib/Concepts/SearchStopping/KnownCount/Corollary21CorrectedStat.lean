/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.SearchStopping.KnownCount.Corollary22RealRestrictedStat

/-!
# Corrected diffusion positivity contract

`Corollary2_1Corrected` records sufficient conditions for positivity of both real amplitudes
after diffusion. Its dimension threshold N ≥ 8 is included explicitly.

For the mathematical background, see [Grover1997].

## Main statements

* `Corollary2_1Corrected`: The proposition that N ≥ 8, k < 0 < l, and |k/l| < √N imply
  positivity of both real diffusion updates.

## References

* [Grover, 1997][Grover1997]
-/

namespace Qatlib.Concepts.SearchStopping.KnownCount

/-- The proposition that N ≥ 8, k < 0 < l, and |k/l| < √N imply positivity of both real
diffusion updates. -/
def Corollary2_1Corrected : Prop :=
  ∀ (N : ℕ), 8 ≤ N → ∀ (k l : ℝ), k < 0 → 0 < l →
    |k / l| < Real.sqrt N →
      0 < distinguishedAfter N k l ∧ 0 < ordinaryAfter N k l

end Qatlib.Concepts.SearchStopping.KnownCount
