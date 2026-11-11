/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.WalkFind.UniqueCollision.JohnsonWalk

/-!
# Initial marked-fraction specification

`AlphaFromInput` collects the population and overlap identities for the reduced Johnson-walk
starting state. It specifies the binomial ratio for the squared marked overlap and the bounds `0
< jwAlpha ≤ 1` under the physical size assumptions [Ambainis2007ElementDistinctness].

## Main statements

* `AlphaFromInput`: the total-population and marked-overlap proposition.

## References

* [Ambainis, 2007][Ambainis2007ElementDistinctness]
-/

set_option warningAsError false
open Qatlib.Concepts.WalkFind.UniqueCollision
set_option autoImplicit false

namespace Qatlib.Concepts.WalkFind.WalkSpectrum

open Qatlib.Concepts.WalkFind.UniqueCollision

open Matrix

/-- The proposition that, for `1 ≤ k ≤ r` and `k < N-r`, the starting population and marked
overlap have the displayed formulas, `jwAlpha² = choose (N-k) (r-k) / choose N r`, and `0 <
jwAlpha ≤ 1`. -/
def AlphaFromInput : Prop :=
  ∀ (k N r : ℕ), 1 ≤ k → k ≤ r → k < N - r →
    jwStartNormSq k N r = ((Nat.choose N r) * (N - r) : ℝ) ∧
    (∑ i : Fin (2 * k + 1), star (jwGoodTilde k i) * jwStart k N r i)
      = ((Real.sqrt (jwCnt k N r k false) : ℝ) : ℂ) ∧
    (jwAlpha k N r) ^ 2 =
      ((Nat.choose (N - k) (r - k) : ℝ) / (Nat.choose N r : ℝ)) ∧
    0 < jwAlpha k N r ∧
    jwAlpha k N r ≤ 1

end Qatlib.Concepts.WalkFind.WalkSpectrum
