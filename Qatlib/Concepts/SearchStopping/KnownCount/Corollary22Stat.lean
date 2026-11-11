/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.SearchStopping.KnownCount.Theorem2Stat

/-!
# Complex diffusion quadratic preservation contract

`Corollary2_2` states that the complex diffusion update preserves the quadratic polynomial k² +
(N − 1)l² in positive dimension. The expression uses complex squares rather than absolute
squares.

For the mathematical background, see [Grover1997].

## Main statements

* `Corollary2_2`: The proposition that the complex diffusion update preserves k² + (N − 1)l² for
  positive N.

## References

* [Grover, 1997][Grover1997]
-/

namespace Qatlib.Concepts.SearchStopping.KnownCount

/-- The proposition that the complex diffusion update preserves k² + (N − 1)l² for positive N. -/
def Corollary2_2 : Prop :=
  ∀ (N : ℕ), 0 < N → ∀ (k l : ℂ),
    (distinguishedAfterC N k l) ^ 2 + ((N : ℂ) - 1) * (ordinaryAfterC N k l) ^ 2 =
      k ^ 2 + ((N : ℂ) - 1) * l ^ 2

end Qatlib.Concepts.SearchStopping.KnownCount
