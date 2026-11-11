/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.SearchStopping.KnownCount.Corollary22Stat

/-!
# Complex quadratic identity for diffusion amplitudes

`corollary2_2_complex` proves preservation of k² + (N − 1)l² by the complex two-amplitude
diffusion update for N > 0. This is an algebraic identity involving complex squares.

For the mathematical background, see [Grover1997].

## Main statements

* `corollary2_2_complex`: For positive N, the complex diffusion update preserves the quadratic
  expression k² + (N − 1)l².

## References

* [Grover, 1997][Grover1997]
-/

namespace Qatlib.Concepts.SearchStopping.KnownCount

/-- For positive N, the complex diffusion update preserves the quadratic expression k² + (N −
1)l². See [Grover1997]. -/
theorem corollary2_2_complex : Corollary2_2 := by
  intro N hN k l
  have hn : (N : ℂ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hN)
  unfold distinguishedAfterC ordinaryAfterC
  field_simp
  ring

end Qatlib.Concepts.SearchStopping.KnownCount
