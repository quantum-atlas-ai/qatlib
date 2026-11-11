/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Foundations.PureStateMath.Reflection.Basic

/-!
# Complex two-amplitude diffusion update

`distinguishedAfterC` and `ordinaryAfterC` define the complex amplitude update for one
distinguished coordinate in dimension N. `Theorem2` states that these formulas agree with
applying the diffusion matrix to the associated marked vector.

For the mathematical background, see [Grover1997].

## Main statements

* `Theorem2`: The proposition that applying diffusion to a singleton-marked complex vector
  produces the two amplitudes specified by `distinguishedAfterC` and `ordinaryAfterC`.

## References

* [Grover, 1997][Grover1997]
-/

open Qatlib.Foundations.PureStateMath.Reflection
open Qatlib.Foundations.PureStateMath

namespace Qatlib.Concepts.SearchStopping.KnownCount

/-- The distinguished complex amplitude (2/N − 1)k + 2(N − 1)l/N after diffusion. -/
noncomputable def distinguishedAfterC (N : ℕ) (k l : ℂ) : ℂ :=
  (2 / (N : ℂ) - 1) * k + 2 * ((N : ℂ) - 1) / N * l

/-- The ordinary complex amplitude 2k/N + (N − 2)l/N after diffusion. -/
noncomputable def ordinaryAfterC (N : ℕ) (k l : ℂ) : ℂ :=
  2 / (N : ℂ) * k + ((N : ℂ) - 2) / N * l

/-- The proposition that applying diffusion to a singleton-marked complex vector produces the
two amplitudes specified by `distinguishedAfterC` and `ordinaryAfterC`. -/
def Theorem2 : Prop :=
  ∀ (I : Type) [Fintype I] [DecidableEq I] (w : I) (k l : ℂ),
    ApplyGate (Diffusion I) (MarkedVector {w} k l) =
      MarkedVector {w} (distinguishedAfterC (Fintype.card I) k l)
        (ordinaryAfterC (Fintype.card I) k l)

end Qatlib.Concepts.SearchStopping.KnownCount
