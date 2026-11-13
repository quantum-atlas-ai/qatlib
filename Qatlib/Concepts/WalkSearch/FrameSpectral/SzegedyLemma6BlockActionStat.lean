/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.SpectralFilter.BusySpectrum.BipartiteDiscriminantSpectrum

/-!
# Specification of bipartite discriminant block action

The proposition `SzegedyLemma6BlockAction` expresses the zero diagonal block structure of the
bipartite discriminant. It specifies the separate images of the left and right source components
from the image of their direct sum, without requiring the frames to be isometries. The quantum
walk spectral framework is developed in [Szegedy2004].

## Main statements

* `SzegedyLemma6BlockAction`: Separate actions on the two source summands.

## References

* [Szegedy, 2004][Szegedy2004]
-/

set_option backward.isDefEq.respectTransparency false

open Matrix

open Qatlib.Foundations.PureStateMath

open Qatlib.Concepts.SpectralFilter.BusySpectrum

namespace Qatlib.Concepts.WalkSearch.FrameSpectral

/-- The requirement that a discriminant image `(a, b) ↦ (a', b')` separates into `(a, 0) ↦ (0,
b')` and `(0, b) ↦ (a', 0)` [Szegedy, Lemma 6][Szegedy2004]. -/
def SzegedyLemma6BlockAction : Prop :=
  ∀ (H I J : Type) [Fintype H] [DecidableEq H] [Fintype I] [DecidableEq I]
      [Fintype J] [DecidableEq J] (A : Matrix H I ℂ) (B : Matrix H J ℂ)
      (a a' : QState I) (b b' : QState J),
    bipartiteDiscriminant A B *ᵥ Sum.elim a b = Sum.elim a' b' →
    bipartiteDiscriminant A B *ᵥ Sum.elim a (0 : QState J) =
      Sum.elim (0 : QState I) b' ∧
    bipartiteDiscriminant A B *ᵥ Sum.elim (0 : QState I) b =
      Sum.elim a' (0 : QState J)

end Qatlib.Concepts.WalkSearch.FrameSpectral
