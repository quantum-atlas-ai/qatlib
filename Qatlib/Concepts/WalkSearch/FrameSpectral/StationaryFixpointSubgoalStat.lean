/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.WalkSearch.TwoLevelLower
import Qatlib.Foundations.PureStateMath.Qubit

/-!
# Specification of reversible walk fixed states

The proposition `StationaryFixpointSubgoal` specifies normalization and invariance of embedded
reversible distributions. It quantifies over finite transition matrices and nonnegative
distributions of total mass one satisfying detailed balance. The quantum walk spectral framework
is developed in [Szegedy2004].

## Main statements

* `StationaryFixpointSubgoal`: The embedded reversible state is normalized and fixed.

## References

* [Szegedy, 2004][Szegedy2004]
-/

set_option backward.isDefEq.respectTransparency false
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.WalkSearch.TwoLevelLower

open Matrix

namespace Qatlib.Concepts.WalkSearch.FrameSpectral

/-- The requirement that every nonnegative normalized reversible distribution embeds into a
normalized fixed state of its Szegedy walk [Szegedy2004]. -/
def StationaryFixpointSubgoal : Prop :=
  ∀ (I : Type) [Fintype I] [DecidableEq I] (P : I → I → ℝ), IsTransitionMatrix P →
    ∀ (π : I → ℝ), (∀ x, 0 ≤ π x) → (∑ x, π x = 1) → IsReversible P π →
      Normalized (SzegedyEmbedState P π) ∧
      SzegedyWalk P *ᵥ SzegedyEmbedState P π = SzegedyEmbedState P π

end Qatlib.Concepts.WalkSearch.FrameSpectral
