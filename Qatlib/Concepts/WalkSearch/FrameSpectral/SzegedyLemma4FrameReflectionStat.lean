/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Foundations.PureStateMath.Reflection.ReflectionLaws
import Qatlib.Foundations.PureStateMath.Qubit
import Qatlib.Concepts.WalkSearch.FrameSpectral.SzegedyLemma4FrameReflectionDefs
import Qatlib.Foundations.InstrumentCore.ProjectiveMeasurement

/-!
# Specification of orthonormal frame reflections

The proposition `SzegedyLemma4FrameReflection` states the projection and reflection laws for an
arbitrary finite orthonormal family. The matrix `paperFrameProjection` fixes each frame vector
and annihilates every state orthogonal to the family, while its reflection acts with signs +1
and −1 on these parts. The quantum walk spectral framework is developed in [Szegedy2004].

## Main statements

* `SzegedyLemma4FrameReflection`: Orthogonal projection and reflection laws for finite frames.

## References

* [Szegedy, 2004][Szegedy2004]
-/

set_option backward.isDefEq.respectTransparency false
open Qatlib.Foundations.InstrumentCore.ProjectiveMeasurement
open Qatlib.Foundations.PureStateMath.Reflection
open Qatlib.Foundations.PureStateMath

open Matrix

namespace Qatlib.Concepts.WalkSearch.FrameSpectral

/-- The orthonormal frame projection and reflection statement: the outer product sum is an
orthogonal projector, and projection and reflection have the specified actions on frame
vectors and their orthogonal complement [Szegedy, Lemma 4][Szegedy2004]. -/
def SzegedyLemma4FrameReflection : Prop :=
  ∀ (H ι : Type) [Fintype H] [DecidableEq H] [Fintype ι] [DecidableEq ι]
      (v : ι → QState H),
    (∀ i j, Inner (v i) (v j) = if i = j then 1 else 0) →
    IsOrthogonalProjector (paperFrameProjection v) ∧
    (∀ l, paperFrameProjection v *ᵥ v l = v l) ∧
    (∀ w : QState H, (∀ l, Inner (v l) w = 0) → paperFrameProjection v *ᵥ w = 0) ∧
    (∀ l, ReflectionAbout (paperFrameProjection v) *ᵥ v l = v l) ∧
    (∀ w : QState H, (∀ l, Inner (v l) w = 0) →
      ReflectionAbout (paperFrameProjection v) *ᵥ w = -w)

end Qatlib.Concepts.WalkSearch.FrameSpectral
