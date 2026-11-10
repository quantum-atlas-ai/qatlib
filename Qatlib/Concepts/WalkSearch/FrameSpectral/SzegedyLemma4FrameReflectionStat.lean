/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Foundations.PureStateMath.Reflection.ReflectionLaws
import Qatlib.Foundations.PureStateMath.Qubit
import Qatlib.Concepts.WalkSearch.FrameSpectral.SzegedyLemma4FrameReflectionDefs
import Qatlib.Foundations.InstrumentCore.ProjectiveMeasurement
set_option backward.isDefEq.respectTransparency false
set_option warningAsError false
open Qatlib.Foundations.InstrumentCore.ProjectiveMeasurement
open Qatlib.Foundations.PureStateMath.Reflection
open Qatlib.Foundations.PureStateMath

open Matrix

namespace Qatlib.Concepts.WalkSearch.FrameSpectral

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
