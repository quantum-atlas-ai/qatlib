/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Foundations.PureStateMath.Reflection.ReflectionLaws
import Qatlib.Foundations.PureStateMath.Qubit
set_option backward.isDefEq.respectTransparency false
set_option warningAsError false
open Qatlib.Foundations.PureStateMath

open Matrix

namespace Qatlib.Concepts.WalkSearch.FrameSpectral

noncomputable def paperFrameProjection {H ι : Type} [Fintype H] [DecidableEq H]
    [Fintype ι] [DecidableEq ι] (v : ι → QState H) : Matrix H H ℂ :=
  Matrix.of fun x y => ∑ i, v i x * (starRingEnd ℂ) (v i y)
end Qatlib.Concepts.WalkSearch.FrameSpectral
