/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.SpectralFilter.BusySpectrum.BipartiteDiscriminantSpectrum
set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

open Matrix

open Qatlib.Foundations.PureStateMath

namespace Qatlib.Concepts.WalkSearch.FrameSpectral

def paperSourceFlip {I J : Type} (v : QState (I ⊕ J)) : QState (I ⊕ J) :=
  Sum.elim (fun i => v (Sum.inl i)) (fun j => -(v (Sum.inr j)))
end Qatlib.Concepts.WalkSearch.FrameSpectral
