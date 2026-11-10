/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.SpectralFilter.BusySpectrum.BipartiteDiscriminantSpectrum
import Qatlib.Concepts.WalkSearch.FrameSpectral.SzegedyLemma7EigenSymmetryDefs
set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

open Matrix

open Qatlib.Foundations.PureStateMath

open Qatlib.Concepts.SpectralFilter.BusySpectrum

namespace Qatlib.Concepts.WalkSearch.FrameSpectral

def SzegedyLemma7EigenSymmetry : Prop :=
  ∀ (H I J : Type) [Fintype H] [DecidableEq H] [Fintype I] [DecidableEq I]
      [Fintype J] [DecidableEq J] (A : Matrix H I ℂ) (B : Matrix H J ℂ)
      (v : QState (I ⊕ J)) (lam : ℝ),
    bipartiteDiscriminant A B *ᵥ v = (lam : ℂ) • v →
    bipartiteDiscriminant A B *ᵥ paperSourceFlip v = (-(lam : ℂ)) • paperSourceFlip v

end Qatlib.Concepts.WalkSearch.FrameSpectral
