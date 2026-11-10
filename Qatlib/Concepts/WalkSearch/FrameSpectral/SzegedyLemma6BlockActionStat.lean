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

open Qatlib.Concepts.SpectralFilter.BusySpectrum

namespace Qatlib.Concepts.WalkSearch.FrameSpectral

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
