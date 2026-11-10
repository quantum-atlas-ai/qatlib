/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.WalkSearch.TwoLevelLower
import Qatlib.Concepts.SpectralFilter.BusySpectrum.BipartiteDiscriminantSpectrum
import Qatlib.Papers.QWalkSpectra04.WalkDefinition.SzegedyDefOneQuantizedWalkDefs
set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

open Qatlib.Concepts.SpectralFilter.BusySpectrum
open Qatlib.Concepts.WalkSearch.TwoLevelLower
open Matrix

namespace Qatlib.Papers.QWalkSpectra04.WalkDefinition

def SzegedyDefOneQuantizedWalk : Prop :=
  ∀ (I J : Type) [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]
      (c : I → J → ℝ) (r : J → I → ℝ),
    paperMu c r = bipartiteWalk (paperFrameA c) (paperFrameB r) ∧
    ∀ (K : Type) [Fintype K] [DecidableEq K] (P : K → K → ℝ),
      paperMu P P = SzegedyWalk P

end Qatlib.Papers.QWalkSpectra04.WalkDefinition
