/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.WalkSearch.TwoLevelLower
import Qatlib.Concepts.SpectralFilter.BusySpectrum.BipartiteDiscriminantSpectrum
set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

open Matrix

namespace Qatlib.Papers.QWalkSpectra04.WalkDefinition

noncomputable def paperFrameA {I J : Type} [Fintype I] [DecidableEq I]
    [Fintype J] [DecidableEq J] (c : I → J → ℝ) : Matrix (I × J) I ℂ :=
  Matrix.of fun p i => if p.1 = i then ((Real.sqrt (c i p.2) : ℂ)) else 0

noncomputable def paperFrameB {I J : Type} [Fintype I] [DecidableEq I]
    [Fintype J] [DecidableEq J] (r : J → I → ℝ) : Matrix (I × J) J ℂ :=
  Matrix.of fun p j => if p.2 = j then ((Real.sqrt (r j p.1) : ℂ)) else 0

noncomputable def paperDiffusionC {I J : Type} [Fintype I] [DecidableEq I]
    [Fintype J] [DecidableEq J] (c : I → J → ℝ) : Matrix (I × J) (I × J) ℂ :=
  paperFrameA c * (paperFrameA c)ᴴ

noncomputable def paperDiffusionR {I J : Type} [Fintype I] [DecidableEq I]
    [Fintype J] [DecidableEq J] (r : J → I → ℝ) : Matrix (I × J) (I × J) ℂ :=
  paperFrameB r * (paperFrameB r)ᴴ

noncomputable def paperMu {I J : Type} [Fintype I] [DecidableEq I]
    [Fintype J] [DecidableEq J] (c : I → J → ℝ) (r : J → I → ℝ) :
    Matrix (I × J) (I × J) ℂ :=
  ((2 : ℂ) • paperDiffusionR r - 1) * ((2 : ℂ) • paperDiffusionC c - 1)
end Qatlib.Papers.QWalkSpectra04.WalkDefinition
