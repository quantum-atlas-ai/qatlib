/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.WalkSearch.TwoLevelLower
import Qatlib.Concepts.SpectralFilter.BusySpectrum.BipartiteDiscriminantSpectrum

/-!
# Paper frames and the quantized walk operator

The square-root frames `paperFrameA` and `paperFrameB` define the two diffusion matrices and
their product `paperMu`. The formula follows Definition 1 of [Szegedy2004]; these definitions
accept arbitrary finite real kernels, with normalization properties established separately under
suitable assumptions.

## Main statements

* `paperFrameA`: embeds square-root row weights with the first register fixed.
* `paperFrameB`: embeds square-root row weights with the second register fixed.
* `paperMu`: defines `(2R - I)(2C - I)`.

## References

* [Szegedy, 2004][Szegedy2004]
-/

set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

open Matrix

namespace Qatlib.Papers.QWalkSpectra04.WalkDefinition

/-- The square-root frame with entry `√(c i p.2)` when `p.1 = i`, and zero otherwise. -/
noncomputable def paperFrameA {I J : Type} [Fintype I] [DecidableEq I]
    [Fintype J] [DecidableEq J] (c : I → J → ℝ) : Matrix (I × J) I ℂ :=
  Matrix.of fun p i => if p.1 = i then ((Real.sqrt (c i p.2) : ℂ)) else 0

/-- The square-root frame with entry `√(r j p.1)` when `p.2 = j`, and zero otherwise. -/
noncomputable def paperFrameB {I J : Type} [Fintype I] [DecidableEq I]
    [Fintype J] [DecidableEq J] (r : J → I → ℝ) : Matrix (I × J) J ℂ :=
  Matrix.of fun p j => if p.2 = j then ((Real.sqrt (r j p.1) : ℂ)) else 0

/-- The frame product `paperFrameA c * (paperFrameA c)ᴴ` defining the paper's matrix `C`. -/
noncomputable def paperDiffusionC {I J : Type} [Fintype I] [DecidableEq I]
    [Fintype J] [DecidableEq J] (c : I → J → ℝ) : Matrix (I × J) (I × J) ℂ :=
  paperFrameA c * (paperFrameA c)ᴴ

/-- The frame product `paperFrameB r * (paperFrameB r)ᴴ` defining the paper's matrix `R`. -/
noncomputable def paperDiffusionR {I J : Type} [Fintype I] [DecidableEq I]
    [Fintype J] [DecidableEq J] (r : J → I → ℝ) : Matrix (I × J) (I × J) ℂ :=
  paperFrameB r * (paperFrameB r)ᴴ

/-- The paper's quantized walk expression `(2R - I)(2C - I)` formed from the two diffusion
matrices. -/
noncomputable def paperMu {I J : Type} [Fintype I] [DecidableEq I]
    [Fintype J] [DecidableEq J] (c : I → J → ℝ) (r : J → I → ℝ) :
    Matrix (I × J) (I × J) ℂ :=
  ((2 : ℂ) • paperDiffusionR r - 1) * ((2 : ℂ) • paperDiffusionC c - 1)
end Qatlib.Papers.QWalkSpectra04.WalkDefinition
