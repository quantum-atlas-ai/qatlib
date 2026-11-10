/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.SpectralSketch.SpectrumPerturb.OrderedSpectralPerturbation
import Mathlib.Analysis.Normed.Algebra.MatrixExponential
set_option warningAsError false

namespace Qatlib.Concepts.SketchSpectral.MatrixFunctions

open Matrix NormedSpace
open scoped Matrix.Norms.L2Operator

def GibbsTracePerturbation : Prop :=
  ∀ (I : Type) [Fintype I] [DecidableEq I] (H Ht : Matrix I I ℂ)
    (hH : H.IsHermitian) (hHt : Ht.IsHermitian),
    |(Matrix.trace (exp Ht)).re - (Matrix.trace (exp H)).re| ≤
      (Real.exp ‖Ht - H‖ - 1)*(Matrix.trace (exp H)).re

end Qatlib.Concepts.SketchSpectral.MatrixFunctions
