/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.SpectralSketch.SpectrumPerturb.OrderedSpectralPerturbation
import Mathlib.Analysis.Normed.Algebra.MatrixExponential
set_option warningAsError false

open Qatlib.Concepts.SpectralSketch.SpectrumPerturb

namespace Qatlib.Concepts.SketchSpectral.MatrixFunctions

open Matrix NormedSpace
open scoped Matrix.Norms.L2Operator

def GibbsTraceLowerBound : Prop :=
  ∀ (I : Type) [Fintype I] [DecidableEq I] (H : Matrix I I ℂ) (hH : H.IsHermitian),
    (Qatlib.Concepts.SpectralSketch.SpectrumPerturb.spectralFrobenius H)^2 ≤ (Fintype.card I)/4 →
    ((Fintype.card I : ℝ))/2 ≤ (Matrix.trace (exp H)).re

end Qatlib.Concepts.SketchSpectral.MatrixFunctions
