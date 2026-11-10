/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.SpectralSketch.NearIsometry
import Qatlib.Concepts.SpectralSketch.SpectrumPerturb.OrderedSpectralPerturbation
import Mathlib.Analysis.Normed.Algebra.MatrixExponential
set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

namespace Qatlib.Concepts.SketchSpectral.MatrixFunctions

open Matrix NormedSpace
open scoped Matrix.Norms.L2Operator

def ApproximateEigendecompositionTrace : Prop :=
  ∀ (I : Type) [Fintype I] [DecidableEq I]
    (H : Matrix I I ℂ) (hH : H.IsHermitian) (r : ℕ) (d : Fin r → ℝ)
    (D : Matrix (Fin r) (Fin r) ℂ) (hD : D = Matrix.diagonal (fun i => (d i : ℂ)))
    (Ut : Matrix (Fin r) I ℂ) (ε δ : ℝ),
    0 ≤ ε → ε ≤ 1/2 → δ ≤ ε/2 → δ ≤ ε/(4*(‖H‖ + ε)) →
    ‖Ut*Utᴴ - 1‖ ≤ δ →
    ‖H - Utᴴ*D*Ut‖ ≤ ε →
    |(Matrix.trace (exp D)).re + ((Fintype.card I : ℝ) - (r : ℝ)) -
      (Matrix.trace (exp H)).re| ≤
      2*(Real.exp 1 - 1)*ε*(Matrix.trace (exp H)).re

end Qatlib.Concepts.SketchSpectral.MatrixFunctions
