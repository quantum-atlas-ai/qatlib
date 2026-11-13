/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.SpectralSketch.NearIsometry
import Qatlib.Concepts.SpectralSketch.SpectrumPerturb.OrderedSpectralPerturbation
import Mathlib.Analysis.Normed.Algebra.MatrixExponential

/-!
# Statement of the approximate eigendecomposition trace bound

`ApproximateEigendecompositionTrace` states a partition-function approximation bound from a
diagonal real spectrum and an approximately isometric reconstruction. The estimate adds the
missing-dimension contribution to `Re (trace (exp D))` and controls its error relative to `Re
(trace (exp H))`, following [ChiaEtAl2022].

## Main statements

* `ApproximateEigendecompositionTrace`: The proposition that the stated reconstruction error,
  near-isometry error, and smallness bounds give relative exponential-trace error at most `2 *
  (exp 1 - 1) * ε` for the dimension-corrected diagonal estimate.

## References

* [Chia et al., 2022][ChiaEtAl2022]
-/

set_option backward.isDefEq.respectTransparency false

namespace Qatlib.Concepts.SketchSpectral.MatrixFunctions

open Matrix NormedSpace
open scoped Matrix.Norms.L2Operator

/-- The proposition that the stated reconstruction error, near-isometry error, and smallness
bounds give relative exponential-trace error at most `2 * (exp 1 - 1) * ε` for the
dimension-corrected diagonal estimate. -/
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
