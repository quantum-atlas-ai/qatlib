/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.SpectralSketch.SpectrumPerturb.OrderedSpectralPerturbation
import Mathlib.Analysis.Normed.Algebra.MatrixExponential

/-!
# Statement of Gibbs trace perturbation

`GibbsTracePerturbation` specifies the stability of a Hermitian matrix's exponential trace under
operator-norm perturbations. It bounds the absolute change by the original trace times `exp ‖Ht
- H‖ - 1`, providing the partition-function perturbation estimate of [ChiaEtAl2022].

## Main statements

* `GibbsTracePerturbation`: The proposition that the absolute change in the real exponential
  trace between Hermitian matrices `H` and `Ht` is at most `(exp ‖Ht - H‖ - 1) * Re (trace (exp
  H))`.

## References

* [Chia et al., 2022][ChiaEtAl2022]
-/

set_option warningAsError false

namespace Qatlib.Concepts.SketchSpectral.MatrixFunctions

open Matrix NormedSpace
open scoped Matrix.Norms.L2Operator

/-- The proposition that the absolute change in the real exponential trace between Hermitian
matrices `H` and `Ht` is at most `(exp ‖Ht - H‖ - 1) * Re (trace (exp H))`. -/
def GibbsTracePerturbation : Prop :=
  ∀ (I : Type) [Fintype I] [DecidableEq I] (H Ht : Matrix I I ℂ)
    (hH : H.IsHermitian) (hHt : Ht.IsHermitian),
    |(Matrix.trace (exp Ht)).re - (Matrix.trace (exp H)).re| ≤
      (Real.exp ‖Ht - H‖ - 1)*(Matrix.trace (exp H)).re

end Qatlib.Concepts.SketchSpectral.MatrixFunctions
