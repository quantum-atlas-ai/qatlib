/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.SpectralSketch.SpectrumPerturb.OrderedSpectralPerturbation
import Mathlib.Analysis.Normed.Algebra.MatrixExponential

/-!
# Statement of the Gibbs trace lower bound

`GibbsTraceLowerBound` states that a Hermitian matrix with squared Frobenius norm at most one
quarter of its dimension has exponential trace at least half the dimension. This bound supplies
a partition-function estimate used in [ChiaEtAl2022].

## Main statements

* `GibbsTraceLowerBound`: The proposition that `spectralFrobenius H ^ 2 ≤ card I / 4` implies
  `card I / 2 ≤ Re (trace (exp H))` for every Hermitian matrix `H`.

## References

* [Chia et al., 2022][ChiaEtAl2022]
-/

set_option warningAsError false

open Qatlib.Concepts.SpectralSketch.SpectrumPerturb

namespace Qatlib.Concepts.SketchSpectral.MatrixFunctions

open Matrix NormedSpace
open scoped Matrix.Norms.L2Operator

/-- The proposition that `spectralFrobenius H ^ 2 ≤ card I / 4` implies `card I / 2 ≤ Re (trace
(exp H))` for every Hermitian matrix `H`. -/
def GibbsTraceLowerBound : Prop :=
  ∀ (I : Type) [Fintype I] [DecidableEq I] (H : Matrix I I ℂ) (hH : H.IsHermitian),
    (Qatlib.Concepts.SpectralSketch.SpectrumPerturb.spectralFrobenius H)^2 ≤ (Fintype.card I)/4 →
    ((Fintype.card I : ℝ))/2 ≤ (Matrix.trace (exp H)).re

end Qatlib.Concepts.SketchSpectral.MatrixFunctions
