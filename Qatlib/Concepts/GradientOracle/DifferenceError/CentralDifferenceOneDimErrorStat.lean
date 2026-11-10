/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.GradientOracle.CentralDiff.CentralDifferenceExactnessStat
open Qatlib.Concepts.GradientOracle.CentralDiff

namespace Qatlib.Concepts.GradientOracle.DifferenceError

def CentralDifferenceOneDimError : Prop :=
  ∀ (m : ℕ), 0 < m → ∀ (δ B : ℝ), 0 ≤ δ →
    ∀ (f : ℝ → ℝ), ContDiff ℝ (2 * m + 1) f →
    (∀ ξ ∈ Set.Icc (-(m : ℝ) * δ) ((m : ℝ) * δ),
        |iteratedDeriv (2 * m + 1) f ξ| ≤ B) →
    |(deriv f 0) * δ -
        ∑ ℓ ∈ Finset.Ico (-(m : ℤ)) ((m : ℤ) + 1),
          centralDiffCoeff m ℓ * f ((ℓ : ℝ) * δ)| ≤
      Real.exp (-(1 / 2 : ℝ) * (m : ℝ)) * B * |δ| ^ (2 * m + 1)

end Qatlib.Concepts.GradientOracle.DifferenceError
