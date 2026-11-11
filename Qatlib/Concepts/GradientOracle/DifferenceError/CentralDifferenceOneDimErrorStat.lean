/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.GradientOracle.CentralDiff.CentralDifferenceExactnessStat

/-!
# One-dimensional central-difference error specification

`CentralDifferenceOneDimError` states the high-order central-difference remainder bound for
nonnegative step sizes. The derivative of order `2 * m + 1` is bounded on the full ordered
interval containing the sample points. See [GilyenArunachalamWiebe2019] for background.

## Main statements

* `CentralDifferenceOneDimError`: The proposition that, for `δ ≥ 0` and positive `m`, a bound
  `B` on the `(2 * m + 1)`st derivative over the sample interval gives error at most `exp (-(1 /
  2) * m) * B * |δ| ^ (2 * m + 1)`.

## References

* [Gilyen, Arunachalam, and Wiebe, 2019][GilyenArunachalamWiebe2019]
-/

open Qatlib.Concepts.GradientOracle.CentralDiff

namespace Qatlib.Concepts.GradientOracle.DifferenceError

/-- The proposition that, for `δ ≥ 0` and positive `m`, a bound `B` on the `(2 * m + 1)`st
derivative over the sample interval gives error at most `exp (-(1 / 2) * m) * B * |δ| ^ (2 *
m + 1)`. -/
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
