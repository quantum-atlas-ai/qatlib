/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.GradientOracle.DifferenceError.CentralDifferenceOneDimErrorStat

/-!
# Directional central-difference error specification

`CentralDifferenceDirectionalError` states a multivariate central-difference remainder estimate
along a nonzero vector. It bounds the highest derivative on the sampled line segment after
normalizing the direction, and compares `centralDiffApply` with the Fréchet derivative at zero.
See [GilyenArunachalamWiebe2019] for background.

## Main statements

* `CentralDifferenceDirectionalError`: The proposition that a bound `B` on the normalized `(2 *
  m + 1)`st directional derivative gives error at most `B * exp (-(1 / 2) * m) * ‖x‖ ^ (2 * m +
  1)` for a nonzero direction.

## References

* [Gilyen, Arunachalam, and Wiebe, 2019][GilyenArunachalamWiebe2019]
-/

open Qatlib.Concepts.GradientOracle.CentralDiff

namespace Qatlib.Concepts.GradientOracle.DifferenceError

/-- The proposition that a bound `B` on the normalized `(2 * m + 1)`st directional derivative
gives error at most `B * exp (-(1 / 2) * m) * ‖x‖ ^ (2 * m + 1)` for a nonzero direction. -/
def CentralDifferenceDirectionalError : Prop :=
  ∀ (d m : ℕ), 0 < m → ∀ (B : ℝ),
    ∀ (f : EuclideanSpace ℝ (Fin d) → ℝ), ContDiff ℝ (2 * m + 1) f →
    ∀ x : EuclideanSpace ℝ (Fin d), x ≠ 0 →
    (∀ τ ∈ Set.Icc (-(m : ℝ)) (m : ℝ),
        |iteratedFDeriv ℝ (2 * m + 1) f (τ • x)
          (fun _ : Fin (2 * m + 1) => (‖x‖⁻¹ : ℝ) • x)| ≤ B) →
    |centralDiffApply m f x - (fderiv ℝ f 0) x| ≤
      B * Real.exp (-(1 / 2 : ℝ) * (m : ℝ)) * ‖x‖ ^ (2 * m + 1)

end Qatlib.Concepts.GradientOracle.DifferenceError
