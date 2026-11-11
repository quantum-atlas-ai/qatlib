/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.GradientOracle.CentralDiff.CentralDifferenceExactnessStat

/-!
# The legacy central-difference error contract

`CentralDifferenceOneDimErrorLegacy` records the original remainder statement with an
unrestricted real step. Its derivative bound uses the ordered interval from `-m * δ` to `m * δ`,
which is empty for negative step and positive order; this explains the failure proved by
`not_centralDifferenceOneDimError` in the error proof module. See [GilyenArunachalamWiebe2019]
for background.

## Main statements

* `CentralDifferenceOneDimErrorLegacy`: The legacy central-difference error proposition with
  unrestricted real step and a highest-derivative bound on the ordered sample interval.

## References

* [Gilyen, Arunachalam, and Wiebe, 2019][GilyenArunachalamWiebe2019]
-/

open Qatlib.Concepts.GradientOracle.CentralDiff

set_option autoImplicit false
namespace Qatlib.Concepts.GradientOracle.DifferenceError
/-- The legacy central-difference error proposition with unrestricted real step and a
highest-derivative bound on the ordered sample interval. -/
def CentralDifferenceOneDimErrorLegacy : Prop :=
  ∀ (m : ℕ), 0 < m → ∀ (δ B : ℝ),
    ∀ (f : ℝ → ℝ), ContDiff ℝ (2 * m + 1) f →
    (∀ ξ ∈ Set.Icc (-(m : ℝ) * δ) ((m : ℝ) * δ),
        |iteratedDeriv (2 * m + 1) f ξ| ≤ B) →
    |(deriv f 0) * δ -
        ∑ ℓ ∈ Finset.Ico (-(m : ℤ)) ((m : ℤ) + 1),
          centralDiffCoeff m ℓ * f ((ℓ : ℝ) * δ)| ≤
      Real.exp (-(1 / 2 : ℝ) * (m : ℝ)) * B * |δ| ^ (2 * m + 1)

end Qatlib.Concepts.GradientOracle.DifferenceError
