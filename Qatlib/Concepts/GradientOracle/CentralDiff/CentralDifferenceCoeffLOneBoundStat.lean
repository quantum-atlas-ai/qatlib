/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.GradientOracle.CentralDiff.CentralDifferenceExactnessStat

/-!
# Central-difference coefficient mass specification

`CentralDifferenceCoeffLOneBound` packages the logarithmic bound on the one-sided sum of
absolute central-difference coefficients. It sums the coefficients indexed from zero through the
positive order `m`. See [GilyenArunachalamWiebe2019] for background.

## Main statements

* `CentralDifferenceCoeffLOneBound`: The proposition that the absolute coefficient sum over
  indices zero through `m` is at most `Real.log m + 1` for every positive `m`.

## References

* [Gilyen, Arunachalam, and Wiebe, 2019][GilyenArunachalamWiebe2019]
-/

namespace Qatlib.Concepts.GradientOracle.CentralDiff

/-- The proposition that the absolute coefficient sum over indices zero through `m` is at most
`Real.log m + 1` for every positive `m`. -/
def CentralDifferenceCoeffLOneBound : Prop :=
  ∀ m : ℕ, 0 < m →
    ∑ ℓ ∈ Finset.Ico (0 : ℤ) ((m : ℤ) + 1), |centralDiffCoeff m ℓ| ≤ Real.log m + 1

end Qatlib.Concepts.GradientOracle.CentralDiff
