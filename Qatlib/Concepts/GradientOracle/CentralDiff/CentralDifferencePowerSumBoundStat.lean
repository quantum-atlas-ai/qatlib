/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.GradientOracle.CentralDiff.CentralDifferenceExactnessStat

/-!
# Central-difference power-sum specification

`CentralDifferencePowerSumBound` packages the exponentially decaying absolute moment bound used
to control high-order Taylor remainders. Its exponent parameter satisfies `2 * m ≤ k` and its
symmetric coefficient sum uses the power `k + 1`. See [GilyenArunachalamWiebe2019] for
background.

## Main statements

* `CentralDifferencePowerSumBound`: The proposition that, for positive `m` and `k ≥ 2 * m`, the
  absolute coefficient-weighted `(k + 1)`st power sum is at most `6 * exp (-(7 / 6) * m) * m ^
  (k + 3 / 2)`.

## References

* [Gilyen, Arunachalam, and Wiebe, 2019][GilyenArunachalamWiebe2019]
-/

namespace Qatlib.Concepts.GradientOracle.CentralDiff

/-- The proposition that, for positive `m` and `k ≥ 2 * m`, the absolute coefficient-weighted
`(k + 1)`st power sum is at most `6 * exp (-(7 / 6) * m) * m ^ (k + 3 / 2)`. -/
def CentralDifferencePowerSumBound : Prop :=
  ∀ (m k : ℕ), 0 < m → 2 * m ≤ k →
    ∑ ℓ ∈ Finset.Ico (-(m : ℤ)) ((m : ℤ) + 1),
      |centralDiffCoeff m ℓ * ((ℓ : ℝ) ^ (k + 1))| ≤
        6 * Real.exp (-(7 / 6 : ℝ) * (m : ℝ)) * (m : ℝ) ^ ((k : ℝ) + 3 / 2)

end Qatlib.Concepts.GradientOracle.CentralDiff
