/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Analysis.Calculus.Taylor
import Mathlib.Data.Int.Interval

/-!
# High-order central-difference coefficients

`centralDiffCoeff` defines the signed binomial-ratio coefficients, with coefficient zero at the
origin. `centralDiffApply` forms their weighted sum over integer multiples of a direction in a
finite-dimensional Euclidean space. See [GilyenArunachalamWiebe2019] for background.

## Main statements

* `centralDiffCoeff`: The signed central-difference coefficient defined by the binomial ratio at
  the absolute integer index, with value zero at index zero.
* `centralDiffApply`: The weighted sum of function values at the integer multiples of `y` from
  `-m` through `m`, using `centralDiffCoeff`.

## References

* [Gilyen, Arunachalam, and Wiebe, 2019][GilyenArunachalamWiebe2019]
-/

namespace Qatlib.Concepts.GradientOracle.CentralDiff
noncomputable section

/-- The signed central-difference coefficient defined by the binomial ratio at the absolute
integer index, with value zero at index zero. -/
noncomputable def centralDiffCoeff (m : ℕ) (ℓ : ℤ) : ℝ :=
  if ℓ = 0 then 0 else
    (-1 : ℝ) ^ (ℓ.natAbs - 1) / (ℓ : ℝ) *
      (Nat.choose m ℓ.natAbs : ℕ) / (Nat.choose (m + ℓ.natAbs) ℓ.natAbs : ℕ)
end
noncomputable section

/-- The weighted sum of function values at the integer multiples of `y` from `-m` through `m`,
using `centralDiffCoeff`. -/
noncomputable def centralDiffApply {d : ℕ} (m : ℕ) (f : EuclideanSpace ℝ (Fin d) → ℝ)
    (y : EuclideanSpace ℝ (Fin d)) : ℝ :=
  ∑ ℓ ∈ Finset.Ico (-(m : ℤ)) ((m : ℤ) + 1), centralDiffCoeff m ℓ * f ((ℓ : ℝ) • y)
end
end Qatlib.Concepts.GradientOracle.CentralDiff
