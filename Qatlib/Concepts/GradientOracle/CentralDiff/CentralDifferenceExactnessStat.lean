/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Analysis.Calculus.Taylor
import Mathlib.Data.Int.Interval
import Qatlib.Concepts.GradientOracle.CentralDiff.CentralDifferenceDefs

/-!
# Central-difference exactness specification

`CentralDifferenceExactness` expresses the monomial moment conditions for an order-`m`
central-difference rule. For positive `m`, these conditions reproduce the first derivative at
zero on monomials through degree `2 * m`. See [GilyenArunachalamWiebe2019] for background.

## Main statements

* `CentralDifferenceExactness`: The proposition that, for every positive `m` and degree at most
  `2 * m`, the central-difference coefficient moment is one in degree one and zero otherwise.

## References

* [Gilyen, Arunachalam, and Wiebe, 2019][GilyenArunachalamWiebe2019]
-/

noncomputable section

namespace Qatlib.Concepts.GradientOracle.CentralDiff

/-- The proposition that, for every positive `m` and degree at most `2 * m`, the
central-difference coefficient moment is one in degree one and zero otherwise. -/
def CentralDifferenceExactness : Prop :=
  ∀ (m : ℕ), 0 < m → ∀ j : ℕ, j ≤ 2 * m →
    ∑ ℓ ∈ Finset.Ico (-(m : ℤ)) ((m : ℤ) + 1),
      centralDiffCoeff m ℓ * ((ℓ : ℝ) ^ j) = if j = 1 then 1 else 0

end Qatlib.Concepts.GradientOracle.CentralDiff
