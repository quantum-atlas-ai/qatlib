/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.GradientOracle.CentralDiff.CentralDifferenceExactnessStat

namespace Qatlib.Concepts.GradientOracle.CentralDiff

def CentralDifferencePowerSumBound : Prop :=
  ∀ (m k : ℕ), 0 < m → 2 * m ≤ k →
    ∑ ℓ ∈ Finset.Ico (-(m : ℤ)) ((m : ℤ) + 1),
      |centralDiffCoeff m ℓ * ((ℓ : ℝ) ^ (k + 1))| ≤
        6 * Real.exp (-(7 / 6 : ℝ) * (m : ℝ)) * (m : ℝ) ^ ((k : ℝ) + 3 / 2)

end Qatlib.Concepts.GradientOracle.CentralDiff
