/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.GradientOracle.CentralDiff.CentralDifferenceExactnessStat

namespace Qatlib.Concepts.GradientOracle.CentralDiff

def CentralDifferenceCoeffLOneBound : Prop :=
  ∀ m : ℕ, 0 < m →
    ∑ ℓ ∈ Finset.Ico (0 : ℤ) ((m : ℤ) + 1), |centralDiffCoeff m ℓ| ≤ Real.log m + 1

end Qatlib.Concepts.GradientOracle.CentralDiff
