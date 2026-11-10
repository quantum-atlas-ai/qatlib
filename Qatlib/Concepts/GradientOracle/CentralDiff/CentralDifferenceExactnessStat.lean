/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Analysis.Calculus.Taylor
import Mathlib.Data.Int.Interval
import Qatlib.Concepts.GradientOracle.CentralDiff.CentralDifferenceDefs

noncomputable section

namespace Qatlib.Concepts.GradientOracle.CentralDiff

def CentralDifferenceExactness : Prop :=
  ∀ (m : ℕ), 0 < m → ∀ j : ℕ, j ≤ 2 * m →
    ∑ ℓ ∈ Finset.Ico (-(m : ℤ)) ((m : ℤ) + 1),
      centralDiffCoeff m ℓ * ((ℓ : ℝ) ^ j) = if j = 1 then 1 else 0

end Qatlib.Concepts.GradientOracle.CentralDiff
