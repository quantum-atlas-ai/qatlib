/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Analysis.Calculus.Taylor
import Mathlib.Data.Int.Interval

namespace Qatlib.Concepts.GradientOracle.CentralDiff
noncomputable section

noncomputable def centralDiffCoeff (m : ℕ) (ℓ : ℤ) : ℝ :=
  if ℓ = 0 then 0 else
    (-1 : ℝ) ^ (ℓ.natAbs - 1) / (ℓ : ℝ) *
      (Nat.choose m ℓ.natAbs : ℕ) / (Nat.choose (m + ℓ.natAbs) ℓ.natAbs : ℕ)
end
noncomputable section

noncomputable def centralDiffApply {d : ℕ} (m : ℕ) (f : EuclideanSpace ℝ (Fin d) → ℝ)
    (y : EuclideanSpace ℝ (Fin d)) : ℝ :=
  ∑ ℓ ∈ Finset.Ico (-(m : ℤ)) ((m : ℤ) + 1), centralDiffCoeff m ℓ * f ((ℓ : ℝ) • y)
end
end Qatlib.Concepts.GradientOracle.CentralDiff
