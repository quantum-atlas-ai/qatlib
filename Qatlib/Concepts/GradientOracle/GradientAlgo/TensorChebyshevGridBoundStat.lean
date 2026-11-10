/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Probability.Moments.SubGaussian

namespace Qatlib.Concepts.GradientOracle.GradientAlgo

def TensorChebyshevGridBound : Prop :=
  ∀ (d k : ℕ), 0 < d → 0 < k → ∀ r : ℝ, 1 < r →
    ∀ S : Finset ℝ, (∀ v ∈ S, |v| ≤ 1 / 2) → (∀ v ∈ S, -v ∈ S) → S.Nonempty →
    ∀ H : (Fin k → Fin d) → ℝ, (∀ α, |H α| ≤ 1) →
    ((Finset.univ.filter (fun y : Fin d → S =>
        Real.sqrt 2 * (r * Real.sqrt ((d : ℝ) * k / 2)) ^ k
          ≤ |∑ α : Fin k → Fin d, H α * ∏ i : Fin k, (y (α i) : ℝ)|)).card : ℝ)
      ≤ (((S.card : ℕ) ^ d : ℕ) : ℝ) / r ^ (2 * k)

end Qatlib.Concepts.GradientOracle.GradientAlgo
