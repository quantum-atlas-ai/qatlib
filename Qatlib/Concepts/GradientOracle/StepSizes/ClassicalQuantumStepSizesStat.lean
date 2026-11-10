/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Analysis.Calculus.Taylor

set_option autoImplicit false

namespace Qatlib.Concepts.GradientOracle.StepSizes

def ClassicalQuantumStepSizes : Prop :=
  (∀ (F1 F0 f1 f0 l δ : ℝ), 0 < l → 0 < δ → |F1 - f1| ≤ δ → |F0 - f0| ≤ δ →
      |(F1 - F0) / l - (f1 - f0) / l| ≤ 2 * δ / l) ∧
  (∀ (f : ℝ → ℝ) (x l D : ℝ), 0 < l → ContDiff ℝ 3 f →
      (∀ ξ ∈ Set.Icc (x - l / 2) (x + l / 2), |iteratedDeriv 3 f ξ| ≤ D) →
      |(f (x + l / 2) - f (x - l / 2)) / l - deriv f x| ≤ D * l ^ 2 / 24) ∧
  (∀ (σ D2 D3 : ℝ) (d : ℕ), 0 < σ → 0 < D2 → 0 < D3 → 0 < d →
      (2 * Real.sqrt (6 * σ / D3)) ^ 2 * D3 / 24 = σ ∧
      (2 * Real.sqrt 3 * σ / (D2 * Real.sqrt d)) * D2 * Real.sqrt d / (2 * Real.sqrt 3) = σ)

end Qatlib.Concepts.GradientOracle.StepSizes
