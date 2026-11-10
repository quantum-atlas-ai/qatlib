/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Analysis.SpecialFunctions.Sqrt
set_option autoImplicit false
open scoped Classical BigOperators
namespace Qatlib.Concepts.AmpTransform.NoiseEnvelope

def ErrorExpectationMinimizedAtMinL : Prop :=
  ∀ (M N : ℕ), 2 ≤ M → 0 < N →
    let MinL : ℝ := -(M:ℝ)^2 +
      Real.sqrt ((M:ℝ)*((M:ℝ)-1)*((M:ℝ)*((M:ℝ)-1)+(N:ℝ)))
    let bound : ℝ → ℝ := fun L => (L+(M:ℝ)^2)/(((N:ℝ)-L-(M:ℝ))*(L+(M:ℝ)))
    ∀ L : ℝ, -(M:ℝ) < L → L < (N:ℝ)-(M:ℝ) → bound MinL ≤ bound L
end Qatlib.Concepts.AmpTransform.NoiseEnvelope
