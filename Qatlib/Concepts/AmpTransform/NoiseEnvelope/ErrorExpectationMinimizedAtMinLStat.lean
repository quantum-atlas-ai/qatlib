/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Analysis.SpecialFunctions.Sqrt

/-!
# Specification of the noise-envelope minimizer

`ErrorExpectationMinimizedAtMinL` states the global real-variable minimization property of the
noise envelope. It fixes the square-root expression for the minimizer used in the
amplified-transform noise analysis of [Cornwell2014].

## Main statements

* `ErrorExpectationMinimizedAtMinL`: The proposition that MinL = −M² + √(M(M−1)(M(M−1)+N))
  minimizes (L+M²)/((N−L−M)(L+M)) on −M < L < N−M for M ≥ 2 and N > 0.

## References

* [Cornwell, 2014][Cornwell2014]
-/

set_option autoImplicit false
open scoped Classical BigOperators
namespace Qatlib.Concepts.AmpTransform.NoiseEnvelope

/-- The proposition that MinL = −M² + √(M(M−1)(M(M−1)+N)) minimizes (L+M²)/((N−L−M)(L+M)) on −M
< L < N−M for M ≥ 2 and N > 0. -/
def ErrorExpectationMinimizedAtMinL : Prop :=
  ∀ (M N : ℕ), 2 ≤ M → 0 < N →
    let MinL : ℝ := -(M:ℝ)^2 +
      Real.sqrt ((M:ℝ)*((M:ℝ)-1)*((M:ℝ)*((M:ℝ)-1)+(N:ℝ)))
    let bound : ℝ → ℝ := fun L => (L+(M:ℝ)^2)/(((N:ℝ)-L-(M:ℝ))*(L+(M:ℝ)))
    ∀ L : ℝ, -(M:ℝ) < L → L < (N:ℝ)-(M:ℝ) → bound MinL ≤ bound L
end Qatlib.Concepts.AmpTransform.NoiseEnvelope
