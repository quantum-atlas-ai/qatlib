/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Analysis.Complex.Trigonometric
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Data.Real.Sqrt
import Mathlib.Data.Real.Basic

/-!
# Restricted amplitude separation contract

Records the amplitude perturbation bound for shifting an angle by `π / M`. This proposition
captures the squared-sine error estimate used to compare phase resolution with amplitude
resolution in [Montanaro2015].

## Main statements

* `SeparationCorollaryRestrictedSubgoal` specifies the error bound `2 * ε * sqrt (a * (1 - a)) +
  ε²` for positive `M` and `ε`, assuming `π / M ≤ ε`.

## References

* [Montanaro, 2015][Montanaro2015]
-/

namespace Qatlib.Concepts.EstimatorLaws.TvStability

/-- The proposition asserting the squared-sine perturbation bound for `a = sin² θ` and the shift
`π / M`, under `0 ≤ θ ≤ π`, `M > 0`, and `π / M ≤ ε` with `ε > 0`. -/
def SeparationCorollaryRestrictedSubgoal : Prop :=
  ∀ (a θ : ℝ) (M : ℕ), 0 < M → a = Real.sin θ ^ 2 → 0 ≤ θ → θ + Real.pi ≤ 2 * Real.pi →
    ∀ (ε : ℝ), 0 < ε → Real.pi / M ≤ ε →
      |Real.sin (θ + Real.pi / M) ^ 2 - a| ≤ 2 * ε * Real.sqrt (a * (1 - a)) + ε ^ 2

end Qatlib.Concepts.EstimatorLaws.TvStability
