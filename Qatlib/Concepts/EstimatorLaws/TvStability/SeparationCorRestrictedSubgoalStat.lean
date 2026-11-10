/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Analysis.Complex.Trigonometric
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Data.Real.Sqrt
import Mathlib.Data.Real.Basic

namespace Qatlib.Concepts.EstimatorLaws.TvStability

def SeparationCorollaryRestrictedSubgoal : Prop :=
  ∀ (a θ : ℝ) (M : ℕ), 0 < M → a = Real.sin θ ^ 2 → 0 ≤ θ → θ + Real.pi ≤ 2 * Real.pi →
    ∀ (ε : ℝ), 0 < ε → Real.pi / M ≤ ε →
      |Real.sin (θ + Real.pi / M) ^ 2 - a| ≤ 2 * ε * Real.sqrt (a * (1 - a)) + ε ^ 2

end Qatlib.Concepts.EstimatorLaws.TvStability
