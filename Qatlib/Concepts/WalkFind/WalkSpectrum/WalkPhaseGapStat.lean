/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.WalkFind.UniqueCollision.JohnsonWalk
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Data.Real.Sqrt
import Mathlib.Data.Real.Basic
set_option warningAsError false
open Qatlib.Concepts.WalkFind.UniqueCollision
set_option autoImplicit false

namespace Qatlib.Concepts.WalkFind.WalkSpectrum

open Qatlib.Concepts.WalkFind.UniqueCollision

open Matrix

def WalkPhaseGap : Prop :=
  ∀ (k N r : ℕ), 1 ≤ k → k ≤ r → 2 * k ≤ r + 1 →
    ((8 * Real.pi ^ 2 * (k ^ 3) * (r + 1) * (2 ^ (k + 4)) * (k + 1) * k : ℝ) ≤
      N - r) →
    ∀ (μ : ℂ) (v : Fin (2 * k + 1) → ℂ),
      jwWalk k N r *ᵥ v = μ • v →
      (∑ i, star (v i) * jwStart k N r i) = 0 →
      v ≠ 0 →
      ‖μ - 1‖ ≥
        2 / Real.sqrt ((r + 1 : ℝ)) -
          (2 : ℝ) ^ (((k : ℝ) + 2) / 2) *
            2 * Real.sqrt 2 * Real.sqrt (((k : ℝ) ^ 3) / (N - r)) ∧
      ‖μ + 1‖ ≥
        Real.sqrt 2 -
          (2 : ℝ) ^ (((k : ℝ) + 2) / 2) *
            2 * Real.sqrt 2 * Real.sqrt (((k : ℝ) ^ 3) / (N - r))

end Qatlib.Concepts.WalkFind.WalkSpectrum
