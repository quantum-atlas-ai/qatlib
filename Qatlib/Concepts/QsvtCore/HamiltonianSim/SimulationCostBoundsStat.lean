/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Log.Basic

open scoped Real

namespace Qatlib.Concepts.QsvtCore.HamiltonianSim

def SimulationCostBounds : Prop :=
  ∀ (t ε r : ℝ), 0 < t → 0 < ε → ε < 1 → t ≤ r → (t / r) ^ r = ε →
    (t ≤ (Real.log (1/ε)) / (Real.exp 1) →
      (Real.log (1/ε)) /
          Real.log ((Real.exp 1) + (Real.log (1/ε)) / t) ≤ r ∧
      r ≤ 4 * (Real.log (1/ε)) /
          Real.log ((Real.exp 1) + (Real.log (1/ε)) / t)) ∧
    ((Real.log (1/ε)) / (Real.exp 1) ≤ t → r ≤ (Real.exp 1) * t) ∧
    (∀ q : ℝ, 0 < q → r ≤ (Real.exp q) * t + (Real.log (1/ε)) / q)

end Qatlib.Concepts.QsvtCore.HamiltonianSim
