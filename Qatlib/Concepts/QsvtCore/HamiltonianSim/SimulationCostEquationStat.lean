/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Log.Basic

open scoped Real

namespace Qatlib.Concepts.QsvtCore.HamiltonianSim

def SimulationCostEquation : Prop :=
  ∀ (t ε : ℝ), 0 < t → 0 < ε → ε < 1 →
    ∃ r : ℝ, t ≤ r ∧ (t / r) ^ r = ε ∧
      ∀ s : ℝ, t ≤ s → (t / s) ^ s = ε → s = r

end Qatlib.Concepts.QsvtCore.HamiltonianSim
