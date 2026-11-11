/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-!
# Simulation cost equation specification

This module defines `SimulationCostEquation`, specifying existence and uniqueness of the real
simulation cost parameter in `[t, ∞)` for each positive `t` and each error in `(0, 1)`. The
mathematical background is developed in [GilyenSuLowWiebe2019].

## Main statements

* `SimulationCostEquation`: the unique solution specification for `(t / r) ^ r = ε`.

## References

* [Gilyén et al., 2019][GilyenSuLowWiebe2019]
-/

open scoped Real

namespace Qatlib.Concepts.QsvtCore.HamiltonianSim

/-- The assertion that for positive `t` and `0 < ε < 1`, the equation `(t / r) ^ r = ε` has
exactly one solution satisfying `t ≤ r`. -/
def SimulationCostEquation : Prop :=
  ∀ (t ε : ℝ), 0 < t → 0 < ε → ε < 1 →
    ∃ r : ℝ, t ≤ r ∧ (t / r) ^ r = ε ∧
      ∀ s : ℝ, t ≤ s → (t / s) ^ s = ε → s = r

end Qatlib.Concepts.QsvtCore.HamiltonianSim
