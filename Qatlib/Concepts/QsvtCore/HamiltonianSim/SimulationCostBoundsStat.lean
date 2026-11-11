/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-!
# Simulation cost bound specification

This module defines `SimulationCostBounds` for positive `t` and error `ε` in `(0, 1)`. It
records two sided logarithmic bounds in the small time regime, a linear bound in the other
regime, and an upper bound for every positive auxiliary parameter. The mathematical background
is developed in [GilyenSuLowWiebe2019].

## Main statements

* `SimulationCostBounds`: the quantitative bounds for solutions of `(t / r) ^ r = ε`.

## References

* [Gilyén et al., 2019][GilyenSuLowWiebe2019]
-/

open scoped Real

namespace Qatlib.Concepts.QsvtCore.HamiltonianSim

/-- The assertion of logarithmic and linear bounds on `r ≥ t` solving `(t / r) ^ r = ε`,
together with `r ≤ exp q * t + log (1 / ε) / q` for each positive `q`. -/
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
