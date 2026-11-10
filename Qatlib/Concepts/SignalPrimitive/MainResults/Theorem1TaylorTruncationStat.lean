/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.QspSimulation.Achievability.TrigApproximation

open Qatlib.Concepts.QspSimulation.Achievability

namespace Qatlib.Concepts.SignalPrimitive.MainResults

def Theorem1TaylorTruncation : Prop :=
  ∀ (τ ε : ℝ), 0 < ε → ∃ n : ℕ,
    2 * |τ| ≤ (n : ℝ) + 1 ∧
    Qatlib.Concepts.QspSimulation.Achievability.exponentialTaylorError τ n ≤ ε ∧
    (n : ℝ) ≤ 4 * |τ| + 8 * Real.log (8 / min ε 1) + 8

end Qatlib.Concepts.SignalPrimitive.MainResults
