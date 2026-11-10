/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Analysis.Complex.Exponential
import Mathlib.Data.Real.Sqrt
import Qatlib.Foundations.PureStateMath.Qubit
import Mathlib.Data.Complex.Basic
import Qatlib.Papers.HamLCUSim12.LCUDeferred.SubtractionRetryDefs
set_option warningAsError false
open Qatlib.Foundations.PureStateMath
open Qatlib

open Matrix

namespace Qatlib.Papers.HamLCUSim12.LCUDeferred

open scoped BigOperators

def SubtractionRetryTail : Prop :=
  ∀ r : ℕ, 0 < r → ∀ p : Fin (3 * r) → ℝ, (∀ i, 0 ≤ p i) → (∀ i, p i ≤ 1 / 2) →
    MeasureProb (retryState (3 * r) p) (retryExhausted r) ≤ Real.exp (-(r : ℝ) / 14)

end Qatlib.Papers.HamLCUSim12.LCUDeferred
