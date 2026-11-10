/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Analysis.Complex.Exponential
import Mathlib.Data.Real.Sqrt
import Qatlib.Foundations.PureStateMath.Qubit
import Mathlib.Data.Complex.Basic
open Qatlib.Foundations.PureStateMath
open Qatlib

open Matrix

open scoped BigOperators

namespace Qatlib.Papers.HamLCUSim12.LCUDeferred

noncomputable def retryState (m : ℕ) (p : Fin m → ℝ) : QState (Fin m → Bool) :=
  fun z => ∏ i, ((Real.sqrt (if z i then p i else 1 - p i) : ℝ) : ℂ)

def retryExhausted (r : ℕ) : Finset (Fin (3 * r) → Bool) :=
  Finset.univ.filter fun z => 2 * r + 1 ≤ (Finset.univ.filter fun i : Fin (3 * r) => z i).card
end Qatlib.Papers.HamLCUSim12.LCUDeferred
