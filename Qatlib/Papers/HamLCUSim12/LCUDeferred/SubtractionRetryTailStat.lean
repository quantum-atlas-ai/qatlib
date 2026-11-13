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

/-!
# Subtraction retry tail contract

`SubtractionRetryTail` states an exponential bound for the exhaustion event of the Bernoulli
product state `retryState`. For positive `r` and `3 * r` parameters in `[0, 1 / 2]`, the
contract bounds the mass of `retryExhausted r` by `exp (-r / 14)`, as used in the retry analysis
of [ChildsWiebe2012].

## Main statements

* `SubtractionRetryTail`: specifies the exponential exhaustion bound for all valid retry
  parameters.

## References

* [Childs and Wiebe, 2012][ChildsWiebe2012]
-/

open Qatlib.Foundations.PureStateMath
open Qatlib

open Matrix

namespace Qatlib.Papers.HamLCUSim12.LCUDeferred

open scoped BigOperators

/-- The proposition that, for positive `r` and `3 * r` retry parameters in `[0, 1 / 2]`, the
event with at least `2 * r + 1` true outcomes has mass at most `exp (-r / 14)`. -/
def SubtractionRetryTail : Prop :=
  ∀ r : ℕ, 0 < r → ∀ p : Fin (3 * r) → ℝ, (∀ i, 0 ≤ p i) → (∀ i, p i ≤ 1 / 2) →
    MeasureProb (retryState (3 * r) p) (retryExhausted r) ≤ Real.exp (-(r : ℝ) / 14)

end Qatlib.Papers.HamLCUSim12.LCUDeferred
