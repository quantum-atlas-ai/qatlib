/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Analysis.Complex.Exponential
import Mathlib.Data.Real.Sqrt
import Qatlib.Foundations.PureStateMath.Qubit
import Mathlib.Data.Complex.Basic

/-!
# Product states for subtraction retries

`retryState` assigns product amplitudes to Boolean retry outcomes, with squared amplitudes
representing independent Bernoulli probabilities when the parameters lie in the probability
range. `retryExhausted` selects the outcomes with at least `2 * r + 1` true bits among `3 * r`
trials, for the retry analysis associated with [ChildsWiebe2012].

## Main statements

* `retryState`: defines the product of square-root Bernoulli amplitudes.
* `retryExhausted`: defines the retry exhaustion event by its number of true outcomes.

## References

* [Childs and Wiebe, 2012][ChildsWiebe2012]
-/

open Qatlib.Foundations.PureStateMath
open Qatlib

open Matrix

open scoped BigOperators

namespace Qatlib.Papers.HamLCUSim12.LCUDeferred

/-- The product-amplitude state whose factor at trial `i` is `sqrt (p i)` for a true outcome and
`sqrt (1 - p i)` for a false outcome. -/
noncomputable def retryState (m : ℕ) (p : Fin m → ℝ) : QState (Fin m → Bool) :=
  fun z => ∏ i, ((Real.sqrt (if z i then p i else 1 - p i) : ℝ) : ℂ)

/-- The Boolean strings of length `3 * r` containing at least `2 * r + 1` true outcomes. -/
def retryExhausted (r : ℕ) : Finset (Fin (3 * r) → Bool) :=
  Finset.univ.filter fun z => 2 * r + 1 ≤ (Finset.univ.filter fun i : Fin (3 * r) => z i).card
end Qatlib.Papers.HamLCUSim12.LCUDeferred
