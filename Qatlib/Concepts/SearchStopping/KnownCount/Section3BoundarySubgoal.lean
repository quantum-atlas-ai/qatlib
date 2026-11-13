/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.SearchStopping.KnownCount.Section3RotationSubgoal
import Qatlib.Foundations.BornMetrics.EventProbability
import Qatlib.Foundations.QueryWordCore.Circuit
import Qatlib.Foundations.PureStateMath.Qubit

/-!
# Boundary cases for Grover success

`grover_empty_success`, `grover_full_success`, and `grover_zero_success` give the marked-set
probabilities for empty targets, full targets, and zero iterations. These formulas cover cases
where the usual two-amplitude sine quotient needs separate treatment.

For the mathematical background, see [Grover1997].

## Main statements

* `grover_zero_success`: At zero iterations, Grover success is the marked fraction.

## References

* [Grover, 1997][Grover1997]
-/

set_option backward.isDefEq.respectTransparency false
open Qatlib.Foundations.QueryWordCore.Circuit
open Qatlib.Foundations.PureStateMath
open Qatlib.Foundations.BornMetrics.EventProbability

namespace Qatlib.Concepts.SearchStopping.KnownCount

open Qatlib.Concepts.SearchStopping.KnownCount

variable {I : Type*} [Fintype I] [DecidableEq I]

/-- Grover search has zero success probability on the empty marked set for every iteration
count. -/
theorem grover_empty_success (j : ℕ) :
    MeasureProb (GroverState (∅ : Finset I) j) ∅ = 0 := by
  simp [MeasureProb]

/-- On a nonempty finite space, Grover search succeeds with probability one when every element
is marked. -/
theorem grover_full_success (hN : 0 < Fintype.card I) (j : ℕ) :
    MeasureProb (GroverState (Finset.univ : Finset I) j) Finset.univ = 1 :=
  measureProb_univ (normalized_groverState hN Finset.univ j)

/-- At zero iterations, Grover success is the marked fraction. -/
theorem grover_zero_success (A : Finset I) :
    MeasureProb (GroverState A 0) A = (A.card : ℝ) / Fintype.card I := by
  simpa [GroverState, GroverCircuit, RepeatCircuit] using measureProb_uniform A

end Qatlib.Concepts.SearchStopping.KnownCount
