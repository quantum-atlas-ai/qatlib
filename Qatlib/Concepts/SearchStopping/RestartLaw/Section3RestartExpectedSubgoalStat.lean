/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.SearchStopping.RestartLaw.RestartProfile
import Qatlib.Foundations.PureStateMath.Qubit

/-!
# Statement of the geometric restart expectation

Defines `Section3RestartExpectedSubgoal`, the geometric-series identity for repeated
fixed-length Grover attempts. With positive success probability, the expected total number of
Grover iterations equals the iteration count divided by that probability. For the quantum-search
analysis, see [BoyerEtAl1998].

## Main statements

* `Section3RestartExpectedSubgoal`: The proposition that, under the stated Grover-angle and
  positive-success hypotheses, the geometric first-success sum of total iteration costs equals
  `j / MeasureProb (GroverState A j) A`.

## References

* [Boyer et al., 1998][BoyerEtAl1998]
-/

set_option backward.isDefEq.respectTransparency false
open Qatlib.Foundations.PureStateMath

set_option autoImplicit false

namespace Qatlib.Concepts.SearchStopping.RestartLaw

open Qatlib.Concepts.SearchStopping.KnownCount

/-- The proposition that, under the stated Grover-angle and positive-success hypotheses, the
geometric first-success sum of total iteration costs equals `j / MeasureProb (GroverState A
j) A`. -/
def Section3RestartExpectedSubgoal : Prop :=
  ∀ (I : Type*) [Fintype I] [DecidableEq I], 0 < Fintype.card I →
    ∀ (A : Finset I) (θ : ℝ) (j : ℕ),
      0 < θ → θ < Real.pi / 2 →
      (Real.sin θ) ^ 2 = (A.card : ℝ) / (Fintype.card I : ℝ) →
      0 < MeasureProb (GroverState A j) A →
      (∑' r : ℕ, ((r + 1 : ℕ) : ℝ) * (j : ℝ) *
          ((1 - MeasureProb (GroverState A j) A) ^ (r : ℕ) *
            MeasureProb (GroverState A j) A)) =
        (j : ℝ) / MeasureProb (GroverState A j) A

end Qatlib.Concepts.SearchStopping.RestartLaw
