/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.SearchStopping.KnownCount.Section3RotationSubgoal
import Qatlib.Foundations.PureStateMath.Qubit

/-!
# Grover success with a half-iteration budget

`Section2HalfIterationsSubgoal` states that a nondegenerate marked fraction permits success at
least 1/2 within π/(8θ) + 1 Grover iterations. The angle θ lies strictly between zero and π/2
and satisfies sin²(θ) equal to the marked fraction.

For the mathematical background, see [Grover1997].

## Main statements

* `Section2HalfIterationsSubgoal`: The contract asserting existence of k ≤ π/(8θ) + 1 with
  Grover marked-set success at least 1/2 for 0 < θ < π/2 and the specified marked fraction.

## References

* [Grover, 1997][Grover1997]
-/

set_option backward.isDefEq.respectTransparency false
open Qatlib.Foundations.PureStateMath

namespace Qatlib.Concepts.SearchStopping.GroverSuccess

open Qatlib.Concepts.SearchStopping.KnownCount

/-- The contract asserting existence of k ≤ π/(8θ) + 1 with Grover marked-set success at least
1/2 for 0 < θ < π/2 and the specified marked fraction. -/
def Section2HalfIterationsSubgoal : Prop :=
  ∀ (I : Type*) [Fintype I] [DecidableEq I], 0 < Fintype.card I →
    ∀ (A : Finset I) (θ : ℝ), 0 < θ → θ < Real.pi / 2 →
      (Real.sin θ) ^ 2 = (A.card : ℝ) / (Fintype.card I : ℝ) →
      ∃ k : ℕ, (k : ℝ) ≤ Real.pi / (8 * θ) + 1 ∧
        1 / 2 ≤ MeasureProb (GroverState A k) A

end Qatlib.Concepts.SearchStopping.GroverSuccess
