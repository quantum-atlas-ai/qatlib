/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.AmplitudeSearch.InterruptMin.SearchBoundary

/-!
# Randomized Grover success with singular cases

`Lemma2Corrected` states the exact success probability when the Grover iteration count is
uniform below a positive bound m. It includes the singular case sin(2θ) = 0 and a success lower
bound of 1/4 when sin(2θ) > 0 and m ≥ 1/sin(2θ).

For the mathematical background, see [BoyerEtAl1998].

## Main statements

* `Lemma2Corrected`: The contract giving the piecewise formula for `RandomizedSuccess A m` and
  its lower bound 1/4 when sin(2θ) > 0 and m ≥ 1/sin(2θ).

## References

* [Boyer et al., 1998][BoyerEtAl1998]
-/

set_option backward.isDefEq.respectTransparency false

open Qatlib.Concepts.QueryComplexity.AdaptiveQuery

namespace Qatlib.Concepts.SearchStopping.GroverSuccess
universe u

/-- The contract giving the piecewise formula for `RandomizedSuccess A m` and its lower bound
1/4 when sin(2θ) > 0 and m ≥ 1/sin(2θ). -/
def Lemma2Corrected : Prop :=
  ∀ {I : Type u} [Fintype I] [DecidableEq I], 0 < Fintype.card I →
    ∀ (A : Finset I) (θ : ℝ),
      (Real.sin θ)^2 = (A.card : ℝ) / (Fintype.card I : ℝ) →
      ∀ (m : ℕ), 0 < m →
        RandomizedSuccess A m =
          (if Real.sin (2*θ) = 0 then (A.card : ℝ) / (Fintype.card I : ℝ)
          else 1/2 - Real.sin (4*m*θ)/(4*m*Real.sin (2*θ))) ∧
        (0 < Real.sin (2*θ) → 1 / Real.sin (2*θ) ≤ (m : ℝ) →
          1/4 ≤ RandomizedSuccess A m)

end Qatlib.Concepts.SearchStopping.GroverSuccess
