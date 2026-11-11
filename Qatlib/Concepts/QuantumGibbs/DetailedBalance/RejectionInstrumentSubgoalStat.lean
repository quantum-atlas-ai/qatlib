/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.WalkSearch.TwoLevelLower
import Qatlib.Foundations.PureStateMath.Qubit

/-!
# The Metropolis rejection-instrument subgoal

This module states a contract joining classical Metropolis balance and the quantum acceptance
coin. For a transition matrix and nonnegative weights it requires pointwise balance of accepted
transitions, while the coin contract specifies unitarity and the exact Born probability, as
motivated by [TemmeEtAl2011].

## Main statements

* `RejectionInstrumentSubgoal`: The combined accepted-transition and coin specification.

## References

* [Temme et al., 2011][TemmeEtAl2011]
-/

set_option backward.isDefEq.respectTransparency false
set_option warningAsError false
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.WalkSearch.TwoLevelLower

open Matrix

namespace Qatlib.Concepts.QuantumGibbs.DetailedBalance

/-- The proposition that Metropolis acceptance balances a transition matrix against nonnegative
weights, and that every acceptance parameter in `[0, 1]` gives a unitary coin whose
outcome-one Born probability equals that parameter. -/
def RejectionInstrumentSubgoal : Prop :=
  ∀ (I : Type) [Fintype I] [DecidableEq I] (P : I → I → ℝ), IsTransitionMatrix P →
    ∀ (π : I → ℝ), (∀ x, 0 ≤ π x) →
    (∀ x y : I, π x * (P x y * MetropolisAcceptance P π x y)
      = π y * (P y x * MetropolisAcceptance P π y x)) ∧
    ∀ (a : ℝ), 0 ≤ a → a ≤ 1 →
      (MetropolisCoin a ∈ Matrix.unitaryGroup (Fin 2) ℂ) ∧
      BornProb (MetropolisCoin a *ᵥ Ket 0) 1 = a

end Qatlib.Concepts.QuantumGibbs.DetailedBalance
