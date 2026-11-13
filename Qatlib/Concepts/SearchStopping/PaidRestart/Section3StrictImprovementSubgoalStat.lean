/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.SearchStopping.RestartLaw.RestartProfile
import Qatlib.Foundations.PureStateMath.Qubit

/-!
# Statement of a strict restart improvement

Defines `Section3StrictImprovementSubgoal` for a search space of size `2 ^ 20` with one marked
address. It compares a 596-iteration restart strategy with the 804-iteration floor benchmark,
giving rational bounds on the success probability and expected Grover iterations. For the
quantum-search analysis, see [BoyerEtAl1998].

## Main statements

* `Section3StrictImprovementSubgoal`: The proposition that single-target search on `2 ^ 20`
  addresses has floor benchmark 804, success probability between 0.8441 and 0.8443 after 596
  iterations, and expected restart iterations strictly between 705 and 804.

## References

* [Boyer et al., 1998][BoyerEtAl1998]
-/

set_option backward.isDefEq.respectTransparency false
open Qatlib.Foundations.PureStateMath

namespace Qatlib.Concepts.SearchStopping.PaidRestart

open Qatlib.Concepts.SearchStopping.KnownCount

/-- The proposition that single-target search on `2 ^ 20` addresses has floor benchmark 804,
success probability between 0.8441 and 0.8443 after 596 iterations, and expected restart
iterations strictly between 705 and 804. -/
def Section3StrictImprovementSubgoal : Prop :=
  ∀ (I : Type*) [Fintype I] [DecidableEq I], Fintype.card I = 2 ^ 20 →
    ∀ A : Finset I, A.card = 1 →
      Nat.floor (Real.pi / (4 * Real.arcsin (1 / 1024))) = 804 ∧
      8441 / 10000 < MeasureProb (GroverState A 596) A ∧
      MeasureProb (GroverState A 596) A < 8443 / 10000 ∧
      596 / MeasureProb (GroverState A 596) A < 804 ∧
      705 < 596 / MeasureProb (GroverState A 596) A

end Qatlib.Concepts.SearchStopping.PaidRestart
