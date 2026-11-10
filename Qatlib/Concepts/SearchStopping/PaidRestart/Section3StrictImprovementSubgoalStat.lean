/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.SearchStopping.RestartLaw.RestartProfile
import Qatlib.Foundations.PureStateMath.Qubit
set_option backward.isDefEq.respectTransparency false
set_option warningAsError false
open Qatlib.Foundations.PureStateMath

namespace Qatlib.Concepts.SearchStopping.PaidRestart

open Qatlib.Concepts.SearchStopping.KnownCount

def Section3StrictImprovementSubgoal : Prop :=
  ∀ (I : Type*) [Fintype I] [DecidableEq I], Fintype.card I = 2 ^ 20 →
    ∀ A : Finset I, A.card = 1 →
      Nat.floor (Real.pi / (4 * Real.arcsin (1 / 1024))) = 804 ∧
      8441 / 10000 < MeasureProb (GroverState A 596) A ∧
      MeasureProb (GroverState A 596) A < 8443 / 10000 ∧
      596 / MeasureProb (GroverState A 596) A < 804 ∧
      705 < 596 / MeasureProb (GroverState A 596) A

end Qatlib.Concepts.SearchStopping.PaidRestart
