/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.SearchStopping.KnownCount.Section3RotationSubgoal
import Qatlib.Foundations.BornMetrics.EventProbability
import Qatlib.Foundations.QueryWordCore.Circuit
import Qatlib.Foundations.PureStateMath.Qubit
set_option backward.isDefEq.respectTransparency false
set_option warningAsError false
open Qatlib.Foundations.QueryWordCore.Circuit
open Qatlib.Foundations.PureStateMath
open Qatlib.Foundations.BornMetrics.EventProbability

namespace Qatlib.Concepts.SearchStopping.KnownCount

open Qatlib.Concepts.SearchStopping.KnownCount

variable {I : Type*} [Fintype I] [DecidableEq I]

theorem grover_empty_success (j : ℕ) :
    MeasureProb (GroverState (∅ : Finset I) j) ∅ = 0 := by
  simp [MeasureProb]

theorem grover_full_success (hN : 0 < Fintype.card I) (j : ℕ) :
    MeasureProb (GroverState (Finset.univ : Finset I) j) Finset.univ = 1 :=
  measureProb_univ (normalized_groverState hN Finset.univ j)

theorem grover_zero_success (A : Finset I) :
    MeasureProb (GroverState A 0) A = (A.card : ℝ) / Fintype.card I := by
  simpa [GroverState, GroverCircuit, RepeatCircuit] using measureProb_uniform A

end Qatlib.Concepts.SearchStopping.KnownCount
