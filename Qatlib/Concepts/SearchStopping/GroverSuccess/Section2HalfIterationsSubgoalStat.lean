/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.SearchStopping.KnownCount.Section3RotationSubgoal
import Qatlib.Foundations.PureStateMath.Qubit
set_option backward.isDefEq.respectTransparency false
set_option warningAsError false
open Qatlib.Foundations.PureStateMath

namespace Qatlib.Concepts.SearchStopping.GroverSuccess

open Qatlib.Concepts.SearchStopping.KnownCount

def Section2HalfIterationsSubgoal : Prop :=
  ∀ (I : Type*) [Fintype I] [DecidableEq I], 0 < Fintype.card I →
    ∀ (A : Finset I) (θ : ℝ), 0 < θ → θ < Real.pi / 2 →
      (Real.sin θ) ^ 2 = (A.card : ℝ) / (Fintype.card I : ℝ) →
      ∃ k : ℕ, (k : ℝ) ≤ Real.pi / (8 * θ) + 1 ∧
        1 / 2 ≤ MeasureProb (GroverState A k) A

end Qatlib.Concepts.SearchStopping.GroverSuccess
