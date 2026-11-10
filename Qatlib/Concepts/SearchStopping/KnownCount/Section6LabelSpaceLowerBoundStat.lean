/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.QueryComplexity.DegreeMethod.Complexity
import Qatlib.Concepts.QueryWordCore.QueryMachinery.Oracle
open Qatlib.Concepts.QueryWordCore.QueryMachinery
open Qatlib.Concepts.QueryComplexity.DegreeMethod

namespace Qatlib.Concepts.SearchStopping.KnownCount

def Section6LabelSpaceLowerBound : Prop :=
  ∀ (I : Type*) (C : Type*) [Fintype I] [DecidableEq I] [Fintype C] [DecidableEq C]
    (lbl : C → I), Function.Surjective lbl →
    FixedSpaceQueryLowerBound
      (fun w : I => SetOracle (Finset.univ.filter fun c => lbl c = w))
      (fun w : I => Finset.univ.filter fun c => lbl c = w)
      (1 / 2) (Nat.floor (Real.sin (Real.pi / 8) * Real.sqrt (Fintype.card I : ℝ)))

end Qatlib.Concepts.SearchStopping.KnownCount
