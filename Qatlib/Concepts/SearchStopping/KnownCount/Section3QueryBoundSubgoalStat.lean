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

def SingleTargetSearchClaim (I : Type*) [Fintype I] [DecidableEq I] : Prop :=
  ∃ k : ℕ, FixedSpaceQueryUpperBound (MarkOracle (I := I)) (fun w => {w}) (1 / 2) k ∧
    (k : ℝ) ≤ Real.pi / (4 * Real.sqrt (1 / (Fintype.card I : ℝ)))

def Section3QueryBoundSubgoal : Prop :=
  ∀ (I : Type*) [Fintype I] [DecidableEq I],
    2 ≤ Fintype.card I → SingleTargetSearchClaim I

end Qatlib.Concepts.SearchStopping.KnownCount
