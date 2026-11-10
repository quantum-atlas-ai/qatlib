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

def KnownMarkedSets (I : Type*) [Fintype I] (m : ℕ) := {A : Finset I // A.card = m}

def KnownCountSearchClaim (I : Type*) [Fintype I] [DecidableEq I] (m : ℕ) : Prop :=
  ∃ k : ℕ,
    FixedSpaceQueryUpperBound
      (fun A : KnownMarkedSets I m => SetOracle A.val) (fun A => A.val) (1 / 2) k ∧
      (k : ℝ) ≤ Real.pi / (4 * Real.sqrt ((m : ℝ) / Fintype.card I))
end Qatlib.Concepts.SearchStopping.KnownCount
