/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.QueryComplexity.DegreeMethod.Complexity
import Qatlib.Concepts.QueryWordCore.QueryMachinery.Oracle

/-!
# Known-count search problem

`KnownMarkedSets` restricts the oracle family to marked sets of a fixed cardinality.
`KnownCountSearchClaim` requires a common fixed-space algorithm with success at least 1/2 and
query budget at most π/(4√(m/N)).

For the mathematical background, see [Grover1997].

## Main statements

* `KnownCountSearchClaim`: The proposition that fixed-space search over all m-element marked
  sets has success at least 1/2 within some natural query budget k ≤ π/(4√(m/N)), where N is the
  cardinality of `I`.

## References

* [Grover, 1997][Grover1997]
-/

open Qatlib.Concepts.QueryWordCore.QueryMachinery
open Qatlib.Concepts.QueryComplexity.DegreeMethod

namespace Qatlib.Concepts.SearchStopping.KnownCount

/-- The type of finite marked sets in `I` with cardinality exactly m. -/
def KnownMarkedSets (I : Type*) [Fintype I] (m : ℕ) := {A : Finset I // A.card = m}

/-- The proposition that fixed-space search over all m-element marked sets has success at least
1/2 within some natural query budget k ≤ π/(4√(m/N)), where N is the cardinality of `I`. -/
def KnownCountSearchClaim (I : Type*) [Fintype I] [DecidableEq I] (m : ℕ) : Prop :=
  ∃ k : ℕ,
    FixedSpaceQueryUpperBound
      (fun A : KnownMarkedSets I m => SetOracle A.val) (fun A => A.val) (1 / 2) k ∧
      (k : ℝ) ≤ Real.pi / (4 * Real.sqrt ((m : ℝ) / Fintype.card I))
end Qatlib.Concepts.SearchStopping.KnownCount
