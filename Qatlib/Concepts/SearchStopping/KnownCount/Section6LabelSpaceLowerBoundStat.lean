/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.QueryComplexity.DegreeMethod.Complexity
import Qatlib.Concepts.QueryWordCore.QueryMachinery.Oracle

/-!
# Labeled-space search lower-bound contract

`Section6LabelSpaceLowerBound` specifies the lower bound for phase-oracle search on a finite
configuration space with surjective labels. Success means landing in the full fiber of the
marked label.

For the mathematical background, see [BealsEtAl2001].

## Main statements

* `Section6LabelSpaceLowerBound`: The proposition asserting fixed-space query lower bound
  ⌊sin(π/8)√N⌋ at success threshold 1/2 for target-fiber phase oracles under any surjective
  labeling by N labels.

## References

* [Beals et al., 2001][BealsEtAl2001]
-/

open Qatlib.Concepts.QueryWordCore.QueryMachinery
open Qatlib.Concepts.QueryComplexity.DegreeMethod

namespace Qatlib.Concepts.SearchStopping.KnownCount

/-- The proposition asserting fixed-space query lower bound ⌊sin(π/8)√N⌋ at success threshold
1/2 for target-fiber phase oracles under any surjective labeling by N labels. -/
def Section6LabelSpaceLowerBound : Prop :=
  ∀ (I : Type*) (C : Type*) [Fintype I] [DecidableEq I] [Fintype C] [DecidableEq C]
    (lbl : C → I), Function.Surjective lbl →
    FixedSpaceQueryLowerBound
      (fun w : I => SetOracle (Finset.univ.filter fun c => lbl c = w))
      (fun w : I => Finset.univ.filter fun c => lbl c = w)
      (1 / 2) (Nat.floor (Real.sin (Real.pi / 8) * Real.sqrt (Fintype.card I : ℝ)))

end Qatlib.Concepts.SearchStopping.KnownCount
