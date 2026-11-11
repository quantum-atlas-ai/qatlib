/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.QueryComplexity.DegreeMethod.Complexity
import Qatlib.Concepts.QueryWordCore.QueryMachinery.Oracle

/-!
# Ancilla search lower-bound contract

`Section6AncillaLowerBound` states the phase-query search lower bound with a nonempty finite
workspace. Both the oracle's marked subspace and the success event are the fiber of the target
address.

For the mathematical background, see [BealsEtAl2001].

## Main statements

* `Section6AncillaLowerBound`: The proposition asserting fixed-space query lower bound
  ⌊sin(π/8)√N⌋ at success threshold 1/2 for singleton address search with arbitrary nonempty
  finite workspace.

## References

* [Beals et al., 2001][BealsEtAl2001]
-/

open Qatlib.Concepts.QueryWordCore.QueryMachinery
open Qatlib.Concepts.QueryComplexity.DegreeMethod

namespace Qatlib.Concepts.SearchStopping.KnownCount

/-- The proposition asserting fixed-space query lower bound ⌊sin(π/8)√N⌋ at success threshold
1/2 for singleton address search with arbitrary nonempty finite workspace. -/
def Section6AncillaLowerBound : Prop :=
  ∀ (I : Type*) (W : Type*) [Fintype I] [DecidableEq I] [Fintype W] [DecidableEq W]
    [Nonempty W],
    FixedSpaceQueryLowerBound
      (fun w : I => SetOracle (Finset.univ.filter fun p : I × W => p.1 = w))
      (fun w : I => Finset.univ.filter fun p : I × W => p.1 = w)
      (1 / 2) (Nat.floor (Real.sin (Real.pi / 8) * Real.sqrt (Fintype.card I : ℝ)))

end Qatlib.Concepts.SearchStopping.KnownCount
