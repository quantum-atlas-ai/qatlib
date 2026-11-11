/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.StoppingCore.BranchCostCore.WeightedUnboundedExecution

/-!
# Accumulated-cost halting mass

The definition `haltMass` assigns an extended nonnegative real mass to each output and total
cost by taking the supremum over finite-fuel weighted runs. It supplies the cost-resolved
halting quantity for probabilistic algorithm analysis, with [DeckerDraismaWocjan2009] as
application context.

## Main statements

* `haltMass`: Define output-and-cost halting mass by a fuel supremum.

## References

* [Decker et al., 2009][DeckerDraismaWocjan2009]
-/

set_option warningAsError false

open Qatlib.Concepts.StoppingCore.BranchCostCore

set_option autoImplicit false
noncomputable section
namespace Qatlib.Concepts.ZeroCostLimit.FirstHitMass
open Qatlib
open scoped ENNReal

/-- The supremum over finite fuel of the probability of halting with output `o` and accumulated
cost `k`. -/
def haltMass {S O : Type} [Fintype S] [DecidableEq S] [Fintype O] [DecidableEq O]
    (next : S → PMF (O ⊕ S)) (cost : S → ℕ) (cfg : O ⊕ S) (o : O) (k : ℕ) : ℝ≥0∞ :=
  ⨆ fuel : ℕ, weightedRunFor next cost fuel cfg (.inl o,k)
end Qatlib.Concepts.ZeroCostLimit.FirstHitMass
