/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.StoppingCore.BranchCostCore.WeightedUnboundedExecution
set_option warningAsError false

open Qatlib.Concepts.StoppingCore.BranchCostCore

set_option autoImplicit false
noncomputable section
namespace Qatlib.Concepts.ZeroCostLimit.FirstHitMass
open Qatlib
open scoped ENNReal

def haltMass {S O : Type} [Fintype S] [DecidableEq S] [Fintype O] [DecidableEq O]
    (next : S → PMF (O ⊕ S)) (cost : S → ℕ) (cfg : O ⊕ S) (o : O) (k : ℕ) : ℝ≥0∞ :=
  ⨆ fuel : ℕ, weightedRunFor next cost fuel cfg (.inl o,k)
end Qatlib.Concepts.ZeroCostLimit.FirstHitMass
