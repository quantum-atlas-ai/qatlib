/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Concepts.LocalCircuits.LocalGateCosts.Costs

@[expose] public section

/-!
# The worst-case gate count bounds every specific frame cost

The paper writes `b(g,n;k)` for the worst case of `b(g,n;u,v)` over orthonormal target frames
`v` of the computational basis [Knill1995], §3. The published definition
`Qatlib.Concepts.LocalCircuits.LocalGateCosts.bMax` is the supremum of the extended natural costs
of mapping `basisFrame n k` to such a frame, so it dominates the cost of each individual frame.

This module records that half of the identification. It is the step that lets the paper's
worst-case `b(g,n;k)` be used as an upper bound for a concrete frame, and it does not provide a
numerical estimate of `bMax`. The identity frame is `basisFrame n k` itself only for `k = 0`; for
`k > 0` the cost of the identity frame enters the supremum through a different witness.

## Main statements

* `bComplexity_le_bMax`: an orthonormal target frame has cost at most `bMax g n k`.

## References

* [Knill, 1995][Knill1995]
-/

set_option autoImplicit false
noncomputable section
open Qatlib.Foundations.BornMetrics.FiniteStats
namespace Qatlib.Papers.QCircApprox95.MainResults

open Qatlib.Concepts.LocalCircuits.LocalGateCosts

/-- Every orthonormal target frame is one of the witnesses in the defining set of `bMax`, so its
local gate complexity from the computational basis frame is at most the worst case
`Qatlib.Concepts.LocalCircuits.LocalGateCosts.bMax` [Knill1995], §3. The statement is the
`le_sSup` half of the worst-case definition; it gives no numerical bound on `bMax` and does not
assert that the supremum is attained. -/
theorem bComplexity_le_bMax {g n k : ℕ} {v : Fin k → Fin (2 ^ n) → ℂ}
    (hv : Orthonormal (2 ^ n) k v) :
    bComplexity g n k (basisFrame n k) v ≤ bMax g n k :=
  le_sSup ⟨v, hv, rfl⟩

end Qatlib.Papers.QCircApprox95.MainResults
