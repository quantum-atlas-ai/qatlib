/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Foundations.ResourceBounds.AdaptiveCosts

/-!
# Comparison of spacetime resource measures

This module compares expected cost, worst cost over records, and the sum of layerwise envelopes
for finite history distributions. The example `unequal_resources` demonstrates that the last two
quantities can differ in the resource accounting of [BhartiHaugTanggara2026].

## Main statements

* `resource_comparison`: For a finite distribution of histories, mean cost is at most worst
  cost, which is at most the layer-envelope cost.
* `unequal_resources`: The exclusive-history example has worst cost `100` and layer-envelope
  cost `200`.

## References

* [Bharti et al., 2026][BhartiHaugTanggara2026]
-/

set_option autoImplicit false
namespace Qatlib.Papers.SpacetimeLB26.ResourceDefs
open Qatlib.Foundations.ResourceBounds.AdaptiveCosts

/-- For a finite distribution of histories, mean cost is at most worst cost, which is at most
the layer-envelope cost. See [BhartiHaugTanggara2026]. -/
theorem resource_comparison {H : Type*} [Fintype H] {S : ℕ}
    (law : PMF H) (width : Fin S → H → ℕ) :
    meanCost law width ≤ worstCost law width ∧ worstCost law width ≤ envelopeCost law width :=
  ⟨mean_le_worst law width,worst_le_envelope law width⟩

/-- The exclusive-history example has worst cost `100` and layer-envelope cost `200`. See
[BhartiHaugTanggara2026]. -/
theorem unequal_resources : worstCost exclusiveLaw exclusiveWidth = 100 ∧ envelopeCost exclusiveLaw exclusiveWidth = 200 :=
  exclusive_costs

end Qatlib.Papers.SpacetimeLB26.ResourceDefs
