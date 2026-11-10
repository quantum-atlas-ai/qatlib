/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Foundations.ResourceBounds.AdaptiveCosts

set_option autoImplicit false
namespace Qatlib.Papers.SpacetimeLB26.ResourceDefs
open Qatlib.Foundations.ResourceBounds.AdaptiveCosts

theorem resource_comparison {H : Type*} [Fintype H] {S : ℕ}
    (law : PMF H) (width : Fin S → H → ℕ) :
    meanCost law width ≤ worstCost law width ∧ worstCost law width ≤ envelopeCost law width :=
  ⟨mean_le_worst law width,worst_le_envelope law width⟩

theorem unequal_resources : worstCost exclusiveLaw exclusiveWidth = 100 ∧ envelopeCost exclusiveLaw exclusiveWidth = 200 :=
  exclusive_costs

end Qatlib.Papers.SpacetimeLB26.ResourceDefs
