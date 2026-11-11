/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.WalkSearch.Primitives.ClassificationContracts
import Qatlib.Concepts.WalkSearch.Primitives.ClassificationBounds
import Qatlib.Concepts.WalkSearch.Primitives.ClassificationTriangleTrace
import Qatlib.Concepts.WalkSearch.Primitives.ClassificationSoundness
import Qatlib.Concepts.WalkSearch.Primitives.ClassificationTermination

/-!
# Verification of corrected classification

Proves `classifySpec_source_complete` by combining classification soundness, termination,
partition, and resource estimates. The resulting contract supplies the deterministic guarantees
needed for the surrounding quantum graph-search construction; see [Ambainis2005].

## Main statements

* `classifySpec_source_complete`: Establishes `classifySpecCorrected`, including the corrected
  query budget and either a sound triangle or a disjoint partition satisfying the stated
  triangle-count and graph-edge bounds.

## References

* [Ambainis, 2005][Ambainis2005]
-/

set_option warningAsError false
set_option backward.isDefEq.respectTransparency false
set_option autoImplicit false
set_option maxHeartbeats 1200000
noncomputable section
namespace Qatlib.Concepts.WalkSearch.Primitives
open scoped Classical BigOperators

/-- Establishes `classifySpecCorrected`, including the corrected query budget and either a sound
triangle or a disjoint partition satisfying the stated triangle-count and graph-edge bounds. -/
theorem classifySpec_source_complete : classifySpecCorrected := by
  intro n G sgs τ dHi dLo K c tThin hn hdLo _hdHi hτ ttape stape S _hG hthin hc r
  refine ⟨classifyScan_cost_bound G sgs τ dHi dLo K c ttape stape S hn hdLo hτ hc,?_⟩
  cases htri : r.triangle with
  | some p =>
    rcases p with ⟨a,b,cc⟩
    exact classifyScan_sound G sgs τ K c ttape stape Finset.univ.toList S a b cc htri
  | none =>
    have he:=classifyScan_full_left_empty G sgs τ K c ttape stape S htri
    have hp:=classifyScan_partition G sgs τ K c ttape stape Finset.univ.toList S
    change r.left=∅ at he
    change partitionPayload S.edges r.left r.movedT r.movedE at hp
    refine ⟨?_,hp.2.2.2.1,classifyScan_triCount_bound G sgs τ K c ttape stape Finset.univ.toList S,
      classifyScan_E_bound G sgs τ dHi dLo K c tThin ttape stape S hn hdLo hτ hc hthin⟩
    simpa only [he,Finset.empty_union] using hp.1
end Qatlib.Concepts.WalkSearch.Primitives
