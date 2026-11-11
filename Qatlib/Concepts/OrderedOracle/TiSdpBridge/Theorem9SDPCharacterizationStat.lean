/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.OrderedOracle.TiSdpBridge.OrderedSearchSDP

/-!
# Statement of the ordered search SDP characterization

This module packages the equivalence of `tiSDPFeasible` and `tiPolyConditions` as the
proposition `Theorem9SDPCharacterization`, quantified over the search size, query count, and
error parameter. The formulation connects positive semidefinite matrix data with normalized
polynomial data in the ordered search framework of [ChildsLandahlParrilo2007].

## Main statements

* `Theorem9SDPCharacterization`: states the equivalence of matrix and polynomial feasibility.

## References

* [Childs, Landahl and Parrilo, 2007][ChildsLandahlParrilo2007]
-/

set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

namespace Qatlib.Concepts.OrderedOracle.TiSdpBridge

/-- The proposition that translation-invariant SDP feasibility is equivalent to the normalized
polynomial conditions for every nonzero search size, query count, and real error parameter. -/
def Theorem9SDPCharacterization : Prop :=
  ∀ (n k : ℕ) [NeZero n] (ε : ℝ),
    tiSDPFeasible n k ε ↔ tiPolyConditions n k ε

end Qatlib.Concepts.OrderedOracle.TiSdpBridge
