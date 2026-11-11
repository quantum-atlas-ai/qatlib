/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.OrderedOracle.TiSdpBridge.OrderedSearchSDP

/-!
# Exact Laurent witnesses from SDP statement

`ExactProgramFromSDP` names the implication from `tiSDPFeasible n k 0` to `exactTIProgram n k`
for nonzero size. It specifies one direction of the Laurent and matrix feasibility
correspondence used in ordered-search semidefinite programming [ChildsLandahlParrilo2007].

## Main statements

* `ExactProgramFromSDP`: zero-error translation-invariant SDP feasibility implies existence of
  an exact Laurent-program witness.

## References

* [Childs, Landahl, and Parrilo, 2007][ChildsLandahlParrilo2007]
-/

set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

namespace Qatlib.Concepts.OrderedOracle.TiSdpBridge

/-- The proposition that zero-error translation-invariant SDP feasibility yields an
`exactTIProgram` witness for every nonzero size and natural query count. -/
def ExactProgramFromSDP : Prop :=
  ∀ (n k : ℕ) [NeZero n], tiSDPFeasible n k 0 → exactTIProgram n k

end Qatlib.Concepts.OrderedOracle.TiSdpBridge
