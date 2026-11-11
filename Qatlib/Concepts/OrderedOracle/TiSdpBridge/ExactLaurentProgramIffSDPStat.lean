/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.OrderedOracle.TiSdpBridge.LaurentCircleFactorization
import Qatlib.Concepts.OrderedOracle.TiSdpBridge.OrderedSearchSDP

/-!
# Exact Laurent program and SDP equivalence statement

`ExactLaurentProgramIffSDP` names the proposition that `exactTIProgram n k` is equivalent to
`tiSDPFeasible n k 0` for every nonzero size. It isolates the exact Laurent-program formulation
in the ordered-search semidefinite programming framework of [ChildsLandahlParrilo2007].

## Main statements

* `ExactLaurentProgramIffSDP`: equivalence of the exact translation-invariant Laurent program
  and zero-error SDP feasibility.

## References

* [Childs, Landahl, and Parrilo, 2007][ChildsLandahlParrilo2007]
-/

set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false
namespace Qatlib.Concepts.OrderedOracle.TiSdpBridge
open Qatlib.Concepts.OrderedOracle.TiSdpBridge Polynomial Matrix
open scoped BigOperators Classical ComplexOrder

/-- The proposition that, for every nonzero size `n` and natural query count `k`,
`exactTIProgram n k` is equivalent to zero-error translation-invariant SDP feasibility. -/
def ExactLaurentProgramIffSDP : Prop :=
  ∀ (n k : ℕ) [NeZero n], exactTIProgram n k ↔ tiSDPFeasible n k 0

end Qatlib.Concepts.OrderedOracle.TiSdpBridge
