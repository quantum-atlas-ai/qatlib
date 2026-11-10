/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.OrderedOracle.TiSdpBridge.OrderedSearchSDP
set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

namespace Qatlib.Concepts.OrderedOracle.TiSdpBridge

def ExactProgramFromSDP : Prop :=
  ∀ (n k : ℕ) [NeZero n], tiSDPFeasible n k 0 → exactTIProgram n k

end Qatlib.Concepts.OrderedOracle.TiSdpBridge
