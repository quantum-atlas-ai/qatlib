/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.OrderedOracle.TiSdpBridge.OrderedSearchSDP
set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

namespace Qatlib.Concepts.OrderedOracle.TiSdpBridge

def Theorem9SDPCharacterization : Prop :=
  ∀ (n k : ℕ) [NeZero n] (ε : ℝ),
    tiSDPFeasible n k ε ↔ tiPolyConditions n k ε

end Qatlib.Concepts.OrderedOracle.TiSdpBridge
