/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.QuditTeleport.CommLowerBound.CommBoundContracts
set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false
namespace Qatlib.Concepts.QuditTeleport.CommLowerBound

def CommBoundRestricted : Prop :=
  CommBoundMergeNoGoQudit ∧ CommBoundMessageInjectiveQudit ∧
    CommBoundMergeNoGoBell ∧ CommBoundMessageInjectiveBell
end Qatlib.Concepts.QuditTeleport.CommLowerBound
