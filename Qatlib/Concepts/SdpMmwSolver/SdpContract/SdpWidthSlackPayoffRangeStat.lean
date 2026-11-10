/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.SdpMmwSolver.SdpContract.RetainedContracts
set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

namespace Qatlib.Concepts.SdpMmwSolver.SdpContract

def SdpWidthSlackPayoffRange : Prop := SdpWidthSlackPayoffRangeContract

end Qatlib.Concepts.SdpMmwSolver.SdpContract
