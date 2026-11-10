/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.VarTimeAmpAmp10.CoherentAA.CoherentAmplificationContracts
set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

namespace Qatlib.Papers.VarTimeAmpAmp10.CoherentAA

def CoherentAmplification : Prop := coherentAmplificationWindow

end Qatlib.Papers.VarTimeAmpAmp10.CoherentAA
