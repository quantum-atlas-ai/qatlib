/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.WalkSearch.Primitives.ClassificationContracts
set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

namespace Qatlib.Concepts.WalkSearch.Primitives

def Classification : Prop := classifySpecCorrected

end Qatlib.Concepts.WalkSearch.Primitives
