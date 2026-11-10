/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.WalkSearch.Primitives.DegreeTestContracts
set_option warningAsError false

namespace Qatlib.Concepts.WalkSearch.Primitives

def DegreeTest : Prop := fact2DegreeTestAllPositive

end Qatlib.Concepts.WalkSearch.Primitives
