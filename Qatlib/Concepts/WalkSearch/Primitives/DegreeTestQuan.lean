/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.WalkSearch.Primitives.DegreeTestStat
import Qatlib.Concepts.WalkSearch.Primitives.DegreeConcentration
set_option warningAsError false
set_option backward.isDefEq.respectTransparency false
namespace Qatlib.Concepts.WalkSearch.Primitives

theorem degreeTest_answer : DegreeTest := fact2DegreeTest_concentration_allPositive
end Qatlib.Concepts.WalkSearch.Primitives
