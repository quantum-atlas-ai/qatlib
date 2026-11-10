/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.WalkSearch.Primitives.Fact5Stat
import Qatlib.Concepts.WalkSearch.Primitives.IncrementalTriangleFact5
import Qatlib.Concepts.WalkSearch.Primitives.RemovalTriangleFact5
set_option warningAsError false
namespace Qatlib.Concepts.WalkSearch.Primitives

theorem fact5_answer : Fact5 := fact5_incremental
end Qatlib.Concepts.WalkSearch.Primitives
