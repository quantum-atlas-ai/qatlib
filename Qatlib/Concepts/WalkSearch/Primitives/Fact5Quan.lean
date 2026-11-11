/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.WalkSearch.Primitives.Fact5Stat
import Qatlib.Concepts.WalkSearch.Primitives.IncrementalTriangleFact5
import Qatlib.Concepts.WalkSearch.Primitives.RemovalTriangleFact5

/-!
# Incremental triangle-count guarantee

`fact5_answer` proves `Fact5` by invoking the incremental triangle-count bound. The statement
limits the final number of triangles when each inserted edge has a bounded number of common
neighbors at insertion time, a counting ingredient for subset-search reductions
[ChildsEisenberg2003].

## Main statements

* `fact5_answer`: the incremental triangle-count contract.

## References

* [Childs and Eisenberg, 2003][ChildsEisenberg2003]
-/

set_option warningAsError false
namespace Qatlib.Concepts.WalkSearch.Primitives

/-- Establishes `Fact5` from the incremental bound `fact5_incremental`. -/
theorem fact5_answer : Fact5 := fact5_incremental
end Qatlib.Concepts.WalkSearch.Primitives
