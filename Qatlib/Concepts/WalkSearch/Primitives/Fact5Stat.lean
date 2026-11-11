/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.WalkSearch.Primitives.TriangleContracts

/-!
# Triangle-count contract

`Fact5` names the incremental counting proposition `fact5`: an edge ordering with at most `τ`
earlier common neighbors per edge yields at most `n.choose 2 * τ` triangles. Such counting
estimates support subset-finding reductions [ChildsEisenberg2003].

## Main statements

* `Fact5`: the incremental triangle-count proposition.

## References

* [Childs and Eisenberg, 2003][ChildsEisenberg2003]
-/

set_option warningAsError false

namespace Qatlib.Concepts.WalkSearch.Primitives

/-- The proposition `fact5`, bounding triangle count from common-neighbor counts along an edge
insertion order. -/
def Fact5 : Prop := fact5

end Qatlib.Concepts.WalkSearch.Primitives
