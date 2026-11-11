/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.WalkSearch.Primitives.DegreeTestContracts

/-!
# Degree-test contract

`DegreeTest` names the proposition `fact2DegreeTestAllPositive`. This interface packages the
degree-test statement used by triangle-search primitives; quantum search provides the
algorithmic background [Grover1996].

## Main statements

* `DegreeTest`: the all-positive degree-test proposition.

## References

* [Grover, 1996][Grover1996]
-/

set_option warningAsError false

namespace Qatlib.Concepts.WalkSearch.Primitives

/-- The proposition `fact2DegreeTestAllPositive`, exposed as the degree-test contract. -/
def DegreeTest : Prop := fact2DegreeTestAllPositive

end Qatlib.Concepts.WalkSearch.Primitives
