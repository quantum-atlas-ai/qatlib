/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.WalkSearch.Primitives.DegreeTestStat
import Qatlib.Concepts.WalkSearch.Primitives.DegreeConcentration

/-!
# Degree-test concentration guarantee

`degreeTest_answer` proves the `DegreeTest` contract by using the all-positive concentration
result. This degree-classification primitive supplies probabilistic estimates for graph-search
reductions, whose search background includes [Grover1996].

## Main statements

* `degreeTest_answer`: the all-positive degree-test contract.

## References

* [Grover, 1996][Grover1996]
-/

set_option warningAsError false
set_option backward.isDefEq.respectTransparency false
namespace Qatlib.Concepts.WalkSearch.Primitives

/-- Establishes `DegreeTest` using the all-positive degree-test concentration theorem. -/
theorem degreeTest_answer : DegreeTest := fact2DegreeTest_concentration_allPositive
end Qatlib.Concepts.WalkSearch.Primitives
