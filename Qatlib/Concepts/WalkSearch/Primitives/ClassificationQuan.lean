/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.WalkSearch.Primitives.ClassificationStat
import Qatlib.Concepts.WalkSearch.Primitives.ClassificationSpecification
import Qatlib.Concepts.WalkSearch.Primitives.ClassificationBudgetPreservation

/-!
# The corrected classification theorem

Exports `classification_answer`, the proof of the corrected classification contract. It combines
the scan's query bound with sound triangle output or a disjoint pair partition satisfying the
required counting bounds, within the graph-search setting surveyed in [Ambainis2005].

## Main statements

* `classification_answer`: Establishes `Classification`: under the corrected hypotheses, a
  complete scan satisfies its query budget and returns either a valid triangle or the specified
  disjoint partition with triangle and graph-edge bounds.

## References

* [Ambainis, 2005][Ambainis2005]
-/

set_option backward.isDefEq.respectTransparency false
namespace Qatlib.Concepts.WalkSearch.Primitives

/-- Establishes `Classification`: under the corrected hypotheses, a complete scan satisfies its
query budget and returns either a valid triangle or the specified disjoint partition with
triangle and graph-edge bounds. -/
theorem classification_answer : Classification := classifySpec_source_complete
end Qatlib.Concepts.WalkSearch.Primitives
