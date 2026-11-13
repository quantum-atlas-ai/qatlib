/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.WalkSearch.Primitives.ClassificationContracts

/-!
# Classification proposition

Defines `Classification` as the corrected classification specification `classifySpecCorrected`.
The proposition packages the complete scan's query, triangle-output, and pair-partition
guarantees for use in graph-search constructions; see [Ambainis2005] for background.

## Main statements

* `Classification`: The proposition `classifySpecCorrected`, packaging the corrected query bound
  and the triangle-or-partition guarantees for a complete classification scan.

## References

* [Ambainis, 2005][Ambainis2005]
-/

set_option backward.isDefEq.respectTransparency false

namespace Qatlib.Concepts.WalkSearch.Primitives

/-- The proposition `classifySpecCorrected`, packaging the corrected query bound and the
triangle-or-partition guarantees for a complete classification scan. -/
def Classification : Prop := classifySpecCorrected

end Qatlib.Concepts.WalkSearch.Primitives
