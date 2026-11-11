/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.WalkSearch.WalkAlgorithms.WalkCorrectedContracts

/-!
# Corrected graph-collision statement

`Theorem3` names the corrected graph-collision proposition `theorem3WalkCorrected`. It is the
statement used by the collision-search reduction with the corrected solver cost assumptions. See
[Ambainis2005] for the mathematical background.

## Main statements

* `Theorem3`: the corrected graph-collision proposition.

## References

* [Ambainis, 2005][Ambainis2005]
-/

set_option warningAsError false
open Qatlib.Concepts.WalkSearch.WalkAlgorithms

namespace Qatlib.Concepts.WalkSearch.CollisionSearch

/-- The proposition `theorem3WalkCorrected`, naming the corrected graph-collision guarantees for
the walk-based reduction. -/
def Theorem3 : Prop := theorem3WalkCorrected

end Qatlib.Concepts.WalkSearch.CollisionSearch
