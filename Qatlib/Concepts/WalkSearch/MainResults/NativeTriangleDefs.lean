/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.WalkSearch.MainResults.GeneralMnrsFind

/-!
# Finite triangle predicates and assigned costs

`triangleEdges` represents a finite ordered edge relation, and `triangleOf` requires the three
indicated pairs of a vertex triple to belong to it. `triangleSearchCost` assigns the cubic cost
used in the finite triangle selection account. For background on quantum search and amplitude
amplification, see [BrassardEtAl2002].

## Main statements

* `triangleEdges`: Finite sets of ordered pairs of vertices in `Fin n`.
* `triangleSearchCost`: The assigned cost `n^3` for finite triangle search.

## References

* [Brassard et al., 2002][BrassardEtAl2002]
-/

set_option backward.isDefEq.respectTransparency false

namespace Qatlib.Concepts.WalkSearch.MainResults
namespace NativeTriangleDefs

open Matrix
open scoped Classical BigOperators
set_option autoImplicit false

/-- Finite sets of ordered pairs of vertices in `Fin n`. -/
abbrev triangleEdges (n : ℕ) := Finset (Fin n × Fin n)

/-- The three ordered pairs `(a, b)`, `(b, c)`, and `(a, c)` of the given triple belong to `E`. -/
def triangleOf {n : ℕ} (E : triangleEdges n) (t : Fin n × Fin n × Fin n) : Prop :=
  (t.1, t.2.1) ∈ E ∧ (t.2.1, t.2.2) ∈ E ∧ (t.1, t.2.2) ∈ E

/-- The assigned cost `n^3` for finite triangle search. -/
def triangleSearchCost (n : ℕ) : ℕ := n ^ 3

end NativeTriangleDefs
end Qatlib.Concepts.WalkSearch.MainResults
