/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Data.Fintype.Basic

/-!
# Boolean graph collision

This module defines the Boolean graph-collision predicate and degree statistics for finite sets
of ordered vertex pairs. `graphCollision` tests whether an adjacent pair has both endpoints
marked. These predicates belong to the graph-query setting of [DurrEtAl2006].

## Main statements

* `graphCollision`: existence of an adjacent pair of marked vertices.
* `gcDegree` and `gcMaxDegree`: incident-pair counts and their maximum.

## References

* [Dürr et al., 2006][DurrEtAl2006]
-/

set_option autoImplicit false

namespace Qatlib.Concepts.GraphQuery.EdgeQuery

/-- The Boolean predicate asserting that some adjacent pair has both vertices marked by `x`. -/
def graphCollision {n : ℕ} (adj : Fin n → Fin n → Bool) (x : Fin n → Bool) : Bool :=
  decide (∃ u v : Fin n, adj u v = true ∧ x u = true ∧ x v = true)

/-- The number of pairs in `edges` having `v` as at least one endpoint. -/
def gcDegree {n : ℕ} (edges : Finset (Fin n × Fin n)) (v : Fin n) : ℕ :=
  (edges.filter fun e => e.1 = v ∨ e.2 = v).card

/-- The maximum incident-pair count over all vertices, with value zero for an empty vertex type. -/
def gcMaxDegree {n : ℕ} (edges : Finset (Fin n × Fin n)) : ℕ :=
  Finset.sup Finset.univ (gcDegree edges)

end Qatlib.Concepts.GraphQuery.EdgeQuery
