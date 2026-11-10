/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Data.Fintype.Basic

set_option autoImplicit false

namespace Qatlib.Concepts.GraphQuery.EdgeQuery

def graphCollision {n : ℕ} (adj : Fin n → Fin n → Bool) (x : Fin n → Bool) : Bool :=
  decide (∃ u v : Fin n, adj u v = true ∧ x u = true ∧ x v = true)

def gcDegree {n : ℕ} (edges : Finset (Fin n × Fin n)) (v : Fin n) : ℕ :=
  (edges.filter fun e => e.1 = v ∨ e.2 = v).card

def gcMaxDegree {n : ℕ} (edges : Finset (Fin n × Fin n)) : ℕ :=
  Finset.sup Finset.univ (gcDegree edges)

end Qatlib.Concepts.GraphQuery.EdgeQuery
