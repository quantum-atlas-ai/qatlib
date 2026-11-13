/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.WalkSearch.WalkAlgorithms.WalkFreshValidationContracts
import Mathlib.Data.Finset.Prod

/-!
# Stored-subgraph queries and replay vocabulary

This module defines `storedEdges`, setup and update query lists, and the corresponding answer
records. `storedReplay` retains the true answers, while `storedReplayInsert` adds their
reversals to an existing stored edge set.

`storedInsert` describes the same incident-edge insertion directly from adjacency values. These
definitions support concrete setup and update accounting for graph data in quantum-walk search
[MagniezNayakRolandSantha2011].

## Main statements

* `storedEdges`: the induced ordered edge set.
* `storedSetupQueries` and `storedUpdateQueries`: explicit adjacency query lists.
* `storedReplayInsert`: insertion from recorded query answers.

## References

* [Magniez et al., 2011][MagniezNayakRolandSantha2011]
-/

set_option autoImplicit false
noncomputable section

namespace Qatlib.Concepts.WalkSearch.WalkAlgorithms

/-- The ordered adjacent pairs whose endpoints both belong to `U`. -/
def storedEdges {n : ℕ} (adj : Fin n → Fin n → Bool) (U : Finset (Fin n)) :
    Finset (Fin n × Fin n) :=
  (U.product U).filter (fun p => adj p.1 p.2 = true)

/-- The list of all ordered pairs in `U × U` used for setup adjacency queries. -/
def storedSetupQueries {n : ℕ} (U : Finset (Fin n)) : List (Fin n × Fin n) :=
  (U.product U).toList

/-- The list of adjacency queries `(a, v)` with `a` ranging over the stored subset. -/
def storedUpdateQueries {n : ℕ} (U : Finset (Fin n)) (v : Fin n) :
    List (Fin n × Fin n) := U.toList.map (fun a => (a, v))

/-- Attach the Boolean adjacency answer to each pair in a query list. -/
def storedQueryAnswers {n : ℕ} (adj : Fin n → Fin n → Bool)
    (queries : List (Fin n × Fin n)) : List ((Fin n × Fin n) × Bool) :=
  queries.map (fun p => (p, adj p.1 p.2))

/-- The finite set of queried pairs whose recorded answers are true. -/
def storedReplay {n : ℕ} (answers : List ((Fin n × Fin n) × Bool)) :
    Finset (Fin n × Fin n) :=
  (answers.toFinset.filter (fun row => row.2 = true)).image Prod.fst

/-- Extend a stored edge set with the true replayed pairs and their reversals. -/
def storedReplayInsert {n : ℕ} (D : Finset (Fin n × Fin n))
    (answers : List ((Fin n × Fin n) × Bool)) : Finset (Fin n × Fin n) :=
  D ∪ (storedReplay answers ∪ (storedReplay answers).image Prod.swap)

/-- Extend the induced edge set on `U` with both orientations of each true adjacency between a
vertex of `U` and `v`. -/
def storedInsert {n : ℕ} (adj : Fin n → Fin n → Bool) (U : Finset (Fin n))
    (v : Fin n) : Finset (Fin n × Fin n) :=
  storedEdges adj U ∪
    ((U.filter (fun a => adj a v = true)).image (fun a => (a, v)) ∪
      (U.filter (fun a => adj a v = true)).image (fun a => (v, a)))

end Qatlib.Concepts.WalkSearch.WalkAlgorithms
