/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Mathlib.Data.Fintype.Prod
public import Mathlib.Data.Fintype.Sum
public import Mathlib.Data.Finset.Card
public import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Tactic.Order

/-!
# Coordinates for the Section 8 pair graph

Vertices are actual ordered two-element subsets of `Fin (N+1)`. Adjacent pairs
carry the diagonal loops, and nearest-neighbor coordinate moves give the edges.
The cut count records each edge crossing a selected set at its selected endpoint.
-/

@[expose] public section

set_option autoImplicit false

open scoped BigOperators

namespace Qatlib.Papers.KhovanovHom25.MainResults.PairFlow


/-- Ordered coordinates for the two-element subsets of `Fin (N+1)`. -/
abbrev Pair (N : ℕ) := {v : Fin (N + 1) × Fin (N + 1) // v.1 < v.2}

/-- The left coordinate of a vertex. -/
def left {N : ℕ} (v : Pair N) : ℕ := v.val.1.val

/-- The right coordinate of a vertex. -/
def right {N : ℕ} (v : Pair N) : ℕ := v.val.2.val

/-- Valid pair coordinates are strictly ordered and lie below `N+1`. -/
theorem coords {N : ℕ} (v : Pair N) : left v < right v ∧ right v ≤ N := by
  refine ⟨v.property, ?_⟩
  change v.val.2.val ≤ N
  have := v.val.2.isLt
  omega

/-- Two vertices with the same coordinates coincide. -/
theorem pair_ext {N : ℕ} {v u : Pair N}
    (hl : left v = left u) (hr : right v = right u) : v = u := by
  apply Subtype.ext
  apply Prod.ext <;> apply Fin.ext
  · exact hl
  · exact hr

/-- An adjacent pair is a diagonal-loop vertex of the source graph. -/
def IsLoop {N : ℕ} (v : Pair N) : Prop := right v = left v + 1

instance {N : ℕ} (v : Pair N) : Decidable (IsLoop v) := by
  change Decidable (right v = left v + 1)
  infer_instance

/-- Undirected nearest-neighbor adjacency in the triangular pair graph. -/
def Adj {N : ℕ} (v u : Pair N) : Prop :=
  (left v = left u ∧ (right v + 1 = right u ∨ right u + 1 = right v)) ∨
    (right v = right u ∧ (left v + 1 = left u ∨ left u + 1 = left v))

instance {N : ℕ} (v u : Pair N) : Decidable (Adj v u) := by
  change Decidable
    ((left v = left u ∧ (right v + 1 = right u ∨ right u + 1 = right v)) ∨
      (right v = right u ∧ (left v + 1 = left u ∨ left u + 1 = left v)))
  infer_instance

/-- The number of adjacent-pair vertices in the selected set. -/
def loopCount {N : ℕ} (S : Finset (Pair N)) : ℕ := (S.filter IsLoop).card

/-- Each edge from the set to its complement is counted at its selected endpoint. -/
noncomputable def cutCount {N : ℕ} (S : Finset (Pair N)) : ℕ := by
  classical
  exact ∑ v ∈ S, (Finset.univ.filter (fun u => u ∉ S ∧ Adj v u)).card

end Qatlib.Papers.KhovanovHom25.MainResults.PairFlow
