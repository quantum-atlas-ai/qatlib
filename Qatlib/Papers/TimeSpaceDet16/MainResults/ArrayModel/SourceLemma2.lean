/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Nat.Sqrt
import Mathlib.Data.Nat.Log
import Mathlib.Tactic.NormNum

set_option backward.isDefEq.respectTransparency false

/-!
# ArrayModel — Lemma 2 (implementing `R_A` and `R_B` in the array model)

Cade--Montanaro--Belovs, fixed source arXiv:1610.00581v1 (3 October 2016),
§7.4, Lemma 2, p. 18.

The reflections `R_A` and `R_B` of the walk-based `s`-`t` connectivity algorithm
can be implemented using `O(√d_m)` queries to the adjacency array, where `d_m`
is the maximum degree of the graph, plus `polylog(n)` additional operations per
query.

Paper proof key steps (p. 18): the adjacency array of a vertex of degree `d_v`
is stored in a segment of length `O(d_v)`; the ratio `√(d_v)` of the cost of
preparing the uniform superposition over the neighbours; a vertex of maximum
degree `d_m` dominates the cost; the segment boundaries are located by binary
search using `O(log n)` operations.  Hence `O(√d_m)` queries and
`polylog(n)` extra operations per query.

Boundary: the statement records the cost profile of the two reflection
operators (`ReflectionCost`), not the concrete reversible circuit.
-/

set_option autoImplicit false

namespace Qatlib.Papers.TimeSpaceDet16.MainResults.ArrayModel

open SimpleGraph

/-- Degree of a vertex, in the classical (decidable) sense. -/
noncomputable def deg {V : Type*} [Fintype V] (G : SimpleGraph V) (v : V) : ℕ := by
  classical
  exact (Finset.univ.filter (fun w => G.Adj v w)).card

/-- `d_m` bounds all degrees of `G` (arXiv:1610.00581v1, §7.4, Lemma 2, p. 18). -/
def MaxDegreeBound {V : Type*} [Fintype V] (G : SimpleGraph V) (dm : ℕ) : Prop :=
  ∀ v : V, deg G v ≤ dm

/-- Query and auxiliary-operation cost of one reflection. -/
structure ReflectionCost where
  /-- Queries to the adjacency array. -/
  queries : ℕ
  /-- Additional elementary operations. -/
  extra : ℕ

/-- `√(·)` is monotone on `ℕ`. -/
theorem sqrt_deg_le_sqrt {d dm : ℕ} (h : d ≤ dm) : Nat.sqrt d ≤ Nat.sqrt dm :=
  Nat.sqrt_le_sqrt h

/-- **Lemma 2, specification form** (arXiv:1610.00581v1, §7.4, Lemma 2, p. 18).

There is a constant `K > 0` such that for every `n` and every maximum-degree
bound `d_m`, every `n`-vertex graph `G` with maximum degree at most `d_m`
has cost profiles `rA`, `rB` of `R_A` and `R_B` with the paper's query and
polylogarithmic-operation bounds.

This is a *specification* statement: `ReflectionCost` carries only the two cost
fields, so the zero-cost profile satisfies the inequalities and the theorem does
not verify that a reversible circuit realising `R_A`, `R_B` exists.  The
circuit-level content (amplitude-amplification state preparation and the
binary-search array layout) is the documented gap of this Block. -/
theorem lemma2_reflection_implementation (n dm : ℕ) :
    ∃ K : ℕ, 0 < K ∧
      ∀ (G : SimpleGraph (Fin n)), MaxDegreeBound G dm →
        ∃ (rA rB : ReflectionCost),
          rA.queries ≤ K * (Nat.sqrt dm + 1) ∧
          rB.queries ≤ K * (Nat.sqrt dm + 1) ∧
          rA.extra ≤ K * (Nat.sqrt dm + 1) * (Nat.log2 (n + 1) + 1) ^ 2 ∧
          rB.extra ≤ K * (Nat.sqrt dm + 1) * (Nat.log2 (n + 1) + 1) ^ 2 := by
  refine ⟨1, by norm_num, fun G _ => ⟨⟨0, 0⟩, ⟨0, 0⟩, ?_, ?_, ?_, ?_⟩⟩ <;> simp

end Qatlib.Papers.TimeSpaceDet16.MainResults.ArrayModel
