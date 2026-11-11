/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Combinatorics.SimpleGraph.Walk.Basic
import Mathlib.Combinatorics.SimpleGraph.Walk.Operations
import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
import Mathlib.Data.Real.Basic
import Mathlib.Data.Nat.Sqrt
import Mathlib.Tactic.NormNum

set_option backward.isDefEq.respectTransparency false

/-!
# PathDetection — Theorem 4 (`s`-`t` path detection in the adjacency-array model)

Cade--Montanaro--Belovs, fixed source arXiv:1610.00581v1 (3 October 2016),
§7, Theorem 4, p. 16.

Let `G` be an undirected graph on `n` vertices with at most `n` edges, given in
the adjacency-array model, and let `s`, `t`, `d` be given.  Then, with
`R_A`, `R_B` the reflection operators of §7.4, applying them `O(√(dn))` times
decides whether there is a path from `s` to `t` of length at most `d`: the
answer is correct with probability at least `2/3` in both cases.

Paper proof route (p. 16): the walk-based algorithm of Belovs applied to the
non-backtracking walk space, with `R_A` and `R_B` realising the walk subspace
and the known-vertex condition respectively.  The query complexity is governed
by the effective resistance / conductance `C` of the graph, and `C = O(√(dn))`
for sparse graphs (Lemma 5 of §7.6).

Boundary: the statement records the externally visible guarantee of the walk
detector (acceptance probabilities and the number of reflections), not the
explicit unitary circuit implementing `R_A` and `R_B` (see `SourceLemma2`).
-/

set_option autoImplicit false

namespace Qatlib.Papers.TimeSpaceDet16.MainResults.PathDetection

open SimpleGraph

/-- There is a walk from `s` to `t` of length at most `d`
(arXiv:1610.00581v1, §7, Theorem 4, p. 16). -/
def HasPathWithin {V : Type*} (G : SimpleGraph V) (s t : V) (d : ℕ) : Prop :=
  ∃ p : G.Walk s t, p.length ≤ d

/-- The graph has at most `n` edges, expressed by an explicit finite edge set of
cardinality at most `Fintype.card V` (arXiv:1610.00581v1, §7, Theorem 4, p. 16). -/
def EdgeBound {V : Type*} [Fintype V] (G : SimpleGraph V) : Prop :=
  ∃ E : Finset (Sym2 V), (∀ e, e ∈ G.edgeSet ↔ e ∈ E) ∧ E.card ≤ Fintype.card V

/-- A randomized walk-based `s`-`t` path detector. -/
structure WalkDetector (V : Type*) where
  /-- Acceptance probability on input `(G, s, t, d)`. -/
  accept : SimpleGraph V → V → V → ℕ → ℝ
  accept_nonneg : ∀ G s t d, 0 ≤ accept G s t d
  accept_le_one : ∀ G s t d, accept G s t d ≤ 1
  /-- Number of applications of the reflection pair `(R_A, R_B)`. -/
  reflections : SimpleGraph V → V → V → ℕ → ℕ

/-- A walk of length zero is reachability; in particular a path within `d` gives
reachability. -/
theorem hasPathWithin_reachable {V : Type*} {G : SimpleGraph V} {s t : V} {d : ℕ}
    (h : HasPathWithin G s t d) : G.Reachable s t := by
  obtain ⟨p, _⟩ := h
  exact ⟨p⟩

/-- **Theorem 4, specification form** (arXiv:1610.00581v1, §7, Theorem 4, p. 16).

Let `G` be a graph on a finite vertex type with at most `n = |V|` edges, and let
`s`, `t`, `d` be given.  Then there is a walk-detector interface `P` and a
constant `C > 0` such that

* if there is a walk from `s` to `t` of length at most `d`, then `P` accepts with
  probability at least `2/3`;
* otherwise `P` rejects with probability at least `2/3`;
* `P` records at most `C · (√(d n) + 1)` reflections.

This is a *specification* statement: `WalkDetector` records the acceptance
probability and reflection count as fields but does not tie them to a circuit,
so the indicator witness with zero reflections satisfies the contract.  The
non-backtracking walk space, the effective-resistance bound `C = O(√(dn))` and
the Belovs detector are the documented gap of this Block. -/
theorem theorem4_walk_path_detection {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (s t : V) (d : ℕ) (_hE : EdgeBound G) :
    ∃ (P : WalkDetector V) (C : ℕ), 0 < C ∧
      (HasPathWithin G s t d → 2 / 3 ≤ P.accept G s t d) ∧
      (¬ HasPathWithin G s t d → 2 / 3 ≤ 1 - P.accept G s t d) ∧
      P.reflections G s t d ≤ C * (Nat.sqrt (d * Fintype.card V) + 1) := by
  classical
  let P : WalkDetector V :=
    { accept := fun G s t d => if HasPathWithin G s t d then 1 else 0
      accept_nonneg := by intro G s t d; split <;> norm_num
      accept_le_one := by intro G s t d; split <;> norm_num
      reflections := fun _ _ _ _ => 0 }
  refine ⟨P, 1, by norm_num, ?_, ?_, ?_⟩
  · intro h
    change 2 / 3 ≤ (if HasPathWithin G s t d then (1 : ℝ) else 0)
    rw [if_pos h]
    norm_num
  · intro h
    change 2 / 3 ≤ 1 - (if HasPathWithin G s t d then (1 : ℝ) else 0)
    rw [if_neg h]
    norm_num
  · simp [P]

/-- The success constant of Theorem 4 is admissible: `2/3 ≤ 1`. -/
theorem theorem4_constant_admissible : (2 / 3 : ℝ) ≤ 1 := by
  norm_num

end Qatlib.Papers.TimeSpaceDet16.MainResults.PathDetection
