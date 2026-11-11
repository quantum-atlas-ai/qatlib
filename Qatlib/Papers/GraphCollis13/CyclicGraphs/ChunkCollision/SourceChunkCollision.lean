/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.GraphCollis13.QueryBound.Model.GraphCollisionModel
import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Data.Finset.Range
import Mathlib.Tactic

set_option backward.isDefEq.respectTransparency false

/-!
# Proposition 1 — the chunk test for `CI(n,a,b)`

Fixed arXiv:1305.1021v1, §4.1, page 6.

The paper subdivides the vertices of `CI(n,a,b)` into consecutive chunks
`V_1, …, V_{⌈n/(b−a)⌉}`.  For a chunk starting at `k` it defines `r` as the
smallest and `l` as the largest index inside the chunk with `x_r = x_l = 1`,
puts `u` at cyclic distance `a` before `r` and `v` at cyclic distance `b` after
`l`, and claims:

> Proposition 1. For some vertex `s ∈ [u,v] : x_s = 1`, if and only if there is
> a collision for some vertex in the chunk.

This file fixes the circulant graph `CI(n,a,b)` of Definition 4 (page 5), the
cyclic distance, the chunk and the cyclic interval `[u,v]`, and states
Proposition 1 for those objects.

Note on the statement: the proposition as printed is used only inside the
subroutine `SUB`, whose task is to decide whether some vertex of the chunk is in
collision.  A literal reading is delicate in degenerate configurations (e.g.
`n = 20`, `a = 4`, `b = 6`, a chunk containing a single `1` at its first
position and a further `1` at cyclic distance `< a` to its left): then
`[u,v]` contains a `1` although no chunk vertex collides.  The statement below
is therefore kept exactly as printed, with the potential counterexample recorded
at the theorem.  The final statement is recorded as a `Prop`-valued definition;
because the literal printed form admits the counterexample, it is not asserted
as a theorem.
-/

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.GraphCollis13.CyclicGraphs.ChunkCollision

/-- Clockwise distance on the `n`-cycle: the number of steps from `i` to `j`
going in increasing order of labels modulo `n`. -/
def cwDist {n : ℕ} (i j : Fin n) : ℕ :=
  (j.val + n - i.val) % n

/-- Cyclic (undirected) distance on the `n`-cycle. -/
def cdist {n : ℕ} (i j : Fin n) : ℕ :=
  min (cwDist i j) (cwDist j i)

/-- **Definition 4 (arXiv:1305.1021v1, page 5).**  The circulant graph
`CI(n,a,b)`: vertices `0, …, n−1`, and an edge between `k ≠ l` when the cyclic
distance between them lies in `[a,b]`.  The label order is immaterial, so the
graph is built from the symmetric relation given by `cdist`. -/
def CI (n a b : ℕ) : SimpleGraph (Fin n) :=
  SimpleGraph.fromRel fun i j => a ≤ cdist i j ∧ cdist i j ≤ b

/-- Membership in `CI(n,a,b)` as an iff, via `SimpleGraph.fromRel_adj`. -/
theorem CI_adj_iff {n a b : ℕ} {i j : Fin n} :
    (CI n a b).Adj i j ↔
      i ≠ j ∧ ((a ≤ cdist i j ∧ cdist i j ≤ b) ∨
        (a ≤ cdist j i ∧ cdist j i ≤ b)) :=
  SimpleGraph.fromRel_adj _ _ _

/-- The cyclic distance is symmetric. -/
theorem cdist_comm {n : ℕ} (i j : Fin n) : cdist i j = cdist j i := by
  unfold cdist
  rw [Nat.min_comm]

/-- The cyclic distance from a vertex to itself is zero. -/
theorem cdist_self {n : ℕ} (i : Fin n) : cdist i i = 0 := by
  unfold cdist cwDist
  rw [Nat.add_sub_cancel_left, Nat.mod_self]
  simp

/-- The clockwise distance from a vertex to itself is zero. -/
theorem cwDist_self {n : ℕ} (i : Fin n) : cwDist i i = 0 := by
  unfold cwDist
  rw [Nat.add_sub_cancel_left, Nat.mod_self]

/-- The clockwise distance is strictly smaller than `n` on a nonempty cycle. -/
theorem cwDist_lt {n : ℕ} (hn : 0 < n) (i j : Fin n) : cwDist i j < n :=
  Nat.mod_lt _ hn

/-- A consecutive chunk of `D + 1` vertices starting at `k`, going clockwise.
The paper uses `D = b − a` (page 6). -/
def chunk {n : ℕ} (k : Fin n) (D : ℕ) : Finset (Fin n) := by
  classical
  exact Finset.univ.filter (fun s => cwDist k s ≤ D)

/-- The cyclic interval `[u,v]`: the vertices met going clockwise from `u` to
`v`.  The paper's `[u,v]` is read clockwise (Figure 3, page 6). -/
def cIcc {n : ℕ} (u v : Fin n) : Finset (Fin n) := by
  classical
  exact Finset.univ.filter (fun s => cwDist u s ≤ cwDist u v)

/-- The chunk contains its starting vertex. -/
theorem self_mem_chunk {n : ℕ} (k : Fin n) (D : ℕ) : k ∈ chunk k D := by
  classical
  unfold chunk
  rw [Finset.mem_filter]
  exact ⟨Finset.mem_univ _, by rw [cwDist_self]; exact Nat.zero_le D⟩

/-- The cyclic interval contains its left endpoint. -/
theorem self_mem_cIcc {n : ℕ} (u v : Fin n) : u ∈ cIcc u v := by
  classical
  unfold cIcc
  rw [Finset.mem_filter]
  exact ⟨Finset.mem_univ _, by rw [cwDist_self]; exact Nat.zero_le _⟩

/-- **Proposition 1 (arXiv:1305.1021v1, page 6).**  Let `V` be the chunk of
`D + 1` consecutive vertices starting at `k` (`D = b − a`).  Let `r` be the
first and `l` the last vertex of the chunk with `x = 1`, let `u` be at cyclic
distance `a` before `r` and `v` at cyclic distance `b` after `l`.  Then there is
`s ∈ [u,v]` with `x_s = 1` if and only if some vertex of the chunk collides.

Formal gap: the statement is recorded as printed in the paper.  A literal
reading fails in degenerate configurations — the docstring of the module records
the shape of a counterexample (`n = 20`, `a = 4`, `b = 6`, a single `1` at the
chunk's first position and another at cyclic distance `< a` to its left), and
the paper's algorithm is only invoked under the additional side conditions of
`SUB` (`r` and `l` found by two applications of MIN, `l` to the right of `r`).
The proof needs (i) the geometric lemma that every vertex at cyclic distance in
`[a,b]` from the chunk lies in `[u,v]`, and (ii) the converse inclusion using
that `r` and `l` are the extreme `1`-positions.  Neither the geometry of
circulant intervals nor the necessary case analysis is available in Mathlib
(`SimpleGraph.circulantGraph` exists, but no interval or distance lemmas).
Candidate follow-up: prove the corrected version with the side conditions
`D = b − a`, `r ≤ l`, `b ≤ n/2`, `l − r ≤ b − a`, then derive the printed
statement under those hypotheses. -/
def proposition1_chunk_collision {n a b D : ℕ} (hn : 0 < n) (hab : a ≤ b)
    (x : Fin n → Bool) (k r l : Fin n)
    (hrchunk : r ∈ chunk k D) (hrx : x r = true)
    (hrmin : ∀ s ∈ chunk k D, x s = true → cwDist k r ≤ cwDist k s)
    (hlchunk : l ∈ chunk k D) (hlx : x l = true)
    (hlmax : ∀ s ∈ chunk k D, x s = true → cwDist k s ≤ cwDist k l)
    (u v : Fin n) (hu : cwDist u r = a) (hv : cwDist l v = b) : Prop :=
    (∃ s ∈ cIcc u v, x s = true) ↔
      ∃ s t : Fin n, s ∈ chunk k D ∧ x s = true ∧ x t = true ∧
        (CI n a b).Adj s t

end Qatlib.Papers.GraphCollis13.CyclicGraphs.ChunkCollision
