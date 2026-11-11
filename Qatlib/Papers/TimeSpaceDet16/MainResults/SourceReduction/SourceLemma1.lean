/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Combinatorics.SimpleGraph.Bipartite
import Mathlib.Combinatorics.SimpleGraph.Acyclic
import Mathlib.Combinatorics.SimpleGraph.Walk.Basic
import Mathlib.Combinatorics.SimpleGraph.Walk.Operations
import Mathlib.Combinatorics.SimpleGraph.Paths
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic.Ring

set_option backward.isDefEq.respectTransparency false

/-!
# SourceReduction — ancillary-graph parity reduction (Lemma 1)

Cade--Montanaro--Belovs, fixed source arXiv:1610.00581v1 (3 October 2016),
§3 "Reduction of Cycle Detection to s-t Connectivity", Lemma 1, p. 8.

The paper fixes an arbitrary orientation of `G` (edge `{u,v}` directed `u → v`
iff `v > u`), splits every vertex `v` into `v₀, v₁, v₂`, and adds, for each
directed edge `(u,v)`, the three undirected edges `(u_b, v_{b+1 mod 3})`, plus
`(s, k₀)` and `(t, k₁)`.

This file constructs that auxiliary graph `H` on `Bool ⊕ (Fin n × ZMod 3)`,
defines the parity bookkeeping `D` of a walk, proves the parity-lift lemma
(the formal content of the "after `c` steps we arrive at `v_{p-q mod 3}`"
argument), proves that a nonzero-`D` closed walk through `k` yields an `s`-`t`
path in `H` of length at most `2c+2`, and states the full iff of Lemma 1.

Boundary: the vertex set is `Fin n` with the label `u < v` reproducing the
paper's arbitrary orientation; cycles are represented by closed walks, which is
the precise object the parity argument uses.  Quantum/space claims of later
sections are not part of this file.
-/

set_option autoImplicit false

namespace Qatlib.Papers.TimeSpaceDet16.MainResults.SourceReduction

open SimpleGraph

variable {n : ℕ}

/-- Vertices of the ancillary graph `H`: `s = inl false`, `t = inl true`, and
the three split copies `(v,0), (v,1), (v,2)` of each `G`-vertex `v`
(arXiv:1610.00581v1, §3, p. 7: `V' = {s,t} ∪ {v_b}`). -/
abbrev AncVertex (n : ℕ) := Bool ⊕ (Fin n × ZMod 3)

/-- The source vertex `s` of the ancillary graph. -/
def sVertex (n : ℕ) : AncVertex n := Sum.inl false

/-- The sink vertex `t` of the ancillary graph. -/
def tVertex (n : ℕ) : AncVertex n := Sum.inl true

/-- The `b`-th split copy `v_b` of a vertex `v`. -/
def splitVertex {n : ℕ} (v : Fin n) (b : ZMod 3) : AncVertex n := Sum.inr (v, b)

/-- Moving along a directed edge `u → v` increments the parity label by `+1`
for a clockwise step and `-1` for an anticlockwise one
(arXiv:1610.00581v1, §3, p. 8: "the clockwise edges add 1 to the value of `d`,
and the anticlockwise edges add `-1`"). -/
def stepIndex {n : ℕ} (u v : Fin n) (b : ZMod 3) : ZMod 3 :=
  b + (if u < v then (1 : ZMod 3) else -1)

/-- Reversing a traversed edge reverses the parity increment. -/
theorem stepIndex_invol {n : ℕ} {u v : Fin n} (huv : u ≠ v) (b : ZMod 3) :
    stepIndex v u (stepIndex u v b) = b := by
  unfold stepIndex
  by_cases h : u < v
  · have h' : ¬ v < u := not_lt_of_ge h.le
    rw [if_pos h, if_neg h']
    ring
  · have h' : v < u := lt_of_le_of_ne (le_of_not_gt h) (Ne.symm huv)
    rw [if_neg h, if_pos h']
    ring

/-- The adjacency relation of the ancillary graph `H`
(arXiv:1610.00581v1, §3, p. 7):
`E' = {(u_b, v_{b+1 mod 3})} ∪ {(s,k₀), (t,k₁)}`. -/
def ancAdj (G : SimpleGraph (Fin n)) (k : Fin n) : AncVertex n → AncVertex n → Prop :=
  fun a b =>
    (a = sVertex n ∧ b = splitVertex k 0) ∨
    (a = splitVertex k 0 ∧ b = sVertex n) ∨
    (a = tVertex n ∧ b = splitVertex k 1) ∨
    (a = splitVertex k 1 ∧ b = tVertex n) ∨
    (∃ (u v : Fin n) (b0 : ZMod 3),
      G.Adj u v ∧ a = splitVertex u b0 ∧ b = splitVertex v (stepIndex u v b0))

/-- The ancillary graph is undirected: adjacency is symmetric. -/
theorem ancAdj_symm (G : SimpleGraph (Fin n)) (k : Fin n) :
    Symmetric (ancAdj G k) := by
  rintro a b (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨u, v, b0, hadj, rfl, rfl⟩)
  · exact Or.inr (Or.inl ⟨rfl, rfl⟩)
  · exact Or.inl ⟨rfl, rfl⟩
  · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, rfl⟩)))
  · exact Or.inr (Or.inr (Or.inl ⟨rfl, rfl⟩))
  · refine Or.inr (Or.inr (Or.inr (Or.inr ⟨v, u, stepIndex u v b0, hadj.symm, rfl, ?_⟩)))
    exact (congrArg (splitVertex u) (stepIndex_invol (G.ne_of_adj hadj) b0)).symm

/-- The ancillary graph is loopless. -/
theorem ancAdj_irrefl (G : SimpleGraph (Fin n)) (k : Fin n) :
    Std.Irrefl (ancAdj G k) :=
  ⟨fun a h => by
    rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨u, v, b0, hadj, h1, h2⟩
    · rw [h1] at h2; simp only [sVertex, splitVertex] at h2; exact nomatch h2
    · rw [h2] at h1; simp only [sVertex, splitVertex] at h1; exact nomatch h1
    · rw [h1] at h2; simp only [tVertex, splitVertex] at h2; exact nomatch h2
    · rw [h2] at h1; simp only [tVertex, splitVertex] at h1; exact nomatch h1
    · rw [h1] at h2
      simp only [splitVertex, Sum.inr.injEq, Prod.mk.injEq] at h2
      obtain ⟨rfl, -⟩ := h2
      exact G.irrefl hadj⟩

/-- The ancillary graph `H` of Lemma 1 (arXiv:1610.00581v1, §3, p. 7). -/
def ancGraph (G : SimpleGraph (Fin n)) (k : Fin n) : SimpleGraph (AncVertex n) where
  Adj := ancAdj G k
  symm := ⟨ancAdj_symm G k⟩
  loopless := ancAdj_irrefl G k

/-- Projection of an ancillary vertex to the underlying `G`-vertex together
with the parity label.  `s` and `t` are identified with `k₀` and `k₁`, the
unique split vertices adjacent to them, so that the special edges `s`-`k₀`
and `t`-`k₁` preserve the projection. -/
def ancProj (k : Fin n) : AncVertex n → Fin n × ZMod 3
  | Sum.inl false => (k, 0)
  | Sum.inl true => (k, 1)
  | Sum.inr p => p

/-- Every `G`-edge `{u,v}` gives a three-way split edge of `H`. -/
theorem ancGraph_adj_step {G : SimpleGraph (Fin n)} {k u v : Fin n}
    (h : G.Adj u v) (b : ZMod 3) :
    (ancGraph G k).Adj (splitVertex u b) (splitVertex v (stepIndex u v b)) := by
  show ancAdj G k _ _
  exact Or.inr (Or.inr (Or.inr (Or.inr ⟨u, v, b, h, rfl, rfl⟩)))

/-- The parity increment of a Dart under the paper's orientation: `+1` when the
dart runs from the smaller label to the larger, `-1` otherwise
(arXiv:1610.00581v1, §3, p. 7: "directing edges from `u → v` if `v > u`"). -/
def dartSign {n : ℕ} (u v : Fin n) : ZMod 3 :=
  if u < v then (1 : ZMod 3) else -1

/-- `stepIndex` is definitionally the parity label plus the dart sign. -/
theorem stepIndex_eq_add_dartSign {u v : Fin n} (b : ZMod 3) :
    stepIndex u v b = b + dartSign u v := rfl

/-- `D = p - q (mod 3)` of a walk: the sum of the signed contributions of its
darts (arXiv:1610.00581v1, §3, p. 8: "we will have traversed `p` clockwise
edges and `q` anticlockwise edges, and so we will arrive at vertex `v_{p-q
mod 3}`"). -/
def walkDiff {G : SimpleGraph (Fin n)} {u v : Fin n} (p : G.Walk u v) : ZMod 3 :=
  (p.darts.map (fun d => dartSign d.fst d.snd)).sum

/-- The empty walk has `D = 0`. -/
@[simp] theorem walkDiff_nil {G : SimpleGraph (Fin n)} {u : Fin n} :
    walkDiff (G := G) (Walk.nil : G.Walk u u) = 0 := rfl

/-- A prepended dart contributes its sign to `D`. -/
theorem walkDiff_cons {G : SimpleGraph (Fin n)} {u v w : Fin n}
    (h : G.Adj u v) (p : G.Walk v w) :
    walkDiff (G := G) (Walk.cons h p) = dartSign u v + walkDiff p := by
  unfold walkDiff
  rw [Walk.darts_cons, List.map_cons, List.sum_cons]

/-- `D` is additive under concatenation of walks. -/
theorem walkDiff_append {G : SimpleGraph (Fin n)} {u v w : Fin n}
    (p : G.Walk u v) (q : G.Walk v w) :
    walkDiff (G := G) (p.append q) = walkDiff p + walkDiff q := by
  unfold walkDiff
  rw [Walk.darts_append, List.map_append, List.sum_append]

/-- **Projection lemma, length induction**: an `H`-walk from `a` to `b`
projects to a `G`-walk between the projected vertices, and the parity label
changes exactly by the `D`-value of that `G`-walk.  The proof is an induction on
the `H`-walk length that peels the last edge; the special edges `s`-`k₀` and
`t`-`k₁` leave both the projected vertex and the parity label unchanged. -/
theorem walk_proj_aux {G : SimpleGraph (Fin n)} {k : Fin n} :
    ∀ (L : ℕ) {a b : AncVertex n} (q : (ancGraph G k).Walk a b), q.length = L →
      ∃ p : G.Walk (ancProj k a).1 (ancProj k b).1,
        (ancProj k a).2 + walkDiff p = (ancProj k b).2 := by
  intro L
  induction L using Nat.strong_induction_on with
  | _ L ih =>
    intro a b q hL
    cases q with
    | nil => exact ⟨Walk.nil, by simp⟩
    | cons h q' =>
        have hlt : q'.length < L := by
          simp only [Walk.length_cons] at hL
          omega
        rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ |
          ⟨u, v, b0, hadj, h1, h2⟩
        · obtain ⟨p', hp'⟩ := ih q'.length hlt q' rfl
          subst h1; subst h2
          exact ⟨p', by simpa [ancProj, sVertex, splitVertex] using hp'⟩
        · obtain ⟨p', hp'⟩ := ih q'.length hlt q' rfl
          subst h1; subst h2
          exact ⟨p', by simpa [ancProj, sVertex, splitVertex] using hp'⟩
        · obtain ⟨p', hp'⟩ := ih q'.length hlt q' rfl
          subst h1; subst h2
          exact ⟨p', by simpa [ancProj, tVertex, splitVertex] using hp'⟩
        · obtain ⟨p', hp'⟩ := ih q'.length hlt q' rfl
          subst h1; subst h2
          exact ⟨p', by simpa [ancProj, tVertex, splitVertex] using hp'⟩
        · obtain ⟨p', hp'⟩ := ih q'.length hlt q' rfl
          subst h1; subst h2
          refine ⟨Walk.cons hadj p', ?_⟩
          rw [walkDiff_cons]
          simp only [ancProj, splitVertex] at hp' ⊢
          rw [← add_assoc]
          simpa [stepIndex, dartSign] using hp'

/-- **Projection lemma** (converse direction of Lemma 1): every `s`-`t` walk in
`H` projects to a closed walk of `G` whose parity is `1`, hence nonzero. -/
theorem walk_proj {G : SimpleGraph (Fin n)} {k : Fin n} {a b : AncVertex n}
    (q : (ancGraph G k).Walk a b) :
    ∃ p : G.Walk (ancProj k a).1 (ancProj k b).1,
      (ancProj k a).2 + walkDiff p = (ancProj k b).2 :=
  walk_proj_aux q.length q rfl

/-- **Parity lift lemma** (arXiv:1610.00581v1, §3, p. 8, first paragraph of the
proof of Lemma 1): a walk `p` in `G` from `u` to `v` lifts to a walk of `H`
from `(u,b)` to `(v, b + D(p))` of the same length. -/
theorem ancWalk_lift {G : SimpleGraph (Fin n)} (k : Fin n) :
    ∀ {u v : Fin n} (p : G.Walk u v) (b : ZMod 3),
      ∃ q : (ancGraph G k).Walk (splitVertex u b) (splitVertex v (b + walkDiff p)),
        q.length = p.length := by
  intro u v p
  induction p with
  | nil =>
      intro b
      exact ⟨(Walk.nil).copy rfl (by simp), by simp⟩
  | cons h p ih =>
      intro b
      obtain ⟨q, hq⟩ := ih (b + dartSign _ _)
      refine ⟨(Walk.cons ?_ q).copy rfl (congrArg (splitVertex _) (add_assoc b _ _)), ?_⟩
      · simpa [stepIndex, dartSign] using ancGraph_adj_step (G := G) (k := k) h b
      · rw [Walk.length_copy, Walk.length_cons, Walk.length_cons, hq]

/-- In `ZMod 3` the only nonzero residues are `1` and `2`. -/
theorem zmod3_eq_one_or_two {d : ZMod 3} (h : d ≠ 0) : d = 1 ∨ d = 2 := by
  have hd : ∀ d : ZMod 3, d = 0 ∨ d = 1 ∨ d = 2 := by decide
  rcases hd d with h0 | h1 | h2
  · exact absurd h0 h
  · exact Or.inl h1
  · exact Or.inr h2

/-- In `ZMod 3`, `2 + 2 = 1`. -/
theorem zmod3_two_add_two : (2 : ZMod 3) + 2 = 1 := by decide

/-- **Cycle traversal path** (arXiv:1610.00581v1, §3, p. 8: "if `p - q = D
≢ 0 mod 3` ... traversing the cycle ... we arrive at `v_{2D mod 3}` ...
Therefore, we have a path from `v₀` to `v_b` for some `b ∈ {1,2}`, from `v_b` to
`v_{b'}`, ... The length of the path from `v_b` to `v_{b'}` in `H` is then at
most `2c`"): a closed walk through `k` with `D ≠ 0` gives a path from `k₀` to
`k₁` in `H` of length at most twice the walk length. -/
theorem cycle_path_le_two_mul {G : SimpleGraph (Fin n)} {k : Fin n}
    {p : G.Walk k k} (hp : walkDiff p ≠ 0) :
    ∃ q : (ancGraph G k).Walk (splitVertex k 0) (splitVertex k 1),
      q.length ≤ 2 * p.length := by
  rcases zmod3_eq_one_or_two hp with h1 | h2
  · obtain ⟨q0, hq0⟩ := ancWalk_lift (G := G) k p 0
    refine ⟨q0.copy rfl (congrArg (splitVertex k) (by rw [zero_add, h1])), ?_⟩
    rw [Walk.length_copy, hq0]
    omega
  · obtain ⟨q0, hq0⟩ := ancWalk_lift (G := G) k p 0
    obtain ⟨q1, hq1⟩ := ancWalk_lift (G := G) k p (walkDiff p)
    have hq0' : (q0.copy rfl (congrArg (splitVertex k) (zero_add (walkDiff p)))).length
        = p.length := by rw [Walk.length_copy, hq0]
    refine ⟨((q0.copy rfl (congrArg (splitVertex k) (zero_add (walkDiff p)))).append q1).copy rfl
      (congrArg (splitVertex k) ?_), ?_⟩
    · rw [h2]
      exact zmod3_two_add_two
    · rw [Walk.length_copy, Walk.length_append, hq0', hq1]
      omega

/-- **Lemma 1, length bound** (arXiv:1610.00581v1, Lemma 1, p. 8: "if `k` is
chosen to be a vertex on the cycle, then the length of the path between `s` and
`t` is at most `2c + 2`, where `c` is the length of the cycle"): from a closed
walk of length `c` through `k` with `D ≠ 0`, `H` has an `s`-`t` walk of length at
most `2c + 2`. -/
theorem path_s_to_t_length {G : SimpleGraph (Fin n)} {k : Fin n}
    {p : G.Walk k k} (hp : walkDiff p ≠ 0) :
    ∃ q : (ancGraph G k).Walk (sVertex n) (tVertex n), q.length ≤ 2 * p.length + 2 := by
  obtain ⟨mid, hmid⟩ := cycle_path_le_two_mul (G := G) (k := k) hp
  have hs : (ancGraph G k).Adj (sVertex n) (splitVertex k 0) := Or.inl ⟨rfl, rfl⟩
  have ht : (ancGraph G k).Adj (splitVertex k 1) (tVertex n) :=
    Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, rfl⟩)))
  refine ⟨Walk.cons hs (mid.append (Walk.cons ht Walk.nil)), ?_⟩
  rw [Walk.length_cons, Walk.length_append, Walk.length_cons, Walk.length_nil]
  omega

/-- **Lemma 1, forward direction** (arXiv:1610.00581v1, §3, p. 8: "Since `G` is
connected, there must be a path from `1` to `2` in `G`. By following the edges
of this path, we can find a corresponding path in `H` from `1₀` to `2_b` and
from `1₁` to `2_{b+1 mod 3}`, for some `b`... there must also exist a path from
`1₀` to `1₁`"): if `G` is connected and has a closed walk with `D ≠ 0`, then
`s` and `t` are connected in `H`. -/
theorem forward_reachable {G : SimpleGraph (Fin n)} {k : Fin n} (hG : G.Preconnected)
    {u : Fin n} {p : G.Walk u u} (hp : walkDiff p ≠ 0) :
    (ancGraph G k).Reachable (sVertex n) (tVertex n) := by
  obtain ⟨w⟩ := hG k u
  obtain ⟨w0, -⟩ := ancWalk_lift (G := G) k w 0
  obtain ⟨w1, -⟩ := ancWalk_lift (G := G) k w 1
  have hbridge : (ancGraph G k).Reachable (splitVertex u (0 + walkDiff w))
      (splitVertex u (1 + walkDiff w)) := by
    rcases zmod3_eq_one_or_two hp with h1 | h2
    · obtain ⟨q, -⟩ := ancWalk_lift (G := G) k p (0 + walkDiff w)
      exact ⟨q.copy rfl (congrArg (splitVertex u) (by rw [h1]; ring))⟩
    · obtain ⟨q1, -⟩ := ancWalk_lift (G := G) k p (0 + walkDiff w)
      obtain ⟨q2, -⟩ := ancWalk_lift (G := G) k p ((0 + walkDiff w) + walkDiff p)
      refine ⟨(q1.append q2).copy rfl (congrArg (splitVertex u) ?_)⟩
      rw [h2, add_assoc ((0 : ZMod 3) + walkDiff w) 2 2, zmod3_two_add_two, zero_add, add_comm]
  obtain ⟨bridge⟩ := hbridge
  have hs : (ancGraph G k).Adj (sVertex n) (splitVertex k 0) := Or.inl ⟨rfl, rfl⟩
  have ht : (ancGraph G k).Adj (splitVertex k 1) (tVertex n) :=
    Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, rfl⟩)))
  exact ⟨Walk.cons hs (w0.append (bridge.append (w1.reverse.append (Walk.cons ht Walk.nil))))⟩

/-- **Lemma 1, converse** (arXiv:1610.00581v1, §3, p. 9: "if `G` does not
contain a cycle, or if it contains a cycle such that `D = p - q ≡ 0 mod 3`, then
`s` and `t` are not connected in `H`"): an `s`-`t` walk in `H` projects, via
`ancProj`, to a closed walk of `G` from `k` to `k` whose parity label changes
from `0` at `k₀` to `1` at `k₁`; hence its `D`-value is `1 ≠ 0`. -/
theorem backward_cycle {G : SimpleGraph (Fin n)} {k : Fin n}
    (h : (ancGraph G k).Reachable (sVertex n) (tVertex n)) :
    ∃ (u : Fin n) (p : G.Walk u u), walkDiff p ≠ 0 := by
  obtain ⟨q⟩ := h
  obtain ⟨p, hp⟩ := walk_proj (G := G) (k := k) q
  refine ⟨k, p, ?_⟩
  intro hzero
  have hp1 : (0 : ZMod 3) = 1 := by
    simp [ancProj, sVertex, tVertex, hzero] at hp
  exact zero_ne_one hp1

/-- **Lemma 1** (arXiv:1610.00581v1, §3, Lemma 1, p. 8): for a connected graph
`G`, the ancillary graph `H` has an `s`-`t` path iff `G` has a closed walk with
`D ≢ 0 mod 3`; moreover a closed walk of length `c` through `k` with `D ≢ 0`
gives an `s`-`t` path in `H` of length at most `2c + 2`. -/
theorem lemma1_ancillary_reduction (G : SimpleGraph (Fin n)) (k : Fin n)
    (hG : G.Preconnected) :
    ((∃ (u : Fin n) (p : G.Walk u u), walkDiff p ≠ 0) ↔
        (ancGraph G k).Reachable (sVertex n) (tVertex n)) ∧
      (∀ (c : ℕ) (p : G.Walk k k), p.length = c → walkDiff p ≠ 0 →
        ∃ q : (ancGraph G k).Walk (sVertex n) (tVertex n), q.length ≤ 2 * c + 2) := by
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · rintro ⟨u, p, hp⟩
    exact forward_reachable (G := G) (k := k) hG hp
  · exact backward_cycle
  · intro c p hc hp
    obtain ⟨q, hq⟩ := path_s_to_t_length (G := G) (k := k) hp
    exact ⟨q, by rw [hc] at hq; omega⟩

end Qatlib.Papers.TimeSpaceDet16.MainResults.SourceReduction
