/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Papers.GraphConnect03.MainResults.Model.ConnectivityModel
public import Qatlib.Papers.GraphConnect03.MainResults.LowerBounds.AmbainisMethod

@[expose] public section


/-!
# Theorem5MatrixConnectivity — the lower bound of Theorem 5

[DurrMhallaLei2003], Theorem 5 and Figure 3 (p. 8).

Theorem 5: Connectivity needs `Ω(n^{3/2})` queries in the adjacency-matrix
model (even for undirected graphs).

The source applies Ambainis' method to the promise problem of distinguishing a
graph with exactly one cycle from a graph with exactly two cycles of lengths in
`[n/3, 2n/3]`.  `X` is the set of adjacency matrices of a unique cycle, `Y` the
set of adjacency matrices with exactly two such cycles, and `M R M′` when the
only differences are four edges: `(a,b), (c,d)` present in `M` and absent in
`M′`, `(a,c), (b,d)` absent in `M` and present in `M′` (a 2-switch along the
cycle, Figure 3). The argument uses degree lower bounds of order `n²` in
both directions and a uniform `O(n)` bound on the changed-coordinate load
product. At a changed entry, one load is at most `4` and the other is
at most linear. These estimates give `√(m m′/l_max) = Ω(n^{3/2})`.

This file records properties of the 2-switch and of the two promise classes.
The arithmetic evaluation is provided by
`Qatlib.Papers.GraphConnect03.MainResults.LowerBounds.sqrt_matrix_parameters`.
The relation degrees, load counts, and query lower bound remain open here.

## Main statements

* `matrixEdgeSwapRel_symm`: the Figure 3 2-switch relation is symmetric.
* `matrixEdgeSwapRel_twoRegular`: a 2-switch preserves 2-regularity, hence
  sends a unique cycle to a 2-regular graph and preserves the degree promise
  on the two-cycle side.
* `twoCycles_componentSize_add`: in a two-cycle input the two components
  partition all vertices, so their sizes add up to `n`.
* `twoCycles_not_uniqueCycle`: the two-cycle and unique-cycle sides of the
  promise problem are disjoint.
-/

set_option autoImplicit false
set_option maxHeartbeats 800000
noncomputable section

namespace Qatlib.Papers.GraphConnect03.MainResults.LowerBounds

open Qatlib.Papers.GraphConnect03.MainResults Qatlib.Papers.GraphConnect03.MainResults

open Classical
open Qatlib.Papers.GraphConnect03.MainResults.Model

attribute [local instance] Classical.propDecidable

/-- `TwoRegular M`: every vertex has exactly two neighbours, i.e. the graph is a
disjoint union of cycles. -/
def TwoRegular {n : ℕ} (M : UndirectedMatrix n) : Prop :=
  ∀ v : Vertex n, (Finset.univ.filter (fun w => M.adj v w = true)).card = 2

/-- `UniqueCycle M`: a nonempty, 2-regular connected graph, the unique
spanning cycle side of the source's promise problem. -/
def UniqueCycle {n : ℕ} (M : UndirectedMatrix n) : Prop :=
  TwoRegular M ∧ 0 < n ∧ M.Connected

/-- Number of vertices in the connected component of `v`. -/
def componentSize {n : ℕ} (M : UndirectedMatrix n) (v : Vertex n) : ℕ :=
  (Finset.univ.filter (fun w => M.toDigraph.Reach v w)).card

/-- Exactly two connected cycles, each of size between `n/3` and `2n/3`.
Every vertex must belong to one of the two specified components. -/
def TwoCycles {n : ℕ} (M : UndirectedMatrix n) : Prop :=
  TwoRegular M ∧ ¬ M.Connected ∧
    ∃ v w : Vertex n, ¬ M.toDigraph.Reach v w ∧
      (∀ u, M.toDigraph.Reach v u ∨ M.toDigraph.Reach w u) ∧
      3 * componentSize M v ≥ n ∧ 3 * componentSize M v ≤ 2 * n ∧
      3 * componentSize M w ≥ n ∧ 3 * componentSize M w ≤ 2 * n

/-- The edge-change predicate of Theorem 5 (Figure 3): the four changed edges
are `(a,b), (c,d)` in `M` versus `(a,c), (b,d)` in `M′`, with four distinct
vertices. The source relation additionally restricts the endpoints to the
unique-cycle and balanced two-cycle promise classes, respectively. -/
def MatrixEdgeSwapRel {n : ℕ} (M M' : UndirectedMatrix n) : Prop :=
  ∃ a b c d : Vertex n,
    a ≠ b ∧ a ≠ c ∧ a ≠ d ∧ b ≠ c ∧ b ≠ d ∧ c ≠ d ∧
    M.adj a b = true ∧ M.adj c d = true ∧
    M'.adj a b = false ∧ M'.adj c d = false ∧
    M'.adj a c = true ∧ M'.adj b d = true ∧
    M.adj a c = false ∧ M.adj b d = false ∧
    -- all other entries agree
    (∀ i j : Vertex n,
      ¬ ((i = a ∧ j = b) ∨ (i = b ∧ j = a) ∨ (i = c ∧ j = d) ∨ (i = d ∧ j = c) ∨
         (i = a ∧ j = c) ∨ (i = c ∧ j = a) ∨ (i = b ∧ j = d) ∨ (i = d ∧ j = b)) →
      M'.adj i j = M.adj i j)

/-- The Figure 3 2-switch relation is symmetric: swapping the roles of the
two removed edges `(a,b), (c,d)` and the two inserted edges `(a,c), (b,d)`
exchanges the two sides of the relation. -/
theorem matrixEdgeSwapRel_symm {n : ℕ} {M M' : UndirectedMatrix n}
    (h : MatrixEdgeSwapRel M M') : MatrixEdgeSwapRel M' M := by
  obtain ⟨a, b, c, d, hab, hac, had, hbc, hbd, hcd, habM, hcdM, habM', hcdM',
    hacM', hbdM', hacM, hbdM, hagree⟩ := h
  refine ⟨a, c, b, d, hac, hab, had, Ne.symm hbc, hcd, hbd, hacM', hbdM',
    hacM, hbdM, habM, hcdM, habM', hcdM', ?_⟩
  intro i j hij
  exact (hagree i j (fun hh => hij (by
    rcases hh with ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ |
      ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> simp_all))).symm

/-- Related matrices of Theorem 5 are distinct: at the removed entry `(a,b)`
the first matrix has `true` and the second has `false`. -/
theorem matrixEdgeSwapRel_ne {n : ℕ} {M M' : UndirectedMatrix n}
    (h : MatrixEdgeSwapRel M M') : M ≠ M' := by
  obtain ⟨a, b, c, d, -, -, -, -, -, -, habM, -, habM', -, -, -, -, -,
    -⟩ := h
  intro hMM
  subst hMM
  rw [habM] at habM'
  exact Bool.noConfusion habM'

/-- A Figure 3 2-switch preserves 2-regularity.  At each of the four moved
vertices exactly one incident edge is removed and one is inserted; at every
other vertex the neighbourhood is unchanged.  Hence the degree promise of
both sides of the Theorem 5 promise problem is preserved by the relation. -/
theorem matrixEdgeSwapRel_twoRegular {n : ℕ} {M M' : UndirectedMatrix n}
    (h : MatrixEdgeSwapRel M M') (hM : TwoRegular M) : TwoRegular M' := by
  obtain ⟨a, b, c, d, hab, hac, had, hbc, hbd, hcd, habM, hcdM, habM', hcdM',
    hacM', hbdM', hacM, hbdM, hagree⟩ := h
  have habM_rev : M.adj b a = true := by rw [← M.symm a b]; exact habM
  have hcdM_rev : M.adj d c = true := by rw [← M.symm c d]; exact hcdM
  have hacM_rev : M.adj c a = false := by rw [← M.symm a c]; exact hacM
  have hbdM_rev : M.adj d b = false := by rw [← M.symm b d]; exact hbdM
  have habM'_rev : M'.adj b a = false := by rw [← M'.symm a b]; exact habM'
  have hcdM'_rev : M'.adj d c = false := by rw [← M'.symm c d]; exact hcdM'
  have hacM'_rev : M'.adj c a = true := by rw [← M'.symm a c]; exact hacM'
  have hbdM'_rev : M'.adj d b = true := by rw [← M'.symm b d]; exact hbdM'
  have hba : b ≠ a := Ne.symm hab
  have hca : c ≠ a := Ne.symm hac
  have hda : d ≠ a := Ne.symm had
  have hcb : c ≠ b := Ne.symm hbc
  have hdb : d ≠ b := Ne.symm hbd
  have hdc : d ≠ c := Ne.symm hcd
  have swap_card : ∀ (S : Finset (Vertex n)) (x y : Vertex n),
      x ∈ S → y ∉ S → x ≠ y → (insert y (S.erase x)).card = S.card := by
    intro S x y hx hy hxy
    have hpos : 0 < S.card := Finset.card_pos.mpr ⟨x, hx⟩
    rw [Finset.card_insert_of_notMem (by
      simp only [Finset.mem_erase, not_and]
      intro _; exact hy), Finset.card_erase_of_mem hx]
    omega
  intro v
  by_cases hva : v = a
  · rw [hva]
    have hset : (Finset.univ.filter (fun w => M'.adj a w = true)) =
        insert c ((Finset.univ.filter (fun w => M.adj a w = true)).erase b) := by
      apply Finset.ext
      intro w
      simp only [Finset.mem_filter, Finset.mem_univ, true_and,
        Finset.mem_insert, Finset.mem_erase]
      by_cases hwb : w = b
      · rw [hwb]; simp [habM', habM, hbc]
      · by_cases hwc : w = c
        · rw [hwc]; simp [hacM', hacM, hcb]
        · have hag := hagree a w (by
            rintro (⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ |
              ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩) <;>
              simp_all)
          rw [hag]; simp [hwb, hwc]
    rw [hset, swap_card _ b c (by simp [habM]) (by simp [hacM]) hbc,
      hM a]
  · by_cases hvb : v = b
    · rw [hvb]
      have hset : (Finset.univ.filter (fun w => M'.adj b w = true)) =
          insert d ((Finset.univ.filter (fun w => M.adj b w = true)).erase a) := by
        apply Finset.ext
        intro w
        simp only [Finset.mem_filter, Finset.mem_univ, true_and,
          Finset.mem_insert, Finset.mem_erase]
        by_cases hwa : w = a
        · rw [hwa]; simp [habM'_rev, habM_rev, had]
        · by_cases hwd : w = d
          · rw [hwd]; simp [hbdM', hbdM, hda]
          · have hag := hagree b w (by
              rintro (⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ |
                ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩) <;>
                simp_all)
            rw [hag]; simp [hwa, hwd]
      rw [hset, swap_card _ a d (by simp [habM_rev]) (by simp [hbdM]) had,
        hM b]
    · by_cases hvc : v = c
      · rw [hvc]
        have hset : (Finset.univ.filter (fun w => M'.adj c w = true)) =
            insert a ((Finset.univ.filter (fun w => M.adj c w = true)).erase d) := by
          apply Finset.ext
          intro w
          simp only [Finset.mem_filter, Finset.mem_univ, true_and,
            Finset.mem_insert, Finset.mem_erase]
          by_cases hwd : w = d
          · rw [hwd]; simp [hcdM', hcdM, hda]
          · by_cases hwa : w = a
            · rw [hwa]; simp [hacM'_rev, hacM_rev, had]
            · have hag := hagree c w (by
                rintro (⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ |
                  ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩) <;>
                  simp_all)
              rw [hag]; simp [hwd, hwa]
        rw [hset, swap_card _ d a (by simp [hcdM]) (by simp [hacM_rev])
          hda, hM c]
      · by_cases hvd : v = d
        · rw [hvd]
          have hset : (Finset.univ.filter (fun w => M'.adj d w = true)) =
              insert b ((Finset.univ.filter (fun w => M.adj d w = true)).erase c) := by
            apply Finset.ext
            intro w
            simp only [Finset.mem_filter, Finset.mem_univ, true_and,
              Finset.mem_insert, Finset.mem_erase]
            by_cases hwc : w = c
            · rw [hwc]; simp [hcdM'_rev, hcdM_rev, hcb]
            · by_cases hwb : w = b
              · rw [hwb]; simp [hbdM'_rev, hbdM_rev, hbc]
              · have hag := hagree d w (by
                  rintro (⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ |
                    ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩) <;>
                    simp_all)
                rw [hag]; simp [hwc, hwb]
          rw [hset, swap_card _ c b (by simp [hcdM_rev]) (by simp [hbdM_rev])
            hcb, hM d]
        · have hset : (Finset.univ.filter (fun w => M'.adj v w = true)) =
              Finset.univ.filter (fun w => M.adj v w = true) := by
            apply Finset.ext
            intro w
            simp only [Finset.mem_filter, Finset.mem_univ, true_and]
            have hag := hagree v w (by
              rintro (⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ |
                ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩) <;>
                simp_all)
            rw [hag]
          rw [hset, hM v]

/-- In a two-cycle input the two balanced components partition the vertex
set: the witnesses of `TwoCycles` satisfy `componentSize v + componentSize w
= n`, together with the source's `[n/3, 2n/3]` size window.  This is the
counting step that makes the two sides of the Theorem 5 promise disjoint in
size from a single spanning cycle component. -/
theorem twoCycles_componentSize_add {n : ℕ} {M : UndirectedMatrix n}
    (h : TwoCycles M) :
    ∃ v w : Vertex n, ¬ M.toDigraph.Reach v w ∧
      componentSize M v + componentSize M w = n ∧
      3 * componentSize M v ≥ n ∧ 3 * componentSize M v ≤ 2 * n ∧
      3 * componentSize M w ≥ n ∧ 3 * componentSize M w ≤ 2 * n := by
  obtain ⟨-, -, v, w, hnw, hcover, hv1, hv2, hw1, hw2⟩ := h
  refine ⟨v, w, hnw, ?_, hv1, hv2, hw1, hw2⟩
  have hunion : (Finset.univ.filter (fun u => M.toDigraph.Reach v u)) ∪
        (Finset.univ.filter (fun u => M.toDigraph.Reach w u)) =
      Finset.univ := by
    apply Finset.eq_univ_of_forall
    intro u
    simp only [Finset.mem_union, Finset.mem_filter, Finset.mem_univ,
      true_and]
    exact hcover u
  have hdisj : Disjoint (Finset.univ.filter (fun u => M.toDigraph.Reach v u))
      (Finset.univ.filter (fun u => M.toDigraph.Reach w u)) := by
    rw [Finset.disjoint_left]
    intro u hu1 hu2
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hu1 hu2
    exact hnw (hu1.trans (M.reach_symm hu2))
  unfold componentSize
  rw [← Finset.card_union_of_disjoint hdisj, hunion]
  simp

/-- The two sides of the Theorem 5 promise problem are disjoint: no matrix
is both a unique spanning cycle and a pair of balanced cycles. -/
theorem twoCycles_not_uniqueCycle {n : ℕ} {M : UndirectedMatrix n}
    (h : TwoCycles M) : ¬ UniqueCycle M := by
  intro hU
  exact h.2.1 hU.2.2

/- The relation-parameter counts of Theorem 5 are not stated as a
declaration: they require the 2-switch
counting on the unique-cycle vs two-cycle promise problem, which is not
mechanized.  The arithmetic evaluation `√(m m′/l_max) = n^{3/2}` at the source's
parameter values is proved in the imported `AmbainisMethod` module. -/

/- Source Theorem 5 (`Ω(n^{3/2})` matrix-model Connectivity lower bound) is not
stated as a declaration.  Its ingredients are: the promise relations
(`UniqueCycle`, `TwoCycles`, `MatrixEdgeSwapRel`), the relation-parameter counts
(recorded gap above), the abstract Ambainis relation bound (see `AmbainisMethod`),
and the passage to `Model.matrixConnectivityQueryComplexity`, which needs the
operational circuit semantics this block does not rebuild. -/

end Qatlib.Papers.GraphConnect03.MainResults.LowerBounds
