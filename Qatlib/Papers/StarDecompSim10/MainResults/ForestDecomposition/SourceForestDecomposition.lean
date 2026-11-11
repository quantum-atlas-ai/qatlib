/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Tactic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Inverse
import Mathlib.Analysis.Normed.Algebra.MatrixExponential
import Mathlib.Analysis.Asymptotics.Lemmas
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Basic

set_option backward.isDefEq.respectTransparency false

/-!
# SourceForestDecomposition — Lemma 1 (forest decomposition)

Fixed version: arXiv:1003.3683v2 (5 Nov 2010), Childs--Kothari, "Simulating
sparse Hamiltonians with star decompositions", §4, Lemma 1, pages 5--6.

The paper models a Hamiltonian by its graph: a black-box oracle
`f(x,i) = (y, H x y)` lists, for every row `x` and slot `i < d`, the `i`-th
neighbour `y` of `x` (or reports that the row has fewer than `i` entries).
Lemma 1 colours every edge by the *proposal of its higher-labelled endpoint*
(vertex `x` proposes slot `i` for the edge to `f(x,i)`) and directs each edge
from the lower- to the higher-labelled endpoint.  It then proves:

* `H = Σ_{c=1}^d H_c` where `H_c` is the sub-Hamiltonian on the colour-`c`
  edges (here `weight_decomposition`);
* each `H_c` is a forest of arborescences (`color_class_is_forest`);
* the parent of `v` in `H_c` is the `c`-th neighbour of `v` when that
  neighbour has smaller label (else `v` is a root), so one oracle query
  suffices (`parent_one_query`);
* the edges of `H_c` incident on `v` are computable with at most `2d`
  oracle queries (`incEdges_two_d_queries`).

The oracle model below is deliberately minimal but honest: it keeps the
symmetry of the Hamiltonian graph and the uniqueness of each neighbour in a
row, which are exactly the two properties used by the paper's argument.
-/

set_option autoImplicit false

noncomputable section

namespace Qatlib.Papers.StarDecompSim10.MainResults.ForestDecomposition

open Finset

variable {N d : ℕ}

/-- The row-wise neighbour oracle of §3: `nbr x i` is the `i`-th nonzero
column of row `x`.  Rows are symmetric (if `y` is listed in row `x` then `x`
is listed in row `y`) and each neighbour occurs at most once in a row. -/
structure SparseOrb (N d : ℕ) where
  nbr : Fin N → Fin d → Option (Fin N)
  nbr_symm : ∀ {x : Fin N} {i : Fin d} {y : Fin N},
    nbr x i = some y → ∃ j, nbr y j = some x
  nbr_row_inj : ∀ {x : Fin N} {i j : Fin d} {y : Fin N},
    nbr x i = some y → nbr x j = some y → i = j

/-- `O` lists exactly the edges of the simple graph `G`. -/
structure ListsGraph (O : SparseOrb N d) (G : SimpleGraph (Fin N)) : Prop where
  adj_of_nbr : ∀ {x : Fin N} {i : Fin d} {y : Fin N},
    O.nbr x i = some y → G.Adj x y
  exists_nbr_of_adj : ∀ {x y : Fin N}, G.Adj x y → ∃ i, O.nbr x i = some y

/-! ## Slot lookup and the proposal colouring -/

/-- The slot at which row `x` lists `y`, if any. -/
def slot (O : SparseOrb N d) (x y : Fin N) : Option (Fin d) :=
  if h : ∃ i, O.nbr x i = some y then some (Classical.choose h) else none

/-- Reading back a listed slot. -/
theorem nbr_slot (O : SparseOrb N d) {x y : Fin N} {i : Fin d}
    (h : slot O x y = some i) : O.nbr x i = some y := by
  unfold slot at h
  by_cases hex : ∃ j, O.nbr x j = some y
  · rw [dif_pos hex] at h
    have hci : Classical.choose hex = i := by simpa using h
    rw [← hci]
    exact Classical.choose_spec hex
  · rw [dif_neg hex] at h
    exact absurd h (by simp)

/-- A listed slot is *the* slot of that neighbour (row uniqueness). -/
theorem slot_unique (O : SparseOrb N d) {x y : Fin N} {i : Fin d}
    (h : O.nbr x i = some y) : slot O x y = some i := by
  unfold slot
  rw [dif_pos ⟨i, h⟩]
  have hspec : O.nbr x (Classical.choose (⟨i, h⟩ : ∃ j, O.nbr x j = some y)) = some y :=
    Classical.choose_spec (⟨i, h⟩ : ∃ j, O.nbr x j = some y)
  have hci : Classical.choose (⟨i, h⟩ : ∃ j, O.nbr x j = some y) = i :=
    O.nbr_row_inj hspec h
  rw [hci]

/-- The colour of an edge: the proposal of its higher-labelled endpoint. -/
def edgeColor (O : SparseOrb N d) (x y : Fin N) : Option (Fin d) :=
  slot O (max x y) (min x y)

/-- For `x < y`, an edge `xy` has colour `c` exactly when `y` proposes `c`. -/
theorem edgeColor_eq_some_iff (O : SparseOrb N d) {x y : Fin N} (hxy : x < y)
    (c : Fin d) : edgeColor O x y = some c ↔ O.nbr y c = some x := by
  unfold edgeColor
  rw [max_eq_right (le_of_lt hxy), min_eq_left (le_of_lt hxy)]
  exact ⟨fun h => nbr_slot O h, fun h => slot_unique O h⟩

/-- Colours are symmetric in the endpoints. -/
theorem edgeColor_comm (O : SparseOrb N d) (x y : Fin N) :
    edgeColor O x y = edgeColor O y x := by
  unfold edgeColor
  rw [max_comm, min_comm]

/-- A vertex is never its own neighbour, so its self-edge has no colour. -/
theorem edgeColor_self_eq_none (O : SparseOrb N d) {G : SimpleGraph (Fin N)} (hG : ListsGraph O G) (x : Fin N) :
    edgeColor O x x = none := by
  unfold edgeColor
  rw [max_self, min_self]
  unfold slot
  rw [dif_neg]
  intro ⟨i, hi⟩
  exact G.irrefl (hG.adj_of_nbr hi)

/-- A non-edge has no colour. -/
theorem edgeColor_of_not_adj (O : SparseOrb N d) {G : SimpleGraph (Fin N)} (hG : ListsGraph O G) {x y : Fin N}
    (hxy : x < y) (h : ¬ G.Adj x y) : edgeColor O x y = none := by
  unfold edgeColor
  rw [max_eq_right (le_of_lt hxy), min_eq_left (le_of_lt hxy)]
  unfold slot
  rw [dif_neg]
  intro ⟨i, hi⟩
  exact h (hG.adj_of_nbr hi).symm

/-! ## The weight decomposition `H = Σ_c H_c` -/

/-- The colour-`c` part of the weight matrix. -/
def colorWeight (O : SparseOrb N d) (c : Fin d) (w : Fin N → Fin N → ℂ)
    (x y : Fin N) : ℂ :=
  if edgeColor O x y = some c then w x y else 0

/-- **Lemma 1, first part**: the matrix (weight function) is the sum of its
`d` colour classes.  The paper's `H = Σ_{c=1}^d H_c`. -/
theorem weight_decomposition (O : SparseOrb N d) {G : SimpleGraph (Fin N)} (hG : ListsGraph O G)
    (w : Fin N → Fin N → ℂ) (hw : ∀ x y, ¬ G.Adj x y → w x y = 0) (x y : Fin N) :
    w x y = ∑ c : Fin d, colorWeight O c w x y := by
  by_cases hxy : x = y
  · subst hxy
    rw [hw x x G.irrefl]
    symm
    refine Finset.sum_eq_zero ?_
    intro c _
    simp [colorWeight, edgeColor_self_eq_none O hG x]
  · rcases lt_or_gt_of_ne hxy with hlt | hgt
    · by_cases hadj : G.Adj x y
      · obtain ⟨i, hi⟩ : ∃ i, O.nbr y i = some x := hG.exists_nbr_of_adj hadj.symm
        have he : edgeColor O x y = some i := (edgeColor_eq_some_iff O hlt i).mpr hi
        rw [Finset.sum_eq_single i]
        · simp [colorWeight, he]
        · intro b _ hb
          simp only [colorWeight, he]
          rw [if_neg (by simp only [Option.some.injEq]; exact fun h => hb h.symm)]
        · intro hi'
          exact absurd (Finset.mem_univ i) hi'
      · rw [hw x y hadj]
        symm
        refine Finset.sum_eq_zero ?_
        intro c _
        simp [colorWeight, edgeColor_of_not_adj O hG hlt hadj]
    · by_cases hadj : G.Adj x y
      · have hadj' : G.Adj y x := hadj.symm
        obtain ⟨i, hi⟩ : ∃ i, O.nbr x i = some y := hG.exists_nbr_of_adj hadj
        have he' : edgeColor O y x = some i := (edgeColor_eq_some_iff O hgt i).mpr hi
        have he : edgeColor O x y = some i := by
          rw [edgeColor_comm]; exact he'
        rw [Finset.sum_eq_single i]
        · simp [colorWeight, he]
        · intro b _ hb
          simp only [colorWeight, he]
          rw [if_neg (by simp only [Option.some.injEq]; exact fun h => hb h.symm)]
        · intro hi'
          exact absurd (Finset.mem_univ i) hi'
      · rw [hw x y hadj]
        symm
        refine Finset.sum_eq_zero ?_
        intro c _
        have hnot : ¬ G.Adj y x := fun h => hadj h.symm
        have hnone : edgeColor O y x = none := edgeColor_of_not_adj O hG hgt hnot
        have hnone' : edgeColor O x y = none := by rw [edgeColor_comm]; exact hnone
        simp only [colorWeight, hnone']
        rw [if_neg (by simp)]

/-! ## The directed parent map -/

/-- The parent of `v` in colour `c`: the `c`-th neighbour of `v` when that
neighbour has smaller label, otherwise `none` (the paper directs every edge
from the lower- to the higher-labelled endpoint). -/
def parent (O : SparseOrb N d) (c : Fin d) (v : Fin N) : Option (Fin N) :=
  match O.nbr v c with
  | some w => if w < v then some w else none
  | none => none

/-- Unfolding the parent map. -/
theorem parent_eq_some_iff (O : SparseOrb N d) (c : Fin d) (v w : Fin N) :
    parent O c v = some w ↔ O.nbr v c = some w ∧ w < v := by
  cases h : O.nbr v c with
  | none =>
      have hp : parent O c v = none := by simp [parent, h]
      rw [hp]
      simp [h]
  | some u =>
      have hp : parent O c v = if u < v then some u else none := by simp [parent, h]
      rw [hp]
      by_cases hu : u < v
      · rw [if_pos hu]
        simp only [Option.some.injEq]
        constructor
        · intro h; exact ⟨h, by rw [← h]; exact hu⟩
        · intro h; exact h.1
      · rw [if_neg hu]
        constructor
        · intro h; exact absurd h (by simp)
        · rintro ⟨huv, hlt⟩
          have huw : u = w := Option.some.inj huv
          exact absurd (by rw [huw]; exact hlt) hu

/-- A parent edge is an edge of colour `c`. -/
theorem parent_edgeColor (O : SparseOrb N d) (c : Fin d) {v w : Fin N}
    (h : parent O c v = some w) : edgeColor O w v = some c := by
  obtain ⟨hn, hlt⟩ := (parent_eq_some_iff O c v w).mp h
  exact (edgeColor_eq_some_iff O hlt c).mpr hn

/-- The colour-`c` edge above `v` is exactly the parent edge. -/
theorem edgeColor_iff_parent (O : SparseOrb N d) (c : Fin d) {v w : Fin N}
    (h : w < v) : edgeColor O w v = some c ↔ parent O c v = some w := by
  rw [edgeColor_eq_some_iff O h, parent_eq_some_iff]
  exact ⟨fun hn => ⟨hn, h⟩, fun h' => h'.1⟩

/-! ## Forest of arborescences -/

/-- The step map of a parent function: `v ↦ parent v` when it exists, and
`v` itself at a root. -/
def step (parent : Fin N → Option (Fin N)) (v : Fin N) : Fin N :=
  (parent v).getD v

/-- A parent map is a forest of arborescences when (i) every edge points from
a vertex to a strictly larger label (so the directed graph is acyclic and
every vertex has at most one parent) and (ii) iterating the parent map from
any vertex terminates at a root.  A root is a vertex with no parent; the
strict decrease makes the weak components trees, each with a unique root, and
all edges point away from that root --- i.e. every tree is an arborescence. -/
def IsForestOfArborescences (parent : Fin N → Option (Fin N)) : Prop :=
  (∀ v w, parent v = some w → w < v) ∧
  (∀ v, ∃ k : ℕ, parent ((step parent)^[k] v) = none)

/-- Any strictly label-decreasing parent map is a forest of arborescences:
the parent chain terminates because the label strictly decreases. -/
theorem forest_of_strict_parent {parent : Fin N → Option (Fin N)}
    (hdec : ∀ v w, parent v = some w → w < v) :
    IsForestOfArborescences parent := by
  refine ⟨hdec, ?_⟩
  intro v
  let s := step parent
  have reach : ∀ u : Fin N, ∃ k, parent (s^[k] u) = none := by
    intro u
    induction u using Fin.strong_induction_on with
    | h u ih =>
        by_cases hu : parent u = none
        · exact ⟨0, by simpa [s] using hu⟩
        · obtain ⟨w, hw⟩ : ∃ w, parent u = some w := by
            cases h : parent u with
            | none => exact absurd h hu
            | some w => exact ⟨w, rfl⟩
          obtain ⟨k, hk⟩ := ih w (hdec u w hw)
          refine ⟨k + 1, ?_⟩
          rw [Function.iterate_succ_apply]
          have hsu : s u = w := by simp [s, step, hw]
          rw [hsu]
          exact hk
  exact reach v

/-- The step map fixes every root. -/
theorem step_of_root {parent : Fin N → Option (Fin N)} {r : Fin N}
    (h : parent r = none) : step parent r = r := by
  simp [step, h]

/-- Roots reachable from a fixed vertex by the deterministic parent chain are
unique: this is the paper's "each tree has a unique root". -/
theorem forest_root_unique {parent : Fin N → Option (Fin N)} {v r r' : Fin N}
    {k l : ℕ} (hk : (step parent)^[k] v = r) (hr : parent r = none)
    (hl : (step parent)^[l] v = r') (hr' : parent r' = none) : r = r' := by
  have hfix : ∀ {u : Fin N}, parent u = none → ∀ n, (step parent)^[n] u = u := by
    intro u hu n
    induction n with
    | zero => simp
    | succ n ihn => rw [Function.iterate_succ_apply, step_of_root hu, ihn]
  rcases Nat.le_total k l with hkl | hlk
  · have hl' : (step parent)^[l] v = (step parent)^[l - k] ((step parent)^[k] v) := by
      have h := Function.iterate_add_apply (step parent) (l - k) k v
      rwa [Nat.sub_add_cancel hkl] at h
    rw [hl', hk] at hl
    rw [hfix hr (l - k)] at hl
    exact hl
  · have hk' : (step parent)^[k] v = (step parent)^[k - l] ((step parent)^[l] v) := by
      have h := Function.iterate_add_apply (step parent) (k - l) l v
      rwa [Nat.sub_add_cancel hlk] at h
    rw [hk', hl] at hk
    rw [hfix hr' (k - l)] at hk
    exact hk.symm

/-- **Lemma 1, second part**: every colour class is a forest of
arborescences. -/
theorem color_class_is_forest (O : SparseOrb N d) (c : Fin d) :
    IsForestOfArborescences (parent O c) :=
  forest_of_strict_parent fun v w h => ((parent_eq_some_iff O c v w).mp h).2

/-! ## Query complexity of the parent and of the incident edge list -/

/-- **Lemma 1, third part**: the parent is determined by the single oracle
answer `f(v,c)`. -/
theorem parent_one_query (O : SparseOrb N d) (c : Fin d) (v : Fin N) :
    ∀ O' : SparseOrb N d, O'.nbr v c = O.nbr v c →
      parent O' c v = parent O c v := by
  intro O' h
  unfold parent
  rw [h]

/-- The directed arcs of colour `c`: `(p, v)` with `p` the parent of `v`. -/
def arcs (O : SparseOrb N d) (c : Fin d) : Finset (Fin N × Fin N) :=
  Finset.univ.filter fun p : Fin N × Fin N => parent O c p.2 = some p.1

/-- The edges of colour `c` incident on `x`. -/
def incEdges (O : SparseOrb N d) (c : Fin d) (x : Fin N) : Finset (Fin N × Fin N) :=
  Finset.univ.filter fun p : Fin N × Fin N =>
    p.1 < p.2 ∧ edgeColor O p.1 p.2 = some c ∧ (p.1 = x ∨ p.2 = x)

/-- The incident edges are exactly the colour-`c` arcs touching `x`. -/
theorem incEdges_eq_arcs (O : SparseOrb N d) (c : Fin d) (x : Fin N) :
    incEdges O c x = (arcs O c).filter fun p => p.1 = x ∨ p.2 = x := by
  ext p
  simp only [incEdges, arcs, Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨hlt, hcol, hx⟩
    exact ⟨(edgeColor_iff_parent O c hlt).mp hcol, hx⟩
  · rintro ⟨hpar, hx⟩
    have hlt : p.1 < p.2 := ((parent_eq_some_iff O c p.2 p.1).mp hpar).2
    exact ⟨hlt, (edgeColor_iff_parent O c hlt).mpr hpar, hx⟩

/-- The oracle queries made by the canonical incident-edge procedure: the `d`
slots of `x`, then the `c`-th slot of each listed neighbour. -/
def incQuerySet (O : SparseOrb N d) (c : Fin d) (x : Fin N) : Finset (Fin N × Fin d) :=
  (Finset.univ.image fun i : Fin d => (x, i)) ∪
    ((Finset.univ.filter fun i : Fin d => O.nbr x i ≠ none).image fun i =>
      match O.nbr x i with
      | some y => (y, c)
      | none => (x, c))

/-- At most `2d` oracle queries suffice for the incident list. -/
theorem incQuerySet_card_le (O : SparseOrb N d) (c : Fin d) (x : Fin N) :
    (incQuerySet O c x).card ≤ 2 * d := by
  unfold incQuerySet
  have hA : ((Finset.univ : Finset (Fin d)).image fun i => (x, i)).card ≤ d := by
    calc _ ≤ (Finset.univ : Finset (Fin d)).card := Finset.card_image_le
      _ = d := by simp
  have hB : (((Finset.univ : Finset (Fin d)).filter fun i => O.nbr x i ≠ none).image
      fun i => match O.nbr x i with
        | some y => (y, c)
        | none => (x, c)).card ≤ d := by
    calc _ ≤ ((Finset.univ : Finset (Fin d)).filter fun i => O.nbr x i ≠ none).card :=
          Finset.card_image_le
      _ ≤ (Finset.univ : Finset (Fin d)).card := Finset.card_filter_le _ _
      _ = d := by simp
  calc _ ≤ _ + _ := Finset.card_union_le _ _
    _ ≤ d + d := Nat.add_le_add hA hB
    _ = 2 * d := by ring

/-- **Lemma 1, fourth part**: the incident colour-`c` edge list is determined
by the at most `2d` oracle answers in `incQuerySet`.  This is the precise
meaning of "with `O(d)` queries we can determine the list of edges in `H_c`
incident on `v`" (p. 6). -/
theorem incEdges_two_d_queries (O : SparseOrb N d) (c : Fin d) (x : Fin N) :
    ∃ qs : Finset (Fin N × Fin d), qs.card ≤ 2 * d ∧
      ∀ O' : SparseOrb N d, (∀ q ∈ qs, O'.nbr q.1 q.2 = O.nbr q.1 q.2) →
        incEdges O' c x = incEdges O c x := by
  refine ⟨incQuerySet O c x, incQuerySet_card_le O c x, ?_⟩
  intro O' hO'
  ext p
  simp only [incEdges, Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨hlt, hcol, hx⟩
    have hcol' : edgeColor O p.1 p.2 = some c := by
      by_cases hp1 : p.1 = x
      · -- p = (x, y), read the c-th slot of y
        rw [hp1] at hlt hcol ⊢
        have hne : O'.nbr p.2 c = some x := (edgeColor_eq_some_iff O' hlt c).mp hcol
        obtain ⟨j, hj⟩ : ∃ j, O'.nbr x j = some p.2 := O'.nbr_symm hne
        have hjO : O.nbr x j = some p.2 := by
          have hmem : (x, j) ∈ incQuerySet O c x := by
            simp only [incQuerySet, Finset.mem_union, Finset.mem_image, Finset.mem_filter,
              Finset.mem_univ, true_and]
            exact Or.inl ⟨j, rfl⟩
          exact (hO' (x, j) hmem).symm.trans hj
        have hq : (p.2, c) ∈ incQuerySet O c x := by
          simp only [incQuerySet, Finset.mem_union, Finset.mem_image, Finset.mem_filter,
            Finset.mem_univ, true_and]
          refine Or.inr ⟨j, ?_, by rw [hjO]⟩
          rw [hjO]
          simp
        have hOq : O.nbr p.2 c = O'.nbr p.2 c := (hO' (p.2, c) hq).symm
        exact (edgeColor_eq_some_iff O hlt c).mpr (hOq.trans hne)
      · -- p = (y, x), colour read from the c-th slot of x
        have hpx : p.2 = x := by
          rcases hx with h | h
          · exact absurd h hp1
          · exact h
        rw [hpx] at hlt hcol ⊢
        have hne : O'.nbr x c = some p.1 := (edgeColor_eq_some_iff O' hlt c).mp hcol
        have hq : (x, c) ∈ incQuerySet O c x := by
          simp only [incQuerySet, Finset.mem_union, Finset.mem_image, Finset.mem_filter,
            Finset.mem_univ, true_and]
          exact Or.inl ⟨c, rfl⟩
        have hOq : O.nbr x c = O'.nbr x c := (hO' (x, c) hq).symm
        exact (edgeColor_eq_some_iff O hlt c).mpr (hOq.trans hne)
    exact ⟨hlt, hcol', hx⟩
  · rintro ⟨hlt, hcol, hx⟩
    have hcol' : edgeColor O' p.1 p.2 = some c := by
      by_cases hp1 : p.1 = x
      · rw [hp1] at hlt hcol ⊢
        have hne : O.nbr p.2 c = some x := (edgeColor_eq_some_iff O hlt c).mp hcol
        obtain ⟨j, hj⟩ : ∃ j, O.nbr x j = some p.2 := O.nbr_symm hne
        have hq : (p.2, c) ∈ incQuerySet O c x := by
          simp only [incQuerySet, Finset.mem_union, Finset.mem_image, Finset.mem_filter,
            Finset.mem_univ, true_and]
          refine Or.inr ⟨j, ?_, by rw [hj]⟩
          rw [hj]
          simp
        have hOq : O'.nbr p.2 c = O.nbr p.2 c := hO' (p.2, c) hq
        exact (edgeColor_eq_some_iff O' hlt c).mpr (hOq.trans hne)
      · have hpx : p.2 = x := by
          rcases hx with h | h
          · exact absurd h hp1
          · exact h
        rw [hpx] at hlt hcol ⊢
        have hne : O.nbr x c = some p.1 := (edgeColor_eq_some_iff O hlt c).mp hcol
        have hq : (x, c) ∈ incQuerySet O c x := by
          simp only [incQuerySet, Finset.mem_union, Finset.mem_image, Finset.mem_filter,
            Finset.mem_univ, true_and]
          exact Or.inl ⟨c, rfl⟩
        have hOq : O'.nbr x c = O.nbr x c := hO' (x, c) hq
        exact (edgeColor_eq_some_iff O' hlt c).mpr (hOq.trans hne)
    exact ⟨hlt, hcol', hx⟩

/-! ## Lemma 1, bundled -/

/-- **Lemma 1 (Forest decomposition)**, arXiv:1003.3683v2 §4 p.5--6.
For a Hamiltonian whose graph is `G`, listed by the sparse oracle `O`, there
is an edge colouring with `d` colours and directions on the edges such that:
the weights decompose as a sum of the `d` colour classes; every colour class
is a forest of arborescences; the parent of any vertex in a colour class is
determined by one oracle query; and the incident edge list of any vertex in a
colour class is determined by at most `2d` oracle queries. -/
theorem forest_decomposition (O : SparseOrb N d) {G : SimpleGraph (Fin N)}
    (hG : ListsGraph O G) :
    (∀ (w : Fin N → Fin N → ℂ), (∀ x y, ¬ G.Adj x y → w x y = 0) →
        ∀ x y, w x y = ∑ c : Fin d, colorWeight O c w x y) ∧
      (∀ c : Fin d, IsForestOfArborescences (parent O c)) ∧
      (∀ (c : Fin d) (v : Fin N), ∃ q : Fin N × Fin d,
        ∀ O' : SparseOrb N d, O'.nbr q.1 q.2 = O.nbr q.1 q.2 →
          parent O' c v = parent O c v) ∧
      (∀ (c : Fin d) (x : Fin N), ∃ qs : Finset (Fin N × Fin d),
        qs.card ≤ 2 * d ∧
          ∀ O' : SparseOrb N d, (∀ q ∈ qs, O'.nbr q.1 q.2 = O.nbr q.1 q.2) →
            incEdges O' c x = incEdges O c x) :=
  ⟨fun w hw x y => weight_decomposition O hG w hw x y,
   fun c => color_class_is_forest O c,
   fun c v => ⟨(v, c), fun O' h => parent_one_query O c v O' h⟩,
   fun c x => incEdges_two_d_queries O c x⟩

end Qatlib.Papers.StarDecompSim10.MainResults.ForestDecomposition
