/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.StarDecompSim10.MainResults.ForestDecomposition.SourceForestDecomposition
import Qatlib.Papers.StarDecompSim10.MainResults.VertexColoring.SourceVertexColoring
import Qatlib.Papers.StarDecompSim10.MainResults.GalaxySimulation.SourceGalaxySimulation

set_option backward.isDefEq.respectTransparency false

/-!
# Hamiltonian Star Decomposition

This module formalizes Theorem 4 of [Childs and Kothari, 2011][ChildsKothari2011] (§4, pp. 9–10).
Combining Lemma 1's `d`-forest decomposition (`ForestDecomposition`), Lemma 2's proper
6-coloring of each forest in `log* N + 1` parent queries (`VertexColoring`), and Theorem 3's
galaxy simulation (`GalaxySimulation`), a `d`-sparse Hamiltonian `H` on `N` vertices splits
into `m = 6d` galaxy summands `piece O w c t`, each determined locally by at most
`2d + (log* N + 2) = O(d + log* N)` oracle queries.

## Main statements

* `piece_isGalaxy`: every `(c, t)`-summand is a galaxy (disjoint union of stars).
* `star_decomposition`: `w` equals the sum of the `6d` galaxy summands.
* `piece_query_bound`: each summand's local weights depend on at most `2d + (log* N + 2)`
  oracle queries.
* `hamiltonian_star_decomposition`: bundled Theorem 4 statement.

## References

* [Childs and Kothari, 2011][ChildsKothari2011]
-/

set_option autoImplicit false

noncomputable section

namespace Qatlib.Papers.StarDecompSim10.MainResults.StarDecomposition

open Finset
open scoped BigOperators
open Qatlib.Papers.StarDecompSim10.MainResults.ForestDecomposition
open Qatlib.Papers.StarDecompSim10.MainResults.VertexColoring

variable {N d : ℕ}

/-! ## The colouring of a single colour class -/

/-- The Lemma 2 colour of `v` in the forest of colour `c`: the colour after
`log* N + 1` refinement rounds, started from the vertex label.  This is a
number in `{0,...,5}` by `colorAt_logStar_succ_lt_six`. -/
def starColor (O : SparseOrb N d) (c : Fin d) (v : Fin N) : ℕ :=
  colorAt (parent O c) (logStar N + 1) v

/-! ## The `6d` galaxy summands -/

/-- The `(c,t)`-summand of the star decomposition: it keeps the weight of an
edge of colour `c` when the Lemma 2 colour of its lower endpoint is `t`, and
is zero otherwise.  Edges of a forest are identified with their lower
endpoint, which is exactly the parent endpoint (Lemma 1). -/
def piece (O : SparseOrb N d) (w : Fin N → Fin N → ℂ) (c : Fin d) (t : Fin 6)
    (x y : Fin N) : ℂ :=
  if edgeColor O x y = some c ∧ starColor O c (min x y) = t.val then w x y else 0

/-- A weight function is a galaxy if it has no self-loops and its non-zero
entries are precisely edges of a disjoint union of stars: there is a centre
map `ctr`, idempotent, constant on the endpoints of every non-zero entry, and
each non-zero entry joins a vertex to its star centre. -/
def IsGalaxy (w : Fin N → Fin N → ℂ) : Prop :=
  (∀ x, w x x = 0) ∧
    ∃ ctr : Fin N → Fin N,
      (∀ z, ctr (ctr z) = ctr z) ∧
      (∀ x y, w x y ≠ 0 → ctr x = ctr y ∧ (x = ctr y ∨ y = ctr x))

/-- The centre map of the `(c,t)`-summand.  If `z` has colour `t` it is its
own centre (and a centre of its star); otherwise its centre is its parent,
provided the parent has colour `t`; if neither holds, `z` is not in a star of
colour `t` and is fixed (the summand is zero there). -/
def ctr (O : SparseOrb N d) (c : Fin d) (t : Fin 6) (z : Fin N) : Fin N :=
  if starColor O c z = t.val then z
  else
    match parent O c z with
    | some p => if starColor O c p = t.val then p else z
    | none => z

/-- A vertex of colour `t` is its own centre. -/
theorem ctr_col (O : SparseOrb N d) (c : Fin d) (t : Fin 6) {z : Fin N}
    (h : starColor O c z = t.val) : ctr O c t z = z := by
  unfold ctr
  simp [h]

/-- A vertex whose parent has colour `t` is attached to that parent. -/
theorem ctr_par (O : SparseOrb N d) (c : Fin d) (t : Fin 6) {z p : Fin N}
    (hz : starColor O c z ≠ t.val) (hp : parent O c z = some p)
    (hpt : starColor O c p = t.val) : ctr O c t z = p := by
  unfold ctr
  simp [hz, hp, hpt]

/-- A vertex with no parent of colour `t` is fixed by the centre map. -/
theorem ctr_iso (O : SparseOrb N d) (c : Fin d) (t : Fin 6) {z : Fin N}
    (hz : starColor O c z ≠ t.val)
    (hn : ∀ p, parent O c z = some p → starColor O c p ≠ t.val) :
    ctr O c t z = z := by
  unfold ctr
  simp only [hz, ↓reduceIte]
  cases h : parent O c z with
  | none => rfl
  | some p =>
      have hnp := hn p h
      simp [hnp]

/-- The centre map is idempotent: centres are fixed, and vertices attached to
a centre are mapped to a vertex of colour `t`, which is fixed. -/
theorem ctr_idem (O : SparseOrb N d) (c : Fin d) (t : Fin 6) (z : Fin N) :
    ctr O c t (ctr O c t z) = ctr O c t z := by
  by_cases hz : starColor O c z = t.val
  · rw [ctr_col O c t hz, ctr_col O c t hz]
  · cases hp : parent O c z with
    | none =>
        have hzm : ctr O c t z = z := ctr_iso O c t hz (by simp [hp])
        rw [hzm]
        exact hzm
    | some p =>
        by_cases hpt : starColor O c p = t.val
        · have hzp : ctr O c t z = p := ctr_par O c t hz hp hpt
          rw [hzp, ctr_col O c t hpt]
        · have hzm : ctr O c t z = z :=
            ctr_iso O c t hz (fun q hq => by
              rw [hp] at hq
              have hpq : p = q := Option.some.inj hq
              rw [← hpq]
              exact hpt)
          rw [hzm]
          exact hzm

/-! ## Galaxies supported on the colour classes -/

/-- The support of a `(c,t)`-summand is a star: its non-zero entries have a
well-defined centre, and each entry is either the centre-to-leaf edge or the
corresponding leaf-to-centre edge. -/
theorem piece_ctr_support (O : SparseOrb N d) {G : SimpleGraph (Fin N)}
    (hG : ListsGraph O G) (w : Fin N → Fin N → ℂ) (c : Fin d) (t : Fin 6)
    (x y : Fin N) (hne : piece O w c t x y ≠ 0) :
    ctr O c t x = ctr O c t y ∧ (x = ctr O c t y ∨ y = ctr O c t x) := by
  have hcond : edgeColor O x y = some c ∧ starColor O c (min x y) = t.val := by
    by_contra h
    apply hne
    unfold piece
    simp [h]
  obtain ⟨hedge, hcol⟩ := hcond
  have hpar_all : ∀ v q, parent O c v = some q → q < v :=
    fun v q h => ((parent_eq_some_iff O c v q).mp h).2
  rcases lt_trichotomy x y with hlt | heq | hgt
  · have hxmin : min x y = x := min_eq_left (le_of_lt hlt)
    rw [hxmin] at hcol
    have hpar : parent O c y = some x := (edgeColor_iff_parent O c hlt).mp hedge
    have hcoly : starColor O c y ≠ t.val := by
      have hproper := colorAt_proper hpar_all (logStar N + 1) y x hpar
      exact fun hc => hproper (hc.trans hcol.symm)
    have hcx : ctr O c t x = x := ctr_col O c t hcol
    have hcy : ctr O c t y = x := ctr_par O c t hcoly hpar hcol
    exact ⟨by rw [hcx, hcy], Or.inl (by rw [hcy])⟩
  · subst heq
    have hnone : edgeColor O x x = none := edgeColor_self_eq_none O hG x
    rw [hnone] at hedge
    exact absurd hedge (by simp)
  · have hymin : min x y = y := min_eq_right (le_of_lt hgt)
    rw [hymin] at hcol
    have hedge' : edgeColor O y x = some c := by
      rw [edgeColor_comm]
      exact hedge
    have hpar : parent O c x = some y := (edgeColor_iff_parent O c hgt).mp hedge'
    have hcolx : starColor O c x ≠ t.val := by
      have hproper := colorAt_proper hpar_all (logStar N + 1) x y hpar
      exact fun hc => hproper (hc.trans hcol.symm)
    have hcy : ctr O c t y = y := ctr_col O c t hcol
    have hcx : ctr O c t x = y := ctr_par O c t hcolx hpar hcol
    exact ⟨by rw [hcy, hcx], Or.inr (by rw [hcx])⟩

/-- **Theorem 4, galaxy property**: every `(c,t)`-summand is a galaxy.  Its
edges have a common centre, so it is a disjoint union of stars. -/
theorem piece_isGalaxy (O : SparseOrb N d) {G : SimpleGraph (Fin N)}
    (hG : ListsGraph O G) (w : Fin N → Fin N → ℂ) (c : Fin d) (t : Fin 6) :
    IsGalaxy (piece O w c t) := by
  refine ⟨?_, ctr O c t, ctr_idem O c t, ?_⟩
  · intro x
    unfold piece
    have hnone : edgeColor O x x = none := edgeColor_self_eq_none O hG x
    simp [hnone]
  · intro x y h
    exact piece_ctr_support O hG w c t x y h

/-! ## The sum decomposition -/

/-- **Theorem 4, decomposition step**: fixing a colour `c`, the sum of the six
`(c,t)`-summands is the colour-`c` class `colorWeight O c w`.  At a non-zero
entry of colour `c`, exactly one of the six colours `t` matches the colour of
the lower endpoint. -/
theorem colorWeight_eq_sum_pieces (O : SparseOrb N d) (w : Fin N → Fin N → ℂ)
    (x y : Fin N) (c : Fin d) :
    colorWeight O c w x y = ∑ t : Fin 6, piece O w c t x y := by
  by_cases he : edgeColor O x y = some c
  · have hb : starColor O c (min x y) < 6 :=
      colorAt_logStar_succ_lt_six (parent O c) (min x y)
    have hsingle : (∑ t : Fin 6, piece O w c t x y) =
        piece O w c ⟨starColor O c (min x y), hb⟩ x y := by
      refine Finset.sum_eq_single _ ?_ ?_
      · intro t _ ht
        unfold piece
        have hne_val : starColor O c (min x y) ≠ t.val := fun hct => ht (Fin.ext hct.symm)
        simp [hne_val]
      · intro ht0
        exact absurd (Finset.mem_univ _) ht0
    calc colorWeight O c w x y = w x y := by
          unfold colorWeight
          simp [he]
      _ = piece O w c ⟨starColor O c (min x y), hb⟩ x y := by
          unfold piece
          simp [he]
      _ = ∑ t : Fin 6, piece O w c t x y := hsingle.symm
  · calc colorWeight O c w x y = 0 := by
          unfold colorWeight
          simp [he]
      _ = ∑ t : Fin 6, piece O w c t x y := by
          rw [Finset.sum_eq_zero]
          intro t _
          unfold piece
          simp [he]

/-- **Theorem 4, decomposition**: the weight function is the sum of the `6d`
galaxy summands.  This is the paper's `H = Σ_{j=1}^{m} H_j` with `m = 6d`,
obtained by applying Lemma 1 to `H` and then splitting each colour class
according to the six colours of Lemma 2. -/
theorem star_decomposition (O : SparseOrb N d) {G : SimpleGraph (Fin N)}
    (hG : ListsGraph O G) (w : Fin N → Fin N → ℂ)
    (hw : ∀ x y, ¬ G.Adj x y → w x y = 0) (x y : Fin N) :
    w x y = ∑ j : Fin d × Fin 6, piece O w j.1 j.2 x y := by
  rw [weight_decomposition O hG w hw x y]
  rw [← Finset.univ_product_univ, Finset.sum_product]
  exact Finset.sum_congr rfl fun c _ => colorWeight_eq_sum_pieces O w x y c

/-! ## Query complexity of the summands -/

/-- **Theorem 4, query bound**: the weights of the `(c,t)`-summand at a vertex
`x` are determined by at most `2d + (log* N + 2)` oracle queries: the `2d`
queries for the incident edge list (Lemma 1) and the `log* N + 2` vertices of
the ancestor chain needed by the colouring (Lemma 2). -/
theorem piece_query_bound (O : SparseOrb N d) (c : Fin d) (x : Fin N) :
    (incQuerySet O c x).card + (reach (parent O c) (logStar N + 1) x).card
      ≤ 2 * d + (logStar N + 2) := by
  have h1 := incQuerySet_card_le O c x
  have h2 := reach_card_le (parent O c) (logStar N + 1) x
  omega

/-! ## Theorem 4 -/

/-- **Theorem 4 (Hamiltonian star decomposition)**, arXiv:1003.3683v2 §4
Theorem 4, p. 9--10.  Let `H` be a sparse Hamiltonian on `N` vertices of
maximum degree `d` with weights `w`, listed by the oracle `O`.  Then:

* the decomposition has `m = 6d` summands (`Fintype.card (Fin d × Fin 6)`),
* `w = Σ_j piece_j` (the paper's `H = Σ_{j=1}^{m} H_j`),
* every summand `piece_j` is a galaxy (a disjoint union of stars): it has an
  idempotent centre map and its non-zero entries join a vertex to its centre,
* the weights of each summand are determined by at most
  `2d + (log* N + 2) = O(d + log* N)` queries to the oracle for `H`,
  so by Theorem 3 (`galaxy_simulation`, imported) each galaxy is simulable
  for time `t'` with `Q(H_j) = O(d + log* N)` queries. -/
theorem hamiltonian_star_decomposition (O : SparseOrb N d) {G : SimpleGraph (Fin N)}
    (hG : ListsGraph O G) (w : Fin N → Fin N → ℂ)
    (hw : ∀ x y, ¬ G.Adj x y → w x y = 0) :
    Fintype.card (Fin d × Fin 6) = 6 * d ∧
      (∀ x y, w x y = ∑ j : Fin d × Fin 6, piece O w j.1 j.2 x y) ∧
      (∀ j : Fin d × Fin 6, IsGalaxy (fun x y => piece O w j.1 j.2 x y)) ∧
      (∀ (j : Fin d × Fin 6) (x : Fin N),
        (incQuerySet O j.1 x).card +
            (reach (parent O j.1) (logStar N + 1) x).card
          ≤ 2 * d + (logStar N + 2)) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [Fintype.card_prod]
    simp
    omega
  · intro x y
    exact star_decomposition O hG w hw x y
  · intro j
    exact piece_isGalaxy O hG w j.1 j.2
  · intro j x
    exact piece_query_bound O j.1 x

end Qatlib.Papers.StarDecompSim10.MainResults.StarDecomposition
