/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Papers.StarDecompSim10.MainResults.ForestDecomposition.SourceForestDecomposition
public import Qatlib.Papers.StarDecompSim10.ForestColors.ColorRefine

@[expose] public section


/-!
# Closed galaxy-mask support, with the six-color gap kept explicit

Source: arXiv:1003.3683v2, Theorem 4, pp. 9--10; legacy commit
9182ca0aca06c3e45b933ef9064bb7e805ebdb6e, SourceStarDecomposition.
The eleven recovered declarations prove idempotent centers, the galaxy
support of each mask, and a query-set cardinality bound. They do not prove
that the six masks exhaust a forest: that depended on an admitted bit-width
estimate in the original development. Nor does a matrix-entry support fact
provide an exponential-simulation circuit or an oracle-cost implementation.
The original source and omitted targets remain archived in that commit.
-/

set_option autoImplicit false

noncomputable section

namespace Qatlib.Papers.StarDecompSim10.MainResults

open Finset
open scoped BigOperators
open Qatlib.Papers.StarDecompSim10.MainResults.ForestDecomposition
open Qatlib.Papers.StarDecompSim10.ForestColors

variable {N d : ℕ}

/-- The color after the prescribed number of refinement rounds. A bound by six is not asserted here. -/
def starColor (O : SparseOrb N d) (c : Fin d) (v : Fin N) : ℕ :=
  colorAt (parent O c) (logStar N + 1) v

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
theorem ctrCol (O : SparseOrb N d) (c : Fin d) (t : Fin 6) {z : Fin N}
    (h : starColor O c z = t.val) : ctr O c t z = z := by
  unfold ctr
  rw [ite_eq_left h]

/-- A vertex whose parent has colour `t` is attached to that parent. -/
theorem ctrPar (O : SparseOrb N d) (c : Fin d) (t : Fin 6) {z p : Fin N}
    (hz : starColor O c z ≠ t.val) (hp : parent O c z = some p)
    (hpt : starColor O c p = t.val) : ctr O c t z = p := by
  unfold ctr
  rw [ite_eq_right hz, hp]
  change (if starColor O c p = t.val then p else z) = p
  rw [ite_eq_left hpt]

/-- A vertex with no parent of colour `t` is fixed by the centre map. -/
theorem ctrIso (O : SparseOrb N d) (c : Fin d) (t : Fin 6) {z : Fin N}
    (hz : starColor O c z ≠ t.val)
    (hn : ∀ p, parent O c z = some p → starColor O c p ≠ t.val) :
    ctr O c t z = z := by
  unfold ctr
  rw [ite_eq_right hz]
  cases h : parent O c z with
  | none => rfl
  | some p =>
      change (if starColor O c p = t.val then p else z) = z
      rw [ite_eq_right (hn p h)]

/-- The centre map is idempotent: centres are fixed, and vertices attached to
a centre are mapped to a vertex of colour `t`, which is fixed. -/
theorem ctrIdem (O : SparseOrb N d) (c : Fin d) (t : Fin 6) (z : Fin N) :
    ctr O c t (ctr O c t z) = ctr O c t z := by
  by_cases hz : starColor O c z = t.val
  · rw [ctrCol O c t hz, ctrCol O c t hz]
  · cases hp : parent O c z with
    | none =>
        have hzm : ctr O c t z = z := ctrIso O c t hz (by simp [hp])
        rw [hzm]
        exact hzm
    | some p =>
        by_cases hpt : starColor O c p = t.val
        · have hzp : ctr O c t z = p := ctrPar O c t hz hp hpt
          rw [hzp, ctrCol O c t hpt]
        · have hzm : ctr O c t z = z :=
            ctrIso O c t hz (fun q hq => by
              rw [hp] at hq
              have hpq : p = q := Option.some.inj hq
              rw [← hpq]
              exact hpt)
          rw [hzm]
          exact hzm

/-- The support of a `(c,t)`-summand is a star: its non-zero entries have a
well-defined centre, and each entry is either the centre-to-leaf edge or the
corresponding leaf-to-centre edge. -/
theorem pieceSupport (O : SparseOrb N d) {G : SimpleGraph (Fin N)}
    (hG : ListsGraph O G) (w : Fin N → Fin N → ℂ) (c : Fin d) (t : Fin 6)
    (x y : Fin N) (hne : piece O w c t x y ≠ 0) :
    ctr O c t x = ctr O c t y ∧ (x = ctr O c t y ∨ y = ctr O c t x) := by
  have hcond : edgeColor O x y = some c ∧ starColor O c (min x y) = t.val := by
    by_contra h
    apply hne
    unfold piece
    rw [ite_eq_right h]
  obtain ⟨hedge, hcol⟩ := hcond
  have hpar_all : ∀ v q, parent O c v = some q → q < v :=
    fun v q h => ((parent_eq_some_iff O c v q).mp h).2
  rcases lt_trichotomy x y with hlt | heq | hgt
  · have hxmin : min x y = x := min_eq_left (le_of_lt hlt)
    rw [hxmin] at hcol
    have hpar : parent O c y = some x := (edgeColor_iff_parent O c hlt).mp hedge
    have hcoly : starColor O c y ≠ t.val := by
      have hproper := colorProper hpar_all (logStar N + 1) y x hpar
      exact fun hc => hproper (hc.trans hcol.symm)
    have hcx : ctr O c t x = x := ctrCol O c t hcol
    have hcy : ctr O c t y = x := ctrPar O c t hcoly hpar hcol
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
      have hproper := colorProper hpar_all (logStar N + 1) x y hpar
      exact fun hc => hproper (hc.trans hcol.symm)
    have hcy : ctr O c t y = y := ctrCol O c t hcol
    have hcx : ctr O c t x = y := ctrPar O c t hcolx hpar hcol
    exact ⟨by rw [hcy, hcx], Or.inr (by rw [hcx])⟩

/-- **Theorem 4, galaxy property**: every `(c,t)`-summand is a galaxy.  Its
edges have a common centre, so it is a disjoint union of stars. -/
theorem pieceGalaxy (O : SparseOrb N d) {G : SimpleGraph (Fin N)}
    (hG : ListsGraph O G) (w : Fin N → Fin N → ℂ) (c : Fin d) (t : Fin 6) :
    IsGalaxy (piece O w c t) := by
  refine ⟨?_, ctr O c t, ctrIdem O c t, ?_⟩
  · intro x
    unfold piece
    rw [ite_eq_right]
    rintro ⟨he, -⟩
    rw [edgeColor_self_eq_none O hG x] at he
    exact absurd he (by simp)
  · intro x y h
    exact pieceSupport O hG w c t x y h

/-- The incident-list and ancestor-query sets have the stated combined cardinality. This is a set bound, not a coherent oracle implementation. -/
theorem pieceQueries (O : SparseOrb N d) (c : Fin d) (x : Fin N) :
    (incQuerySet O c x).card + (reach (parent O c) (logStar N + 1) x).card
      ≤ 2 * d + (logStar N + 2) := by
  have h1 := incQuerySet_card_le O c x
  have h2 := reachBound (parent O c) (logStar N + 1) x
  omega

end Qatlib.Papers.StarDecompSim10.MainResults
