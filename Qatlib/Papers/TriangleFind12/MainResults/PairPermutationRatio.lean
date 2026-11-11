/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.GroupTheory.Perm.Basic
import Mathlib.Logic.Equiv.Fintype
import Mathlib.Data.Fintype.Perm
import Mathlib.Data.Finset.Card
import Mathlib.Data.Fintype.Card
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Tactic.Group

set_option backward.isDefEq.respectTransparency false

/-!
# `MainResults/PairPermutationRatio` — the pair ratio of a regular bipartite graph
(source Lemma 10)

Lee--Magniez--Santha, *Improved Quantum Query Algorithms for Triangle Finding and
Associativity Testing*, fixed arXiv:1210.1014v1.

Source locations:

* Definition 2, page 3: the *type* of a bipartite graph between `Y1` and `Y2`;
  type `({(l, d)}, {(g, l*d/g)})` means that `Y1` has `l` vertices of degree `d`
  and `Y2` has `g` vertices of degree `l*d/g`. Its single-degree case is
  `IsType`, and the consistency equation `l*d = g*e` of Definition 2 is
  `IsType.card_mul_eq`.
* Lemma 10, page 16, with its proof: for `Y1, Y2` of size `l, g`, `(y1, y2) ∈
  Y1 × Y2`, and a bipartite `K ⊆ Y1 × Y2` of that type,
  `Pr_σ [{y1, y2} ∈ σ(K)] = d/g`, proved by the double count
  `c * (l*d) = (l*g) * (p*c)` over the `c` graphs isomorphic to `K`.
* The use in the proof of Lemma 9, page 16: the probability is taken over `σ`
  *conditioned* on `y1 ∈ σ(Y1)` and `y2 ∈ σ(Y2)`, i.e. on `σ⁻¹ y1 ∈ Y1` and
  `σ⁻¹ y2 ∈ Y2`.

What is formalized here. The literal unconditional reading of the source
statement is false: with `n = 4`, `Y1 = {0,1}`, `Y2 = {2,3}` and `K` the perfect
matching `{(0,2), (1,3)}` (so `l = g = 2`, `d = 1`), a direct enumeration of the
`24` permutations gives `Pr_σ [{0,2} ∈ σ(K)] = 1/3`, not `d/g = 1/2`. The
statement that the source actually proves — and the one its proof of Lemma 9
uses — is the conditional one, and that is what is proved here:

`Pr_σ [{y1,y2} ∈ σ(K) | σ⁻¹ y1 ∈ Y1 ∧ σ⁻¹ y2 ∈ Y2] = d / g`

for `Y1`, `Y2` disjoint. Because `σ⁻¹ y1 ∈ Y1` and `σ⁻¹ y2 ∈ Y2` pin the preimage
pair to a unique `(i, j) ∈ Y1 × Y2`, the conditioning makes the preimage pair
uniform over the `l*g` pairs of `Y1 × Y2`; a regular bipartite graph then meets
`d/g` of them, which is exactly the source's double count.

The residue of the source statement that is *not* claimed here: the unconditional
probability (which is not `d/g`), and any asymptotic `Ω` transfer to the
learning-graph maximum-vertex-ratio bound of Lemma 9.
-/

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.TriangleFind12.MainResults

open Finset

/-- The fibre of the two-point action of the symmetric group: the permutations
sending `i` to `a` and `j` to `b`. This is the set over which the source's
`Pr_σ` is taken, restricted to one preimage pair. -/
def pairFiber {n : ℕ} (a b i j : Fin n) : Finset (Equiv.Perm (Fin n)) :=
  Finset.univ.filter (fun σ => σ i = a ∧ σ j = b)

/-- Two-point transitivity of the symmetric group: for distinct `i, j` and
distinct `a, b` there is a permutation taking `i` to `a` and `j` to `b`.

This supplies the permutations used by the source's symmetry argument, which is
what lets the double count be run without knowing the fibre size. -/
theorem exists_perm_apply_pair {n : ℕ} (i j a b : Fin n) (hij : i ≠ j) (hab : a ≠ b) :
    ∃ σ : Equiv.Perm (Fin n), σ i = a ∧ σ j = b := by
  classical
  refine ⟨Equiv.swap (Equiv.swap i a j) b * Equiv.swap i a, ?_, ?_⟩
  · simp only [Equiv.Perm.mul_apply, Equiv.swap_apply_left]
    refine Equiv.swap_apply_of_ne_of_ne ?_ hab
    intro h
    have hinv : Equiv.swap i a (Equiv.swap i a j) = j := Equiv.swap_apply_self i a j
    have hstep : Equiv.swap i a a = j := by
      rw [← h] at hinv
      exact hinv
    rw [Equiv.swap_apply_right] at hstep
    exact hij hstep
  · simp only [Equiv.Perm.mul_apply, Equiv.swap_apply_left]

/-- All two-point fibres of the symmetric group have the same cardinality.

The bijection is `σ ↦ τ * σ * π⁻¹`, where `τ` moves `(a, b)` to `(a', b')` and
`π` moves `(i, j)` to `(i', j')`; both exist by two-point transitivity. -/
theorem pairFiber_card_eq {n : ℕ} (a b i j a' b' i' j' : Fin n)
    (hij : i ≠ j) (ha : a ≠ b) (hi'j' : i' ≠ j') (ha'b' : a' ≠ b') :
    (pairFiber a b i j).card = (pairFiber a' b' i' j').card := by
  classical
  obtain ⟨σ₀, hσ₀i, hσ₀j⟩ := exists_perm_apply_pair i j a b hij ha
  obtain ⟨σ₁, hσ₁i, hσ₁j⟩ := exists_perm_apply_pair i j a' b' hij ha'b'
  obtain ⟨π, hπi, hπj⟩ := exists_perm_apply_pair i j i' j' hij hi'j'
  have hτa : (σ₁ * σ₀.symm) a = a' := by
    rw [Equiv.Perm.mul_apply]
    have : σ₀.symm a = i := by rw [Equiv.symm_apply_eq, hσ₀i]
    rw [this, hσ₁i]
  have hτb : (σ₁ * σ₀.symm) b = b' := by
    rw [Equiv.Perm.mul_apply]
    have : σ₀.symm b = j := by rw [Equiv.symm_apply_eq, hσ₀j]
    rw [this, hσ₁j]
  have hπi' : π.symm i' = i := by rw [Equiv.symm_apply_eq, hπi]
  have hπj' : π.symm j' = j := by rw [Equiv.symm_apply_eq, hπj]
  have hτa' : (σ₁ * σ₀.symm).symm a' = a := by
    rw [Equiv.symm_apply_eq, hτa]
  have hτb' : (σ₁ * σ₀.symm).symm b' = b := by
    rw [Equiv.symm_apply_eq, hτb]
  refine Finset.card_bij' (fun σ _ => σ₁ * σ₀.symm * σ * π.symm)
    (fun σ _ => (σ₁ * σ₀.symm).symm * σ * π) ?_ ?_ ?_ ?_
  · intro σ hσ
    simp only [pairFiber, Finset.mem_filter, Finset.mem_univ, true_and] at hσ ⊢
    obtain ⟨h1, h2⟩ := hσ
    refine ⟨?_, ?_⟩
    · rw [Equiv.Perm.mul_apply, Equiv.Perm.mul_apply, hπi', h1, hτa]
    · rw [Equiv.Perm.mul_apply, Equiv.Perm.mul_apply, hπj', h2, hτb]
  · intro σ hσ
    simp only [pairFiber, Finset.mem_filter, Finset.mem_univ, true_and] at hσ ⊢
    obtain ⟨h1, h2⟩ := hσ
    refine ⟨?_, ?_⟩
    · rw [Equiv.Perm.mul_apply, Equiv.Perm.mul_apply, hπi, h1, hτa']
    · rw [Equiv.Perm.mul_apply, Equiv.Perm.mul_apply, hπj, h2, hτb']
  · intro σ _
    show (σ₁ * σ₀⁻¹)⁻¹ * (σ₁ * σ₀⁻¹ * σ * π⁻¹) * π = σ
    group
  · intro σ _
    show σ₁ * σ₀⁻¹ * (σ₁ * σ₀⁻¹)⁻¹ * σ * π * π⁻¹ = σ
    group

/-- The permutations whose preimage pair lies in `Y1 × Y2`: the conditioning
event `σ⁻¹ y1 ∈ Y1 ∧ σ⁻¹ y2 ∈ Y2` of the source's use of Lemma 10. -/
def permFiberAll {n : ℕ} (Y1 Y2 : Finset (Fin n)) (y1 y2 : Fin n) :
    Finset (Equiv.Perm (Fin n)) :=
  Finset.univ.filter (fun σ => σ.symm y1 ∈ Y1 ∧ σ.symm y2 ∈ Y2)

/-- The source's edge condition `{y1, y2} ∈ σ(K)`: some L-edge of `K` is carried
onto the unordered pair `{y1, y2}` by `σ`. -/
def edgeHit {n : ℕ} (K : Finset (Fin n × Fin n)) (σ : Equiv.Perm (Fin n))
    (y1 y2 : Fin n) : Prop :=
  ∃ p ∈ K, ({σ p.1, σ p.2} : Finset (Fin n)) = {y1, y2}

/-- The permutations of the conditioning event for which `{y1, y2}` is an edge of
`σ(K)`: this is the probability space of source Lemma 10 conditional on the
event used in the proof of Lemma 9. -/
def permEdgeHit {n : ℕ} (K : Finset (Fin n × Fin n)) (Y1 Y2 : Finset (Fin n))
    (y1 y2 : Fin n) : Finset (Equiv.Perm (Fin n)) := by
  classical
  exact (permFiberAll Y1 Y2 y1 y2).filter (fun σ => edgeHit K σ y1 y2)

/-- `permFiberAll` is the disjoint union of the two-point fibres over `Y1 × Y2`. -/
theorem permFiberAll_eq_biUnion {n : ℕ} (Y1 Y2 : Finset (Fin n)) (y1 y2 : Fin n) :
    permFiberAll Y1 Y2 y1 y2
      = (Y1 ×ˢ Y2).biUnion (fun p : Fin n × Fin n => pairFiber y1 y2 p.1 p.2) := by
  classical
  ext σ
  simp only [permFiberAll, pairFiber, Finset.mem_filter, Finset.mem_univ, true_and,
    Finset.mem_biUnion, Finset.mem_product]
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨(σ.symm y1, σ.symm y2), ⟨h1, h2⟩, Equiv.apply_symm_apply σ y1,
      Equiv.apply_symm_apply σ y2⟩
  · rintro ⟨p, ⟨hp1, hp2⟩, hf1, hf2⟩
    exact ⟨by rw [← hf1, Equiv.symm_apply_apply]; exact hp1,
      by rw [← hf2, Equiv.symm_apply_apply]; exact hp2⟩

/-- Distinct preimage pairs give disjoint two-point fibres. -/
theorem pairFiber_pairwiseDisjoint {n : ℕ} (Y1 Y2 : Finset (Fin n)) (y1 y2 : Fin n) :
    ((Y1 ×ˢ Y2 : Finset (Fin n × Fin n)) : Set (Fin n × Fin n)).PairwiseDisjoint
      (fun p => pairFiber y1 y2 p.1 p.2) := by
  classical
  intro p _ p' _ hne
  simp only [Function.onFun, Finset.disjoint_left]
  intro σ hσ hσ'
  simp only [pairFiber, Finset.mem_filter, Finset.mem_univ, true_and] at hσ hσ'
  have h1 : p.1 = p'.1 := by
    have e1 : σ.symm y1 = p.1 := by rw [← hσ.1, Equiv.symm_apply_apply]
    have e2 : σ.symm y1 = p'.1 := by rw [← hσ'.1, Equiv.symm_apply_apply]
    rw [← e1, e2]
  have h2 : p.2 = p'.2 := by
    have e1 : σ.symm y2 = p.2 := by rw [← hσ.2, Equiv.symm_apply_apply]
    have e2 : σ.symm y2 = p'.2 := by rw [← hσ'.2, Equiv.symm_apply_apply]
    rw [← e1, e2]
  exact hne (Prod.ext h1 h2)

/-- The cardinality of the conditioning set: `|Y1| * |Y2|` times the common
two-point fibre size. -/
theorem permFiberAll_card {n : ℕ} (Y1 Y2 : Finset (Fin n)) (y1 y2 : Fin n)
    (hne : y1 ≠ y2) (hdisj : Disjoint Y1 Y2) :
    (permFiberAll Y1 Y2 y1 y2).card
      = (Y1.card * Y2.card) * (pairFiber y1 y2 y1 y2).card := by
  classical
  have hne' : ∀ p ∈ Y1 ×ˢ Y2, p.1 ≠ p.2 := by
    intro p hp
    simp only [Finset.mem_product] at hp
    intro h
    exact (Finset.disjoint_left.mp hdisj) hp.1 (h ▸ hp.2)
  rw [permFiberAll_eq_biUnion, Finset.card_biUnion (pairFiber_pairwiseDisjoint Y1 Y2 y1 y2)]
  have hterm : ∀ p ∈ Y1 ×ˢ Y2,
      (pairFiber y1 y2 p.1 p.2).card = (pairFiber y1 y2 y1 y2).card := by
    intro p hp
    exact pairFiber_card_eq y1 y2 p.1 p.2 y1 y2 y1 y2 (hne' p hp) hne hne hne
  rw [Finset.sum_congr rfl hterm, Finset.sum_const_nat (fun _ _ => rfl),
    Finset.card_product]

/-- The edge condition `{y1, y2} ∈ σ(K)` inside the conditioning event is exactly
"the preimage pair lies in `K`", because `Y1` and `Y2` are disjoint.

This is the bridge from the source's edge-based probability to the pair count. -/
theorem permEdgeHit_eq_biUnion {n : ℕ} (Y1 Y2 : Finset (Fin n))
    (K : Finset (Fin n × Fin n)) (y1 y2 : Fin n)
    (hdisj : Disjoint Y1 Y2)
    (hK : ∀ p ∈ K, p.1 ∈ Y1 ∧ p.2 ∈ Y2) :
    permEdgeHit K Y1 Y2 y1 y2
      = K.biUnion (fun p : Fin n × Fin n => pairFiber y1 y2 p.1 p.2) := by
  classical
  ext σ
  simp only [permEdgeHit, permFiberAll, edgeHit, pairFiber, Finset.mem_filter,
    Finset.mem_univ, true_and, Finset.mem_biUnion]
  constructor
  · rintro ⟨⟨hσ1, hσ2⟩, p, hpK, hp⟩
    obtain ⟨hp1, hp2⟩ := hK p hpK
    have hne_p : p.1 ≠ p.2 := by
      intro h
      exact (Finset.disjoint_left.mp hdisj) hp1 (h ▸ hp2)
    have hmem1 : σ p.1 ∈ ({y1, y2} : Finset (Fin n)) := by
      rw [← hp]
      simp
    refine ⟨p, hpK, ?_, ?_⟩
    · rcases (by simpa using hmem1 : σ p.1 = y1 ∨ σ p.1 = y2) with h1 | h1
      · exact h1
      · exfalso
        -- `σ p.1 = y2` forces `p.1 = σ⁻¹ y2 ∈ Y2`, contradicting disjointness
        have : σ.symm y2 = p.1 := by rw [← h1, Equiv.symm_apply_apply]
        exact (Finset.disjoint_left.mp hdisj) hp1 (this ▸ hσ2)
    · -- under the previous case `σ p.1 = y1`, injectivity gives `σ p.2 = y2`
      have hmem2 : σ p.2 ∈ ({y1, y2} : Finset (Fin n)) := by
        rw [← hp]
        simp
      have h1 : σ p.1 = y1 := by
        rcases (by simpa using hmem1 : σ p.1 = y1 ∨ σ p.1 = y2) with h | h
        · exact h
        · exfalso
          have : σ.symm y2 = p.1 := by rw [← h, Equiv.symm_apply_apply]
          exact (Finset.disjoint_left.mp hdisj) hp1 (this ▸ hσ2)
      rcases (by simpa using hmem2 : σ p.2 = y1 ∨ σ p.2 = y2) with h2 | h2
      · exfalso
        exact hne_p (σ.injective (by rw [h1, h2]))
      · exact h2
  · rintro ⟨p, hpK, hf1, hf2⟩
    obtain ⟨hp1, hp2⟩ := hK p hpK
    refine ⟨⟨?_, ?_⟩, p, hpK, ?_⟩
    · rw [← hf1, Equiv.symm_apply_apply]
      exact hp1
    · rw [← hf2, Equiv.symm_apply_apply]
      exact hp2
    · rw [hf1, hf2]

/-- The cardinality of the edge-hit set: `|K|` times the common two-point fibre
size. -/
theorem permEdgeHit_card {n : ℕ} (Y1 Y2 : Finset (Fin n))
    (K : Finset (Fin n × Fin n)) (y1 y2 : Fin n)
    (hne : y1 ≠ y2) (hdisj : Disjoint Y1 Y2)
    (hK : ∀ p ∈ K, p.1 ∈ Y1 ∧ p.2 ∈ Y2) :
    (permEdgeHit K Y1 Y2 y1 y2).card = K.card * (pairFiber y1 y2 y1 y2).card := by
  classical
  have hne' : ∀ p ∈ K, p.1 ≠ p.2 := by
    intro p hp
    obtain ⟨hp1, hp2⟩ := hK p hp
    intro h
    exact (Finset.disjoint_left.mp hdisj) hp1 (h ▸ hp2)
  have hdisjK : ((K : Finset (Fin n × Fin n)) : Set (Fin n × Fin n)).PairwiseDisjoint
      (fun p => pairFiber y1 y2 p.1 p.2) :=
    (pairFiber_pairwiseDisjoint Y1 Y2 y1 y2).subset
      (fun p hp => Finset.mem_product.mpr (hK p hp))
  rw [permEdgeHit_eq_biUnion Y1 Y2 K y1 y2 hdisj hK, Finset.card_biUnion hdisjK]
  have hterm : ∀ p ∈ K, (pairFiber y1 y2 p.1 p.2).card = (pairFiber y1 y2 y1 y2).card := by
    intro p hp
    exact pairFiber_card_eq y1 y2 p.1 p.2 y1 y2 y1 y2 (hne' p hp) hne hne hne
  rw [Finset.sum_congr rfl hterm, Finset.sum_const_nat (fun _ _ => rfl)]

/-- The conditioning event `σ⁻¹ y1 ∈ Y1 ∧ σ⁻¹ y2 ∈ Y2` is nonempty as soon as
`y1 ∈ Y1` and `y2 ∈ Y2`: the identity permutation belongs to it.

This is where the source's hypothesis `(y1, y2) ∈ Y1 × Y2` is used. -/
theorem permFiberAll_nonempty {n : ℕ} (Y1 Y2 : Finset (Fin n)) (y1 y2 : Fin n)
    (hy1 : y1 ∈ Y1) (hy2 : y2 ∈ Y2) :
    (permFiberAll Y1 Y2 y1 y2).Nonempty := by
  classical
  refine ⟨1, ?_⟩
  have hsymm : (Equiv.symm (1 : Equiv.Perm (Fin n))) = 1 := Equiv.refl_symm
  simp only [permFiberAll, Finset.mem_filter, Finset.mem_univ, true_and, hsymm]
  exact ⟨hy1, hy2⟩

/-- Source Definition 2 (page 3), single-degree case: a bipartite graph
`K ⊆ Y1 × Y2` in which every `i ∈ Y1` has degree `d` and every `j ∈ Y2` has
degree `e`. The general Definition 2 allows lists of degrees; the source only
uses this single-degree instance for the triangle and associativity bounds. -/
def IsType {n : ℕ} (K : Finset (Fin n × Fin n)) (Y1 Y2 : Finset (Fin n)) (d e : ℕ) :
    Prop :=
  (∀ i ∈ Y1, (K.filter (fun p => p.1 = i)).card = d) ∧
    ∀ j ∈ Y2, (K.filter (fun p => p.2 = j)).card = e

/-- Definition 2's consistency equation `Σ n_i d_i = Σ m_j g_j`, single-degree
case: a type `({(l, d)}, {(g, e)})` graph satisfies `l * d = g * e`, because both
sides count the edges of `K`. -/
theorem IsType.card_mul_eq {n : ℕ} {K : Finset (Fin n × Fin n)}
    {Y1 Y2 : Finset (Fin n)} {d e : ℕ} (htype : IsType K Y1 Y2 d e)
    (hK : ∀ p ∈ K, p.1 ∈ Y1 ∧ p.2 ∈ Y2) : Y1.card * d = Y2.card * e := by
  classical
  have hleft : K.card = Y1.card * d := by
    have hmaps : Set.MapsTo (fun p : Fin n × Fin n => p.1) (↑K : Set _) (↑Y1 : Set _) :=
      fun p hp => (hK p hp).1
    rw [Finset.card_eq_sum_card_fiberwise hmaps]
    rw [Finset.sum_congr rfl (fun i hi => htype.1 i hi),
      Finset.sum_const_nat (fun _ _ => rfl)]
  have hright : K.card = Y2.card * e := by
    have hmaps : Set.MapsTo (fun p : Fin n × Fin n => p.2) (↑K : Set _) (↑Y2 : Set _) :=
      fun p hp => (hK p hp).2
    rw [Finset.card_eq_sum_card_fiberwise hmaps]
    rw [Finset.sum_congr rfl (fun j hj => htype.2 j hj),
      Finset.sum_const_nat (fun _ _ => rfl)]
  rw [← hleft, hright]

/-- Source Lemma 10 (page 16) in the conditional form its proof and its use in
Lemma 9 actually require: the number of permutations of the conditioning event
`σ⁻¹ y1 ∈ Y1 ∧ σ⁻¹ y2 ∈ Y2` for which `{y1, y2}` is an edge of `σ(K)` is the
`d/g` fraction of that event.

Cross-multiplied, the statement is `|B| * g = |A| * d`, which is the source's
double count `c * (l*d) = (l*g) * (p*c)` with the common fibre size `c`
cancelled. The source's membership hypothesis `(y1, y2) ∈ Y1 × Y2` is only
needed for the conditioning event to be nonempty (see
`permFiberAll_nonempty`) and does not enter the identity itself. -/
theorem lemma10_pair_ratio {n : ℕ} (Y1 Y2 : Finset (Fin n))
    (K : Finset (Fin n × Fin n)) (y1 y2 : Fin n) (d : ℕ)
    (hne : y1 ≠ y2) (hdisj : Disjoint Y1 Y2)
    (hK : ∀ p ∈ K, p.1 ∈ Y1 ∧ p.2 ∈ Y2)
    (hdeg : ∀ i ∈ Y1, (K.filter (fun p => p.1 = i)).card = d) :
    (permEdgeHit K Y1 Y2 y1 y2).card * Y2.card
      = (permFiberAll Y1 Y2 y1 y2).card * d := by
  classical
  -- the type of `K` gives `|K| = |Y1| * d`
  have hKcard : K.card = Y1.card * d := by
    have hmaps : Set.MapsTo (fun p : Fin n × Fin n => p.1) (↑K : Set _) (↑Y1 : Set _) :=
      fun p hp => (hK p hp).1
    rw [Finset.card_eq_sum_card_fiberwise hmaps]
    rw [Finset.sum_congr rfl (fun i hi => hdeg i hi), Finset.sum_const_nat (fun _ _ => rfl)]
  rw [permEdgeHit_card Y1 Y2 K y1 y2 hne hdisj hK,
    permFiberAll_card Y1 Y2 y1 y2 hne hdisj, hKcard]
  ring

/-- Source Lemma 10 (page 16), conditional form, as a ratio of counts: over the
conditioning event `σ⁻¹ y1 ∈ Y1 ∧ σ⁻¹ y2 ∈ Y2`, the probability that `{y1, y2}`
is an edge of `σ(K)` is `d / g` with `g = |Y2|`. -/
theorem lemma10_pair_probability {n : ℕ} (Y1 Y2 : Finset (Fin n))
    (K : Finset (Fin n × Fin n)) (y1 y2 : Fin n) (d : ℕ)
    (hy1 : y1 ∈ Y1) (hy2 : y2 ∈ Y2) (hne : y1 ≠ y2) (hdisj : Disjoint Y1 Y2)
    (hK : ∀ p ∈ K, p.1 ∈ Y1 ∧ p.2 ∈ Y2)
    (hdeg : ∀ i ∈ Y1, (K.filter (fun p => p.1 = i)).card = d) :
    ((permEdgeHit K Y1 Y2 y1 y2).card : ℚ) / ((permFiberAll Y1 Y2 y1 y2).card : ℚ)
      = (d : ℚ) / (Y2.card : ℚ) := by
  have hnat := lemma10_pair_ratio Y1 Y2 K y1 y2 d hne hdisj hK hdeg
  have hcast : ((permEdgeHit K Y1 Y2 y1 y2).card : ℚ) * (Y2.card : ℚ)
      = ((permFiberAll Y1 Y2 y1 y2).card : ℚ) * (d : ℚ) := by
    have := congrArg (fun m : ℕ => (m : ℚ)) hnat
    push_cast at this
    exact this
  have hA : (permFiberAll Y1 Y2 y1 y2).card ≠ 0 :=
    (permFiberAll_nonempty Y1 Y2 y1 y2 hy1 hy2).card_pos.ne'
  have hY2 : Y2.card ≠ 0 := (Finset.card_pos.mpr ⟨y2, hy2⟩).ne'
  rw [div_eq_div_iff (by exact_mod_cast hA) (by exact_mod_cast hY2)]
  rw [mul_comm (d : ℚ)]
  exact hcast

/-- Source Lemma 10 (page 16), conditional form, stated with the *type*
hypothesis of Definition 2 instead of an explicit left-degree hypothesis: for a
type `({(l, d)}, {(g, e)})` bipartite graph `K` between `Y1` and `Y2` (so
`l = |Y1|`, `g = |Y2|`), the probability of `{y1, y2} ∈ σ(K)` over the
conditioning event is `d / g`. -/
theorem lemma10_pair_probability_of_type {n : ℕ} (Y1 Y2 : Finset (Fin n))
    (K : Finset (Fin n × Fin n)) (y1 y2 : Fin n) (d e : ℕ)
    (hy1 : y1 ∈ Y1) (hy2 : y2 ∈ Y2) (hne : y1 ≠ y2) (hdisj : Disjoint Y1 Y2)
    (hK : ∀ p ∈ K, p.1 ∈ Y1 ∧ p.2 ∈ Y2) (htype : IsType K Y1 Y2 d e) :
    ((permEdgeHit K Y1 Y2 y1 y2).card : ℚ) / ((permFiberAll Y1 Y2 y1 y2).card : ℚ)
      = (d : ℚ) / (Y2.card : ℚ) :=
  lemma10_pair_probability Y1 Y2 K y1 y2 d hy1 hy2 hne hdisj hK htype.1

end Qatlib.Papers.TriangleFind12.MainResults
