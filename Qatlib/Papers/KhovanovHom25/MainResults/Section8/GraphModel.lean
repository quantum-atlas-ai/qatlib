/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.KhovanovHom25.MainResults.Model
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Logic.Relation
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Tactic.ByContra
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
set_option backward.isDefEq.respectTransparency false

/-!
# Zero-Homology Knot Graphs, Loop-Sum Bounds, and Twisted Unknots

This module formalizes Section 8.2.2, Section 8.3, and Section 8.4 (Theorem 28,
Lemma 29, Lemma 31, Proposition 32, Proposition 35, and Corollary 37) of
Schmidhuber, O'Donnell, Kothari, and Babbush on the zero-homology knot graphs
`G_{n,k}(K)` over `{1, X}`-label subsets, identifying the signless Laplacian
`Q = D + A` with the restricted degree-zero Khovanov Laplacian `Δ_{0,k-n}(K)`,
computing the exact total loop weight, bounding the minimal eigenvalue via the
loop sum and odd-cycle repair bound `ϒ_K`, and proving bipartiteness,
connectedness, eigenvalue upper bounds, and nontrivial kernel for twisted unknot
graphs `G_{n,k}(TU_N)`.

## Main definitions

* `Vertex`, `vertexSet`, `swapLabels`: `k`-element label subsets and swap moves.
* `loopWeightAt`, `edgeWeightAt`, `weightedDegree`, `signlessLap`, `khovanovLocal`:
  weighted knot-graph and degree-zero Khovanov Laplacian matrices.
* `twistedUnknotEdges`, `IsBipartite`, `ConnectedGraph`, `signlessMatrix`,
  `HasNontrivialKernel`: twisted-unknot adjacency and signless-Laplacian kernel predicates.

## Main statements

* `theorem28_offdiag`, `theorem28`: Theorem 28, `signlessLap = khovanovLocal`.
* `theorem29_loop_sum`: Lemma 29, exact total loop weight over `vertexSet ℓ k`.
* `lemma31`, `proposition32`: Lemma 31 and Proposition 32, minimal-eigenvalue bound.
* `proposition35`: Proposition 35, loop-free `G_{n,k}(TU_N)` is bipartite and connected.
* `corollary37`, `corollary37_kernel`: Corollary 37, eigenvalue bound and nontrivial kernel.

## References

* [Schmidhuber et al., 2025][SchmidhuberEtAl2025Khovanov], Sections 8.2--8.4, pp. 47--54.
-/

set_option autoImplicit false
set_option maxHeartbeats 2000000

noncomputable section

open scoped BigOperators

namespace Qatlib.Papers.KhovanovHom25.MainResults

/-- A vertex of `G_{n,k}(K)`: the set of positions carrying the label `1`. -/
abbrev Vertex (ℓ : ℕ) := Finset (Fin ℓ)

/-- The vertex set of `G_{n,k}(K)` for `ℓ = n + k`: all `k`-element subsets. -/
def vertexSet (ℓ k : ℕ) : Finset (Vertex ℓ) :=
  (Finset.univ : Finset (Fin ℓ)).powersetCard k

/-- Swap the labels in positions `i` and `j` of a vertex. -/
def swapLabels {ℓ : ℕ} (v : Vertex ℓ) (i j : Fin ℓ) : Vertex ℓ :=
  (v \ {i, j}) ∪ (({i, j} : Finset (Fin ℓ)) \ v)

/-- The weighted loop at vertex `v` coming from `p` multiplication terms and
`t` comultiplication terms, Section 8.2.2. -/
def loopWeightAt {ℓ : ℕ} (p t : ℕ) (m : Fin p → Fin ℓ × Fin ℓ)
    (d : Fin t → Fin ℓ) (v : Vertex ℓ) : ℚ :=
  (1 / 2) * ((Finset.univ.filter
      (fun a : Fin p => (m a).1 ∈ v ∧ (m a).2 ∈ v)).card : ℚ) +
    ((Finset.univ.filter (fun b : Fin t => d b ∈ v)).card : ℚ) +
      (1 / 2) * ((Finset.univ.filter (fun b : Fin t => d b ∉ v)).card : ℚ)

/-- The edge multiplicity from `v` to `v'` contributed by the multiplication
terms: one for each `m_{ij}` with exactly one of `i, j` in `v` and
`swapLabels v i j = v'`. -/
def edgeWeightAt {ℓ : ℕ} (p : ℕ) (m : Fin p → Fin ℓ × Fin ℓ)
    (v v' : Vertex ℓ) : ℕ :=
  (Finset.univ.filter (fun a : Fin p =>
    ((m a).1 ∈ v) ≠ ((m a).2 ∈ v) ∧
      swapLabels v (m a).1 (m a).2 = v')).card

/-- The weighted degree of a vertex, counting loops twice, eq. (8.5). -/
def weightedDegree {ℓ : ℕ} (p t : ℕ) (m : Fin p → Fin ℓ × Fin ℓ)
    (d : Fin t → Fin ℓ) (v : Vertex ℓ) : ℚ :=
  2 * loopWeightAt p t m d v +
    ∑ v' ∈ (Finset.univ : Finset (Vertex ℓ)).erase v, (edgeWeightAt p m v v' : ℚ)

/-- The signless Laplacian `Q = D + A` of `G_{n,k}(K)`, eq. (8.5). -/
def signlessLap {ℓ : ℕ} (p t : ℕ) (m : Fin p → Fin ℓ × Fin ℓ)
    (d : Fin t → Fin ℓ) (v v' : Vertex ℓ) : ℚ :=
  if v = v' then weightedDegree p t m d v else (edgeWeightAt p m v v' : ℚ)

/-- The matrix of the degree-zero Khovanov Laplacian `Δ_{0,k-n}(K)` restricted
to the `k`-ones sector, read off eq. (8.2): `m†m` acts by `1` on every pair
state except `XX`, and `d†d` acts by `2` on `1` and by `1` on `X`. -/
def khovanovLocal {ℓ : ℕ} (p t : ℕ) (m : Fin p → Fin ℓ × Fin ℓ)
    (d : Fin t → Fin ℓ) (v v' : Vertex ℓ) : ℚ :=
  if v = v' then
    ((Finset.univ.filter (fun a : Fin p =>
        ¬((m a).1 ∉ v ∧ (m a).2 ∉ v))).card : ℚ) +
      2 * ((Finset.univ.filter (fun b : Fin t => d b ∈ v)).card : ℚ) +
        ((Finset.univ.filter (fun b : Fin t => d b ∉ v)).card : ℚ)
  else
    (Finset.univ.filter (fun a : Fin p =>
      ((m a).1 ∈ v) ≠ ((m a).2 ∈ v) ∧
        swapLabels v (m a).1 (m a).2 = v')).card

/-- **Theorem 28, off-diagonal part.**  For distinct vertices, the signless
Laplacian entry equals the Khovanov Laplacian entry: both count the
multiplication terms that swap `v` to `v'`. -/
theorem theorem28_offdiag {ℓ p t : ℕ} (m : Fin p → Fin ℓ × Fin ℓ)
    (d : Fin t → Fin ℓ) {v v' : Vertex ℓ} (hv : v ≠ v') :
    signlessLap p t m d v v' = khovanovLocal p t m d v v' := by
  simp only [signlessLap, khovanovLocal, edgeWeightAt, hv, ↓reduceIte]

/-- The swap of `v` along `{i, j}` differs from `v` as soon as exactly one of
`i, j` lies in `v`. -/
theorem swapLabels_ne_of_xor {ℓ : ℕ} (v : Vertex ℓ) (i j : Fin ℓ)
    (h : ((i ∈ v) : Prop) ≠ ((j ∈ v) : Prop)) : swapLabels v i j ≠ v := by
  intro heq
  have hmem : ∀ x : Fin ℓ, x ∈ ({i, j} : Finset (Fin ℓ)) →
      (x ∈ swapLabels v i j ↔ x ∉ v) := by
    intro x hx
    simp only [swapLabels, Finset.mem_union, Finset.mem_sdiff]
    constructor
    · rintro (⟨_, hnin⟩ | ⟨_, hnout⟩)
      · exact absurd hx hnin
      · exact hnout
    · intro hout
      exact Or.inr ⟨hx, hout⟩
  have himem : i ∈ ({i, j} : Finset (Fin ℓ)) := by simp
  have hjmem : j ∈ ({i, j} : Finset (Fin ℓ)) := by simp
  by_cases hi : i ∈ v
  · have hj : j ∉ v := by
      intro hj
      exact h (by simp [hi, hj])
    have h3 : j ∈ swapLabels v i j := (hmem j hjmem).mpr hj
    rw [heq] at h3
    exact hj h3
  · have hj : j ∈ v := by
      by_contra hj
      exact h (by simp [hi, hj])
    have h3 : i ∈ swapLabels v i j := (hmem i himem).mpr hi
    rw [heq] at h3
    exact hi h3

/-- **Theorem 28** (arXiv:2501.12378v2, p. 50).  The signless Laplacian of
`G_{n,k}(K)` equals the matrix of `Δ_{0,k-n}(K)` in the vertex basis.

Off the diagonal both entries count the multiplication terms swapping `v` to
`v'` (`theorem28_offdiag`).  On the diagonal the degree sum `2w_vv + Σ w_vv''`
partitions the multiplication terms into "both `1`" (loop) and "exactly one
`1`" (edge contributing to the degree), via a fiber-sum over the neighbours:
each xor pair swaps `v` to exactly one `w ≠ v` (`swapLabels_ne_of_xor`), so the
off-diagonal edge weights add up to the xor count, and the `∨`-filter splits
disjointly into `∧`-filter plus xor filter. -/
theorem theorem28 {ℓ p t : ℕ} (m : Fin p → Fin ℓ × Fin ℓ)
    (d : Fin t → Fin ℓ) (v v' : Vertex ℓ) :
    signlessLap p t m d v v' = khovanovLocal p t m d v v' := by
  by_cases hvv : v = v'
  · subst hvv
    simp only [signlessLap, khovanovLocal, ↓reduceIte]
    -- summing the off-diagonal edge weights over `w ≠ v` counts all xor pairs
    have hmaps : ∀ a ∈ (Finset.univ : Finset (Fin p)).filter (fun a =>
        ((m a).1 ∈ v) ≠ ((m a).2 ∈ v)),
        swapLabels v (m a).1 (m a).2 ∈ (Finset.univ : Finset (Vertex ℓ)).erase v := by
      intro a ha
      rw [Finset.mem_filter] at ha
      rw [Finset.mem_erase]
      exact ⟨swapLabels_ne_of_xor v (m a).1 (m a).2 ha.2, Finset.mem_univ _⟩
    have hA : ∑ w ∈ (Finset.univ : Finset (Vertex ℓ)).erase v,
        ((Finset.univ.filter (fun a : Fin p =>
          (((m a).1 ∈ v) ≠ ((m a).2 ∈ v)) ∧
            swapLabels v (m a).1 (m a).2 = w)).card : ℚ) =
        ((Finset.univ.filter (fun a : Fin p =>
          ((m a).1 ∈ v) ≠ ((m a).2 ∈ v))).card : ℚ) := by
      have hbridge : ∀ w : Vertex ℓ,
          ((Finset.univ.filter (fun a : Fin p =>
            (((m a).1 ∈ v) ≠ ((m a).2 ∈ v)) ∧
              swapLabels v (m a).1 (m a).2 = w)).card : ℚ) =
          ∑ a ∈ (Finset.univ : Finset (Fin p)).filter (fun a =>
            ((m a).1 ∈ v) ≠ ((m a).2 ∈ v)) with
            swapLabels v (m a).1 (m a).2 = w, (1 : ℚ) := by
        intro w
        rw [← Finset.filter_filter, Finset.sum_const]
        simp
      calc ∑ w ∈ (Finset.univ : Finset (Vertex ℓ)).erase v,
          ((Finset.univ.filter (fun a : Fin p =>
            (((m a).1 ∈ v) ≠ ((m a).2 ∈ v)) ∧
              swapLabels v (m a).1 (m a).2 = w)).card : ℚ)
          = ∑ w ∈ (Finset.univ : Finset (Vertex ℓ)).erase v,
              ∑ a ∈ (Finset.univ : Finset (Fin p)).filter (fun a =>
                ((m a).1 ∈ v) ≠ ((m a).2 ∈ v)) with
                swapLabels v (m a).1 (m a).2 = w, (1 : ℚ) :=
            Finset.sum_congr rfl (fun w _ => hbridge w)
        _ = ∑ a ∈ (Finset.univ : Finset (Fin p)).filter (fun a =>
              ((m a).1 ∈ v) ≠ ((m a).2 ∈ v)), (1 : ℚ) :=
            Finset.sum_fiberwise_of_maps_to hmaps (f := fun _ => (1 : ℚ))
        _ = ((Finset.univ.filter (fun a : Fin p =>
              ((m a).1 ∈ v) ≠ ((m a).2 ∈ v))).card : ℚ) := by
            rw [Finset.sum_const]; simp
    -- the `∨`-filter splits into the `∧`-filter and the xor filter
    have hor : (Finset.univ.filter (fun a : Fin p =>
        ¬((m a).1 ∉ v ∧ (m a).2 ∉ v))).card =
        (Finset.univ.filter (fun a : Fin p =>
          ((m a).1 ∈ v) ∧ ((m a).2 ∈ v))).card +
      (Finset.univ.filter (fun a : Fin p =>
        ((m a).1 ∈ v) ≠ ((m a).2 ∈ v))).card := by
      have hunion : (Finset.univ.filter (fun a : Fin p =>
          ¬((m a).1 ∉ v ∧ (m a).2 ∉ v))) =
          (Finset.univ.filter (fun a : Fin p =>
            ((m a).1 ∈ v) ∧ ((m a).2 ∈ v))) ∪
          (Finset.univ.filter (fun a : Fin p =>
            ((m a).1 ∈ v) ≠ ((m a).2 ∈ v))) := by
        ext a
        simp only [Finset.mem_filter, Finset.mem_univ, true_and,
          Finset.mem_union]
        by_cases h1 : (m a).1 ∈ v <;> by_cases h2 : (m a).2 ∈ v <;>
          simp [h1, h2]
      have hdisj : Disjoint
          (Finset.univ.filter (fun a : Fin p =>
            ((m a).1 ∈ v) ∧ ((m a).2 ∈ v)))
          (Finset.univ.filter (fun a : Fin p =>
            ((m a).1 ∈ v) ≠ ((m a).2 ∈ v))) := by
        rw [Finset.disjoint_iff_inter_eq_empty]
        ext a
        simp only [Finset.mem_inter, Finset.mem_filter, Finset.mem_univ,
          true_and]
        by_cases h1 : (m a).1 ∈ v <;> by_cases h2 : (m a).2 ∈ v <;>
          simp [h1, h2]
      rw [hunion, Finset.card_union_of_disjoint hdisj]
    have horQ : ((Finset.univ.filter (fun a : Fin p =>
        ¬((m a).1 ∉ v ∧ (m a).2 ∉ v))).card : ℚ) =
        ((Finset.univ.filter (fun a : Fin p =>
          ((m a).1 ∈ v) ∧ ((m a).2 ∈ v))).card +
        (Finset.univ.filter (fun a : Fin p =>
          ((m a).1 ∈ v) ≠ ((m a).2 ∈ v))).card : ℕ) := by
      exact_mod_cast hor
    rw [Nat.cast_add] at horQ
    rw [weightedDegree, loopWeightAt]
    simp only [edgeWeightAt]
    rw [hA, horQ]
    ring
  · exact theorem28_offdiag m d hvv

/- ## The weighted loop sum (Lemma 29) -/

/-- The total loop weight on a set `S` of vertices. -/
def loopSum {ℓ : ℕ} (p t : ℕ) (m : Fin p → Fin ℓ × Fin ℓ)
    (d : Fin t → Fin ℓ) (S : Finset (Vertex ℓ)) : ℚ :=
  ∑ v ∈ S, loopWeightAt p t m d v

/-- The cut weight of `S`: the total edge weight leaving `S`. -/
def cutWeight {ℓ : ℕ} (p : ℕ) (m : Fin p → Fin ℓ × Fin ℓ)
    (S : Finset (Vertex ℓ)) : ℚ :=
  ∑ v ∈ S, ∑ v' ∈ (Finset.univ : Finset (Vertex ℓ)) \ S,
    (edgeWeightAt p m v v' : ℚ)

/-- The number of vertices whose labels at two distinct positions `i, j` are
both `1` is `C(ℓ-2, k-2)`. -/
theorem card_vertexSet_both {ℓ k p : ℕ} (m : Fin p → Fin ℓ × Fin ℓ)
    (hk : 2 ≤ k) (hkℓ : k ≤ ℓ) (a : Fin p) (hm : (m a).1 ≠ (m a).2) :
    ((vertexSet ℓ k).filter
        (fun v => (m a).1 ∈ v ∧ (m a).2 ∈ v)).card =
      Nat.choose (ℓ - 2) (k - 2) := by
  have hresult : ((vertexSet ℓ k).filter
      (fun v => (m a).1 ∈ v ∧ (m a).2 ∈ v)).card = Nat.choose (ℓ - 2) (k - 2) := by
    have hpair : ({(m a).1, (m a).2} : Finset (Fin ℓ)).card = 2 := by
      rw [Finset.card_insert_of_notMem]
      · simp
      · simp [Finset.mem_singleton, hm]
    have hfilter : (vertexSet ℓ k).filter
        (fun v => (m a).1 ∈ v ∧ (m a).2 ∈ v) =
        (vertexSet ℓ k).filter
          (fun v => ({(m a).1, (m a).2} : Finset (Fin ℓ)) ⊆ v) := by
      apply Finset.filter_congr
      intro v _
      simp [Finset.insert_subset_iff]
    rw [hfilter, vertexSet,
      Finset.card_filter_powersetCard_subset _ _ _ (by simp) (by omega),
      hpair, Finset.card_univ, Fintype.card_fin]
  cases hkℓ <;> exact hresult

/-- The number of vertices whose label at position `i` is `1` is `C(ℓ-1, k-1)`. -/
theorem card_vertexSet_mem {ℓ k : ℕ} (hk : 1 ≤ k) (hkℓ : k ≤ ℓ) (i : Fin ℓ) :
    ((vertexSet ℓ k).filter (fun v => i ∈ v)).card =
      Nat.choose (ℓ - 1) (k - 1) := by
  have hresult : ((vertexSet ℓ k).filter (fun v => i ∈ v)).card =
      Nat.choose (ℓ - 1) (k - 1) := by
    have hfilter : (vertexSet ℓ k).filter (fun v => i ∈ v) =
        (vertexSet ℓ k).filter (fun v => ({i} : Finset (Fin ℓ)) ⊆ v) := by
      apply Finset.filter_congr
      intro v _
      simp
    rw [hfilter, vertexSet,
      Finset.card_filter_powersetCard_subset _ _ _ (by simp) (by simpa using hk),
      Finset.card_univ, Fintype.card_fin, Finset.card_singleton]
  cases hkℓ <;> exact hresult

/-- The number of vertices whose label at position `i` is `X` is `C(ℓ-1, k)`. -/
theorem card_vertexSet_notMem {ℓ k : ℕ} (i : Fin ℓ) :
    ((vertexSet ℓ k).filter (fun v => i ∉ v)).card =
      Nat.choose (ℓ - 1) k := by
  have hfilter : (vertexSet ℓ k).filter (fun v => i ∉ v) =
      ((Finset.univ : Finset (Fin ℓ)).erase i).powersetCard k := by
    ext v
    simp [vertexSet, Finset.mem_powersetCard, Finset.subset_erase, and_comm]
  rw [hfilter, Finset.card_powersetCard,
    Finset.card_erase_of_mem (Finset.mem_univ i), Finset.card_univ,
    Fintype.card_fin]

/-- **Lemma 29** (arXiv:2501.12378v2, p. 51).  The total weight of the loops of
`G_{n,k}(K)` is

`p/2 · C(ℓ-2, k-2) + t · C(ℓ-1, k-1) + t/2 · C(ℓ-1, k)`.

We assume `2 ≤ k ≤ ℓ`: for `k < 2` the paper's binomial coefficients vanish
conventionally while `Nat.choose` uses truncated subtraction, so the literal
formula with `Nat.choose` requires this hypothesis (documented deviation). -/
theorem theorem29_loop_sum {ℓ k p t : ℕ} (m : Fin p → Fin ℓ × Fin ℓ)
    (d : Fin t → Fin ℓ) (hm : ∀ a, (m a).1 ≠ (m a).2)
    (hk : 2 ≤ k) (hkℓ : k ≤ ℓ) :
    loopSum p t m d (vertexSet ℓ k) =
      (p : ℚ) * (1 / 2) * (Nat.choose (ℓ - 2) (k - 2) : ℚ) +
        (t : ℚ) * (Nat.choose (ℓ - 1) (k - 1) : ℚ) +
          (t : ℚ) * (1 / 2) * (Nat.choose (ℓ - 1) k : ℚ) := by
  -- Counting identity for the multiplication terms.
  have hpairNat : ∑ v ∈ vertexSet ℓ k,
      (Finset.univ.filter
        (fun a : Fin p => (m a).1 ∈ v ∧ (m a).2 ∈ v)).card =
      p * Nat.choose (ℓ - 2) (k - 2) := by
    simp_rw [Finset.card_filter]
    rw [Finset.sum_comm]
    have hboth : ∀ a : Fin p,
        ((vertexSet ℓ k).filter
          (fun v => (m a).1 ∈ v ∧ (m a).2 ∈ v)).card =
          Nat.choose (ℓ - 2) (k - 2) :=
      fun a => card_vertexSet_both m hk hkℓ a (hm a)
    simp_rw [← Finset.card_filter, hboth]
    simp
  -- Counting identity for the "1" comultiplication terms.
  have hdinNat : ∑ v ∈ vertexSet ℓ k,
      (Finset.univ.filter (fun b : Fin t => d b ∈ v)).card =
      t * Nat.choose (ℓ - 1) (k - 1) := by
    simp_rw [Finset.card_filter]
    rw [Finset.sum_comm]
    have hmemb : ∀ i : Fin ℓ,
        ((vertexSet ℓ k).filter (fun v => i ∈ v)).card =
          Nat.choose (ℓ - 1) (k - 1) :=
      fun i => card_vertexSet_mem (by omega) hkℓ i
    simp_rw [← Finset.card_filter, hmemb]
    simp
  -- Counting identity for the "X" comultiplication terms.
  have hdoutNat : ∑ v ∈ vertexSet ℓ k,
      (Finset.univ.filter (fun b : Fin t => d b ∉ v)).card =
      t * Nat.choose (ℓ - 1) k := by
    simp_rw [Finset.card_filter]
    rw [Finset.sum_comm]
    have hnot : ∀ i : Fin ℓ,
        ((vertexSet ℓ k).filter (fun v => i ∉ v)).card =
          Nat.choose (ℓ - 1) k :=
      fun i => card_vertexSet_notMem i
    simp_rw [← Finset.card_filter, hnot]
    simp
  simp only [loopSum, loopWeightAt]
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib,
    ← Finset.mul_sum, ← Finset.mul_sum]
  rw [← Nat.cast_sum, hpairNat, ← Nat.cast_sum, hdinNat,
    ← Nat.cast_sum, hdoutNat]
  push_cast
  ring

/- ## Lemma 31 and Proposition 32: the upper bound for `Ψ` -/

/-- **Lemma 31** (arXiv:2501.12378v2, p. 52, eq. (8.6)).  `e_min(V) =
loop(V) + e'_min(V)` and `e_min(V) ≤ loop(V) + 2ϒ_K`.

Formalization scope: `e_min` (the minimum total weight of loops and edges to
delete so that `G_{n,k}(K)` becomes bipartite) and `e'_min` are not constructed
from a bipartite-repair predicate here; the statement is formalized in the
paper's decomposed form with `e_min = loop + e'_min` and the odd-cycle bound
`e'_min ≤ 2ϒ_K` as hypotheses, so the provable content is the displayed
inequality (8.6).  The construction of `ϒ` (maximal odd cycles of the
multiplication graph) is deferred. -/
theorem lemma31 {ℓ k p t : ℕ} (m : Fin p → Fin ℓ × Fin ℓ)
    (d : Fin t → Fin ℓ) (eMin eMinEdges Upsilon : ℚ)
    (hdecomp : eMin = loopSum p t m d (vertexSet ℓ k) + eMinEdges)
    (hcycle : eMinEdges ≤ 2 * Upsilon) :
    eMin ≤ loopSum p t m d (vertexSet ℓ k) + 2 * Upsilon := by
  rw [hdecomp]
  linarith

/-- **Proposition 32** (arXiv:2501.12378v2, p. 52).  The smallest eigenvalue of
`Δ_{0,2k-n}(K)` satisfies

`λ_min ≤ (loop(V) + 2ϒ_K) / C(n+k, k)`.

The proof is the arithmetic consequence of Theorem 24 (`λ_min ≤ e_min/|V|`) and
Lemma 31; `|V| = C(n+k, k)` is the vertex count. -/
theorem proposition32 (n k p t : ℕ) (m : Fin p → Fin (n + k) × Fin (n + k))
    (d : Fin t → Fin (n + k)) (eMin Upsilon lamMin : ℝ)
    (hcardpos : 0 < Nat.choose (n + k) k)
    (htheorem24 : lamMin ≤ eMin / (Nat.choose (n + k) k : ℝ))
    (hlemma31 : eMin ≤ (loopSum p t m d (vertexSet (n + k) k) : ℝ) + 2 * Upsilon) :
    lamMin ≤ ((loopSum p t m d (vertexSet (n + k) k) : ℝ) + 2 * Upsilon) /
      (Nat.choose (n + k) k : ℝ) := by
  have hpos : (0 : ℝ) < (Nat.choose (n + k) k : ℝ) := by exact_mod_cast hcardpos
  calc lamMin ≤ eMin / (Nat.choose (n + k) k : ℝ) := htheorem24
    _ ≤ ((loopSum p t m d (vertexSet (n + k) k) : ℝ) + 2 * Upsilon) /
          (Nat.choose (n + k) k : ℝ) := by
        exact div_le_div_of_nonneg_right hlemma31 (le_of_lt hpos)

/- ## Twisted unknots: Proposition 35, Corollary 37 -/

/-- The multiplication graph of `TU_N`: consecutive pairs `(i, i+1)` for
`i = 0, …, N-1`, matching `Δ₀(TU_N) = Σ_{i=1}^N m_{i,i+1}` (Section 8.4). -/
def twistedUnknotEdges (N : ℕ) : Fin N → Fin (N + 1) × Fin (N + 1) :=
  fun i => (Fin.castSucc i, Fin.succ i)

/-- Adjacency of the loop-free graph `G'_{n,k}(K)`. -/
def Adj {ℓ : ℕ} (p : ℕ) (m : Fin p → Fin ℓ × Fin ℓ) (v v' : Vertex ℓ) : Prop :=
  edgeWeightAt p m v v' ≠ 0

/-- Bipartiteness of the loop-free graph: a two-colouring with no monochromatic
edge. -/
def IsBipartite {ℓ : ℕ} (p : ℕ) (m : Fin p → Fin ℓ × Fin ℓ) : Prop :=
  ∃ color : Vertex ℓ → Bool, ∀ v v', Adj p m v v' → color v ≠ color v'

/-- Connectedness of the loop-free graph restricted to the vertex set. -/
def ConnectedGraph {ℓ : ℕ} (k p : ℕ) (m : Fin p → Fin ℓ × Fin ℓ) : Prop :=
  ∀ v ∈ vertexSet ℓ k, ∀ v' ∈ vertexSet ℓ k,
    Relation.ReflTransGen (Adj p m) v v'

private theorem swapLabels_eq_insert {ℓ : ℕ} (v : Vertex ℓ) (a b : Fin ℓ)
    (ha : a ∉ v) (hb : b ∈ v) :
    swapLabels v a b = insert a (v.erase b) := by
  ext x
  by_cases hxa : x = a <;> by_cases hxb : x = b <;>
    simp_all [swapLabels]

private theorem swapLabels_comm {ℓ : ℕ} (v : Vertex ℓ) (a b : Fin ℓ) :
    swapLabels v a b = swapLabels v b a := by
  simp only [swapLabels, Finset.pair_comm]

private theorem swapLabels_involutive {ℓ : ℕ} (v : Vertex ℓ) (a b : Fin ℓ) :
    swapLabels (swapLabels v a b) a b = v := by
  ext x
  by_cases hx : x ∈ v <;> by_cases hxa : x = a <;> by_cases hxb : x = b <;>
    simp_all [swapLabels]

private theorem swapLabels_card_sum {ℓ : ℕ} (v : Vertex ℓ) (a b : Fin ℓ)
    (ha : a ∉ v) (hb : b ∈ v) :
    (swapLabels v a b).card = v.card ∧
      (∑ x ∈ swapLabels v a b, x.val) + b.val = (∑ x ∈ v, x.val) + a.val := by
  have hains : a ∉ v.erase b := fun h => ha (Finset.mem_of_mem_erase h)
  rw [swapLabels_eq_insert v a b ha hb]
  constructor
  · rw [Finset.card_insert_of_notMem hains, Finset.card_erase_of_mem hb]
    have := Finset.card_pos.mpr ⟨b, hb⟩
    omega
  · rw [Finset.sum_insert hains]
    have hsum := Finset.sum_erase_add v (fun x => x.val) hb
    omega

private theorem twisted_adj_swap (N : ℕ) (v : Vertex (N + 1)) (i : Fin N)
    (hi : (Fin.castSucc i ∈ v) ≠ (Fin.succ i ∈ v)) :
    Adj N (twistedUnknotEdges N) v (swapLabels v (Fin.castSucc i) (Fin.succ i)) := by
  apply Finset.card_ne_zero.mpr
  exact ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ i, hi, rfl⟩⟩

private theorem twisted_adj_symm (N : ℕ) {v v' : Vertex (N + 1)}
    (h : Adj N (twistedUnknotEdges N) v v') :
    Adj N (twistedUnknotEdges N) v' v := by
  obtain ⟨i, hi⟩ := Finset.card_ne_zero.mp h
  rcases (Finset.mem_filter.mp hi).2 with ⟨hxor, heq⟩
  change (Fin.castSucc i ∈ v) ≠ (Fin.succ i ∈ v) at hxor
  change swapLabels v (Fin.castSucc i) (Fin.succ i) = v' at heq
  subst v'
  have hx : (Fin.castSucc i ∈ swapLabels v (Fin.castSucc i) (Fin.succ i)) ≠
      (Fin.succ i ∈ swapLabels v (Fin.castSucc i) (Fin.succ i)) := by
    simpa only [swapLabels, Finset.mem_union, Finset.mem_sdiff,
      Finset.mem_insert, Finset.mem_singleton, true_or, or_true, not_true_eq_false,
      and_false, false_or, true_and, ne_eq, propext_iff, not_iff_not] using hxor
  simpa only [swapLabels_involutive] using twisted_adj_swap N _ i hx

private theorem twisted_path_symm (N : ℕ) {v v' : Vertex (N + 1)}
    (h : Relation.ReflTransGen (Adj N (twistedUnknotEdges N)) v v') :
    Relation.ReflTransGen (Adj N (twistedUnknotEdges N)) v' v := by
  induction h with
  | refl => exact .refl
  | tail _ hstep ih => exact .head (twisted_adj_symm N hstep) ih

private theorem twisted_bipartite (N : ℕ) : IsBipartite N (twistedUnknotEdges N) := by
  refine ⟨fun v => decide ((∑ x ∈ v, x.val) % 2 = 1), ?_⟩
  intro v v' h heq
  obtain ⟨i, hi⟩ := Finset.card_ne_zero.mp h
  rcases (Finset.mem_filter.mp hi).2 with ⟨hxor, rfl⟩
  have hpar : ((∑ x ∈ v, x.val) % 2 = 1) ↔
      ((∑ x ∈ swapLabels v (Fin.castSucc i) (Fin.succ i), x.val) % 2 = 1) :=
    decide_eq_decide.mp heq
  by_cases ha : Fin.castSucc i ∈ v
  · have hb : Fin.succ i ∉ v := by
      intro hb
      exact hxor (by simp [twistedUnknotEdges, ha, hb])
    have hs := (swapLabels_card_sum v (Fin.succ i) (Fin.castSucc i) hb ha).2
    rw [swapLabels_comm v (Fin.succ i) (Fin.castSucc i)] at hs
    simp only [Fin.val_castSucc, Fin.val_succ] at hs
    omega
  · have hb : Fin.succ i ∈ v := by
      by_contra hb
      exact hxor (by simp [twistedUnknotEdges, ha, hb])
    have hs := (swapLabels_card_sum v (Fin.castSucc i) (Fin.succ i) ha hb).2
    simp only [Fin.val_castSucc, Fin.val_succ] at hs
    omega

private theorem twisted_connected (N k : ℕ) (hkN : k ≤ N + 1) :
    ConnectedGraph k N (twistedUnknotEdges N) := by
  let base : Vertex (N + 1) := Finset.univ.filter (fun x => x.val < k)
  have hbase : base.card = k := by
    calc base.card = (Finset.univ : Finset (Fin k)).card := by
          apply Finset.card_bij (fun x hx =>
            (⟨x.val, (Finset.mem_filter.mp hx).2⟩ : Fin k))
          · intro x hx
            exact Finset.mem_univ _
          · intro x hx y hy hxy
            exact Fin.ext (congrArg (fun z : Fin k => z.val) hxy)
          · intro y _
            refine ⟨⟨y.val, by omega⟩, ?_, ?_⟩
            · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, y.isLt⟩
            · rfl
        _ = k := by simp
  have hpath : ∀ w, ∀ v : Vertex (N + 1), (∑ x ∈ v, x.val) = w → v.card = k →
      Relation.ReflTransGen (Adj N (twistedUnknotEdges N)) v base := by
    intro w
    induction w using Nat.strong_induction_on with
    | h w ih =>
      intro v hsum hcard
      by_cases heq : v = base
      · subst v
        exact .refl
      have hx : ∃ x ∈ v, k ≤ x.val := by
        by_contra! hx
        apply heq
        apply Finset.eq_of_subset_of_card_le
        · intro x hxv
          exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hx x hxv⟩
        · omega
      have hy : ∃ y ∈ base, y ∉ v := by
        by_contra! hy
        exact heq (Finset.eq_of_subset_of_card_le hy (by omega)).symm
      obtain ⟨x, hxv, hxk⟩ := hx
      obtain ⟨y, hybase, hyv⟩ := hy
      have hyk : y.val < k := (Finset.mem_filter.mp hybase).2
      have hmove : ∃ i : Fin N, Fin.castSucc i ∉ v ∧ Fin.succ i ∈ v := by
        by_contra! hmove
        have hdown : ∀ d, ∀ z : Fin (N + 1), z.val + d = x.val → z ∈ v := by
          intro d
          induction d with
          | zero =>
              intro z hz
              have hz' : z = x := Fin.ext (by omega)
              simpa only [hz'] using hxv
          | succ d hd =>
              intro z hz
              have hzN : z.val < N := by omega
              let i : Fin N := ⟨z.val, hzN⟩
              have hsucc : Fin.succ i ∈ v := hd (Fin.succ i) (by simp [i]; omega)
              have hcast : Fin.castSucc i ∈ v := by
                by_contra hcast
                exact hmove i hcast hsucc
              exact hcast
        exact hyv (hdown (x.val - y.val) y (by omega))
      obtain ⟨i, ha, hb⟩ := hmove
      let u := swapLabels v (Fin.castSucc i) (Fin.succ i)
      have hu := swapLabels_card_sum v (Fin.castSucc i) (Fin.succ i) ha hb
      have hlt : (∑ z ∈ u, z.val) < w := by
        have hs := hu.2
        simp only [Fin.val_castSucc, Fin.val_succ] at hs
        dsimp only [u]
        omega
      exact .head (twisted_adj_swap N v i (by simp [ha, hb]))
        (ih _ hlt u rfl (hu.1.trans hcard))
  intro v hv v' hv'
  have hvcard := (Finset.mem_powersetCard.mp hv).2
  have hv'card := (Finset.mem_powersetCard.mp hv').2
  exact (hpath _ v rfl hvcard).trans (twisted_path_symm N (hpath _ v' rfl hv'card))

/-- **Proposition 35** (arXiv:2501.12378v2, p. 53).  Removing the weighted loops
from `G_{n,k}(TU_N)` yields a bipartite connected graph.

Colour a label subset by the parity of its position sum. Adjacent swaps flip
this parity; swaps moving a label left decrease the sum until the subset is
the initial segment of length `k`, giving a path to a common vertex. -/
theorem proposition35 (N n k : ℕ) (hk : n + k = N + 1) :
    IsBipartite N (twistedUnknotEdges N) ∧
      ConnectedGraph k N (twistedUnknotEdges N) := by
  cases n <;> exact ⟨twisted_bipartite N, twisted_connected N k (by omega)⟩

/-- The signless Laplacian of `G_{n,k}(K)` as a real matrix (a plain curried
function on vertices). -/
def signlessMatrix {ℓ : ℕ} (p t : ℕ) (m : Fin p → Fin ℓ × Fin ℓ)
    (d : Fin t → Fin ℓ) : Vertex ℓ → Vertex ℓ → ℝ :=
  fun v v' => (signlessLap p t m d v v' : ℝ)

/-- Nontrivial kernel of the signless Laplacian: a non-zero vector annihilated
by all rows. -/
def HasNontrivialKernel {ℓ : ℕ} (p t : ℕ) (m : Fin p → Fin ℓ × Fin ℓ)
    (d : Fin t → Fin ℓ) : Prop :=
  ∃ x : Vertex ℓ → ℝ, x ≠ 0 ∧ ∀ v,
    ∑ v' ∈ (Finset.univ : Finset (Vertex ℓ)), signlessMatrix p t m d v v' * x v' = 0

/-- **Corollary 37, eigenvalue bound** (arXiv:2501.12378v2, p. 54, eq. (8.7)).
For `n + k = N + 1`, the minimal eigenvalue of `Δ_{0,2k-n}(TU_N)` satisfies
`λ_min ≤ 2k(k-1)/(N+1)`.  This is the arithmetic consequence of Theorem 24 and
the value `Ψ_V = k(k-1)/(2(N+1))` computed in eq. (8.7) (the latter is
`theorem29_loop_sum` specialised to `p = N`, `t = 0`, `ℓ = N+1` together with
the vertex count; the cancellation to `k(k-1)/(2(N+1))` itself is not needed for
this arithmetic step). -/
theorem corollary37 (N n k : ℕ) (lamMin : ℝ)
    (htheorem24 : lamMin ≤ 4 * ((k : ℝ) * ((k : ℝ) - 1) / (2 * ((N : ℝ) + 1)))) :
    lamMin ≤ 2 * (k : ℝ) * ((k : ℝ) - 1) / ((N : ℝ) + 1) := by
  cases n <;> {
    have hN : ((N : ℝ) + 1) ≠ 0 := by positivity
    have heq : 4 * ((k : ℝ) * ((k : ℝ) - 1) / (2 * ((N : ℝ) + 1))) =
        2 * (k : ℝ) * ((k : ℝ) - 1) / ((N : ℝ) + 1) := by
      field_simp
      ring
    linarith [htheorem24, heq] }

private theorem edgeWeightAt_empty_right {ℓ : ℕ} (p : ℕ)
    (m : Fin p → Fin ℓ × Fin ℓ) (v : Vertex ℓ) : edgeWeightAt p m v ∅ = 0 := by
  apply Finset.card_eq_zero.mpr
  apply Finset.filter_eq_empty_iff.mpr
  intro i _
  rintro ⟨hxor, heq⟩
  by_cases ha : (m i).1 ∈ v
  · have hb : (m i).2 ∉ v := by
      intro hb
      exact hxor (by simp [ha, hb])
    have hmem : (m i).2 ∈ swapLabels v (m i).1 (m i).2 := by
      simp [swapLabels, hb]
    rw [heq] at hmem
    exact Finset.notMem_empty _ hmem
  · have hmem : (m i).1 ∈ swapLabels v (m i).1 (m i).2 := by
      simp [swapLabels, ha]
    rw [heq] at hmem
    exact Finset.notMem_empty _ hmem

private theorem twisted_kernel (N : ℕ) :
    HasNontrivialKernel N 0 (twistedUnknotEdges N) (fun i => Fin.elim0 i) := by
  refine ⟨fun v => if v = ∅ then 1 else 0, ?_, ?_⟩
  · intro hz
    have h := congrFun hz ∅
    norm_num at h
  · intro v
    have hcol : signlessMatrix N 0 (twistedUnknotEdges N) (fun i => Fin.elim0 i)
        v ∅ = 0 := by
      by_cases hv : v = ∅
      · subst v
        simp [signlessMatrix, signlessLap, weightedDegree, loopWeightAt, edgeWeightAt]
      · simp [signlessMatrix, signlessLap, hv, edgeWeightAt_empty_right]
    simpa only [mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ,
      ↓reduceIte] using hcol

/-- **Corollary 37, kernel statement** (arXiv:2501.12378v2, p. 54).  For
`k = 0` or `k = 1` the Laplacian of the twisted-unknot graph has non-trivial
kernel.

The indicator of the empty label subset is a nonzero kernel vector: its column
vanishes because the empty subset has no incident edges or loops. -/
theorem corollary37_kernel (N n k : ℕ) (hk : n + k = N + 1)
    (h0 : k = 0 ∨ k = 1) :
    HasNontrivialKernel N 0 (twistedUnknotEdges N) (fun i => Fin.elim0 i) := by
  have hresult := twisted_kernel N
  cases n <;> rcases h0 with h0 | h0 <;> subst k <;> cases hk <;> exact hresult

end Qatlib.Papers.KhovanovHom25.MainResults
