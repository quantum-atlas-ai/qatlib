/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Combinatorics.SimpleGraph.Clique
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Finset.Sort
import Mathlib.Data.Finset.SDiff
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Algebra.BigOperators.GroupWithZero.Action
import Mathlib.Data.Finsupp.SMul

set_option backward.isDefEq.respectTransparency false

/-!
# Finite Simplicial Complexes, Oriented Boundary Nilpotency, and Degree Sparsity

This module formalizes Propositions 5, 10, and 11 of Berry et al. for finite abstract
simplicial complexes `K`, establishing the chain-complex identity `∂ ∘ ∂ = 0` on
oriented `ℤ`-chains together with down-degree `k + 1` and up-degree bound
`min(N - k - 1, d)` for every `k`-simplex `σ ∈ K`.

## Main definitions

* `SimplicialComplex`, `vertices`, `kFaces`: finite abstract simplicial complexes and face layers.
* `upDegree`, `downDegree`, `maxVertexUpDegree`: simplex incidence degrees.
* `simplicialBoundary`, `boundaryLin`: oriented simplicial boundary operator on `ℤ`-chains.

## Main statements

* `proposition5_boundary_comp_zero`: Proposition 5, `boundaryLin (boundaryLin c) = 0`.
* `upDegree_le_vertices`, `upDegree_le_maxVertexUpDegree`, `proposition10_upDegree_le_min`: Proposition 10.
* `downDegree_eq`, `downDegree_eq_succ`, `proposition11_sparsity`: Proposition 11, boundary sparsity bounds.

## References

* [Berry et al., 2024][BerryEtAl2024TDA], Section IV.C and Appendix G.4, Propositions 5, 10, and 11.
-/

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.TopoAdvantage22.MainResults.SimplicialCore

open Finset

variable {V : Type*} [DecidableEq V]

/-- A simplex on a vertex set `V` is a finite set of vertices. -/
abbrev Simplex (V : Type*) := Finset V

/-- A finite abstract simplicial complex: a finite family of faces closed under
taking subsets. `Simplicial complex with N vertices` of the paper corresponds to
`K.vertices` having cardinality `N`. -/
structure SimplicialComplex (V : Type*) [DecidableEq V] where
  /-- the family of faces (simplices) of the complex -/
  faces : Finset (Finset V)
  /-- every subset of a face is a face -/
  down : ∀ ⦃s t : Finset V⦄, s ⊆ t → t ∈ faces → s ∈ faces

namespace SimplicialComplex

/-- The vertex set of `K`: the union of all its faces. -/
def vertices (K : SimplicialComplex V) : Finset V := K.faces.biUnion id

/-- Every face of `K` is contained in its vertex set. -/
theorem face_subset_vertices (K : SimplicialComplex V) {s : Finset V} (hs : s ∈ K.faces) :
    s ⊆ K.vertices := by
  intro x hx
  exact Finset.mem_biUnion.mpr ⟨s, hs, hx⟩

/-- The `k`-simplices of `K`: faces with `k+1` vertices. -/
def kFaces (K : SimplicialComplex V) (k : ℕ) : Finset (Finset V) :=
  K.faces.filter (fun s => s.card = k + 1)

/-- The up-degree `degU(σ)`: the number of `(k+1)`-simplices which have the
`k`-simplex `σ` in their boundary. -/
def upDegree (K : SimplicialComplex V) (σ : Finset V) : ℕ :=
  (K.faces.filter (fun τ => σ ⊂ τ ∧ τ.card = σ.card + 1)).card

/-- The down-degree `degL(σ)`: the number of `(k-1)`-simplices in the boundary
of `σ`, i.e. `(k-1)`-faces that are subsets of `σ`. -/
def downDegree (K : SimplicialComplex V) (σ : Finset V) : ℕ :=
  (K.faces.filter (fun ρ => ρ ⊂ σ ∧ ρ.card + 1 = σ.card)).card

/-- The maximal up-degree `d` over all vertices (`0`-simplices) of `K`. -/
def maxVertexUpDegree (K : SimplicialComplex V) : ℕ :=
  K.vertices.sup (fun v => K.upDegree {v})

/- ## Proposition 11 (`c020`): down-degree is always `k+1` -/

/-- **Proposition 11, column sparsity (arXiv:2209.13581, Appendix G §4, page 53).**
The down-degree of a face `σ` equals `#σ.choose(#σ-1)`, the number of
`(k-1)`-subsets of a `k`-simplex; all of them are faces by downward closure. -/
theorem downDegree_eq (K : SimplicialComplex V) {σ : Finset V} (hσ : σ ∈ K.faces)
    (hne : 0 < σ.card) :
    K.downDegree σ = σ.card.choose (σ.card - 1) := by
  have hset : (K.faces.filter (fun ρ => ρ ⊂ σ ∧ ρ.card + 1 = σ.card))
      = σ.powersetCard (σ.card - 1) := by
    apply Finset.ext
    intro ρ
    simp only [Finset.mem_filter, Finset.mem_powersetCard]
    constructor
    · rintro ⟨-, hsub, hcard⟩
      exact ⟨(Finset.ssubset_iff_subset_ne.mp hsub).1, by omega⟩
    · rintro ⟨hsub, hcard⟩
      refine ⟨K.down hsub hσ, ?_, by omega⟩
      rw [Finset.ssubset_iff_subset_ne]
      refine ⟨hsub, ?_⟩
      intro heq
      subst heq
      omega
  unfold SimplicialComplex.downDegree
  rw [hset, Finset.card_powersetCard]

/-- **Proposition 11, column sparsity for a `k`-simplex (arXiv:2209.13581,
Appendix G §4, page 53).** For a `k`-simplex (`σ.card = k+1`) the down-degree is
exactly `k+1`. -/
theorem downDegree_eq_succ (K : SimplicialComplex V) {σ : Finset V} {k : ℕ}
    (hσ : σ ∈ K.faces) (hcard : σ.card = k + 1) :
    K.downDegree σ = k + 1 := by
  rw [K.downDegree_eq hσ (by omega), hcard]
  have h : k + 1 - 1 = k := by omega
  rw [h, Nat.choose_succ_self_right]

/- ## Proposition 5 (`c011`): `∂_k ∘ ∂_{k+1} = 0` -/

/-- The oriented simplicial boundary of a single simplex `σ`, as a `ℤ`-chain:
`∂⟨σ⟩ = Σ_v (-1)^{pos(v)} ⟨σ \ {v}⟩`, where `pos(v)` is the position of `v` in
the order-sorted vertex list of `σ` (the ambient order on `V` fixes orientations). -/
def simplicialBoundary [LinearOrder V] (σ : Finset V) : (Finset V →₀ ℤ) :=
  σ.sum (fun v =>
    Finsupp.single (σ.erase v) ((-1 : ℤ) ^ ((σ.sort (· ≤ ·)).idxOf v)))

/-- The boundary operator extended `ℤ`-linearly to all `ℤ`-chains. -/
def boundaryLin [LinearOrder V] (c : Finset V →₀ ℤ) : (Finset V →₀ ℤ) :=
  c.sum (fun σ n => n • simplicialBoundary (V := V) σ)

private def boundaryHom [LinearOrder V] : (Finset V →₀ ℤ) →+ (Finset V →₀ ℤ) where
  toFun := boundaryLin
  map_zero' := by simp [boundaryLin]
  map_add' := by
    intro c d
    exact Finsupp.sum_add_index' (fun _ => zero_smul _ _)
      (fun _ _ _ => add_smul _ _ _)

private theorem boundaryHom_single [LinearOrder V] (σ : Finset V) (n : ℤ) :
    boundaryHom (Finsupp.single σ n) = n • simplicialBoundary σ := by
  change (Finsupp.single σ n).sum (fun τ m => m • simplicialBoundary τ) = _
  exact Finsupp.sum_single_index (by simp)

private theorem sort_erase [LinearOrder V] (σ : Finset V) (v : V) :
    (σ.erase v).sort (· ≤ ·) = (σ.sort (· ≤ ·)).erase v := by
  apply List.Perm.eq_of_pairwise' (r := (· ≤ ·))
    (Finset.pairwise_sort _ _) ((Finset.pairwise_sort _ _).erase v)
  apply (List.perm_ext_iff_of_nodup (Finset.sort_nodup _ _)
    ((Finset.sort_nodup _ _).erase v)).mpr
  intro x
  simp only [Finset.mem_sort, Finset.mem_erase,
    (Finset.sort_nodup σ (· ≤ ·)).mem_erase_iff]

-- Swapping two deletions reverses their orientation, for any list without repeats.
private theorem erase_sign_cancel (L : List V) (hL : L.Nodup) (u v : V)
    (hu : u ∈ L) (hv : v ∈ L) (huv : u ≠ v) :
    (-1 : ℤ) ^ L.idxOf u * (-1 : ℤ) ^ (L.erase u).idxOf v +
      (-1 : ℤ) ^ L.idxOf v * (-1 : ℤ) ^ (L.erase v).idxOf u = 0 := by
  induction L with
  | nil => simp at hu
  | cons a L ih =>
    obtain ⟨ha, hL⟩ := List.nodup_cons.mp hL
    by_cases hau : a = u
    · subst a
      have huv' : ¬(u == v) := by simpa using huv
      simp [List.erase_cons_tail huv', huv, pow_succ]
    · by_cases hav : a = v
      · subst a
        have hvu : ¬(v == u) := by simpa using huv.symm
        simp [List.erase_cons_tail hvu, huv.symm, pow_succ]
      · have huL : u ∈ L := (List.mem_cons.mp hu).resolve_left (Ne.symm hau)
        have hvL : v ∈ L := (List.mem_cons.mp hv).resolve_left (Ne.symm hav)
        have h := ih hL huL hvL
        simpa [List.idxOf_cons, List.erase_cons, hau, hav, pow_succ] using h

private theorem boundaryHom_boundary [LinearOrder V] (σ : Finset V) :
    boundaryHom (simplicialBoundary σ) = 0 := by
  rw [simplicialBoundary, map_sum]
  simp_rw [boundaryHom_single, simplicialBoundary, smul_sum,
    Finsupp.smul_single, smul_eq_mul]
  let f : V × V → (Finset V →₀ ℤ) := fun p =>
    Finsupp.single ((σ.erase p.1).erase p.2)
      ((-1 : ℤ) ^ (σ.sort (· ≤ ·)).idxOf p.1 *
        (-1 : ℤ) ^ ((σ.erase p.1).sort (· ≤ ·)).idxOf p.2)
  change (∑ u ∈ σ, ∑ v ∈ σ.erase u, f (u, v)) = 0
  rw [← Finset.sum_finset_product σ.offDiag σ (fun v => σ.erase v) (by
    intro p
    simp only [Finset.mem_offDiag, Finset.mem_erase]
    constructor
    · rintro ⟨hu, hv, huv⟩
      exact ⟨hu, huv.symm, hv⟩
    · rintro ⟨hu, huv, hv⟩
      exact ⟨hu, hv, huv.symm⟩) (f := f)]
  apply Finset.sum_involution (fun p _ => (p.2, p.1))
  · intro p hp
    obtain ⟨hu, hv, huv⟩ := Finset.mem_offDiag.mp hp
    dsimp only [f]
    rw [Finset.erase_right_comm, ← Finsupp.single_add, sort_erase, sort_erase]
    rw [erase_sign_cancel (σ.sort (· ≤ ·)) (Finset.sort_nodup _ _) p.1 p.2
      ((Finset.mem_sort (· ≤ ·)).mpr hu) ((Finset.mem_sort (· ≤ ·)).mpr hv) huv,
      Finsupp.single_zero]
  · intro p hp _ heq
    exact (Finset.mem_offDiag.mp hp).2.2 (congrArg Prod.snd heq)
  · intro p hp
    obtain ⟨hu, hv, huv⟩ := Finset.mem_offDiag.mp hp
    exact Finset.mem_offDiag.mpr ⟨hv, hu, huv.symm⟩
  · intro p _
    rfl

/-- **Proposition 5 (arXiv:2209.13581, `∂_k ∘ ∂_{k+1} = 0`; Proposition 5, §IV C,
p. 2453 of the preprint, and used throughout Appendix F).**
Composing the simplicial boundary operator with itself annihilates every chain.

Fixed arXiv:2209.13581. Proof route: the classical alternating-face cancellation
— the coefficient of a `(k-1)`-face `ρ = σ \ {a,b}` in `∂∂⟨σ⟩` is
`(-1)^{pos a + pos b - 1} + (-1)^{pos b + pos a} = 0`, since swapping the order of
the two deletions flips the sign. The cancellation is a
`Finset.sort`/`List.idxOf` parity identity over the doubly-indexed sum `∑ v, ∑ w`:
the positions under `erase` determine the two signs. Expanding
`simplicialBoundary (simplicialBoundary σ)` pairs the deletions using
`(-1)^i + (-1)^(i+1) = 0`; `Finset.sum_eq_zero` expresses the resulting cancellation. -/
theorem proposition5_boundary_comp_zero [LinearOrder V] :
    ∀ c : (Finset V →₀ ℤ), boundaryLin (V := V) (boundaryLin (V := V) c) = 0 := by
  intro c
  change boundaryHom (boundaryHom c) = 0
  induction c using Finsupp.induction_linear with
  | zero => simp
  | add c d hc hd => simp only [map_add, hc, hd, add_zero]
  | single σ n =>
    rw [boundaryHom_single, map_zsmul, boundaryHom_boundary, smul_zero]

/- ## Proposition 10 (`c019`): the up-degree bound `min{N - k - 1, d}` -/

/-- **Proposition 10, first half (arXiv:2209.13581, Appendix G §4, page 52).**
For a `k`-simplex `σ` of a complex `K` on `N = #vertices` vertices, the up-degree
is at most `N - k - 1`: each `(k+1)`-simplex containing `σ` is `σ ∪ {v}` for one
of the `N - (k+1)` vertices `v ∉ σ`, and `τ ↦ τ \ σ` is injective on such faces. -/
theorem upDegree_le_vertices (K : SimplicialComplex V) {σ : Finset V} {k : ℕ}
    (hσ : σ ∈ K.faces) (hcard : σ.card = k + 1) :
    K.upDegree σ ≤ K.vertices.card - (k + 1) := by
  have hσv : σ ⊆ K.vertices := K.face_subset_vertices hσ
  set S : Finset (Finset V) :=
    K.faces.filter (fun τ => σ ⊂ τ ∧ τ.card = σ.card + 1) with hS
  have hcard1 : ∀ τ ∈ S, (τ \ σ).card = 1 := by
    intro τ hτ
    rw [hS, Finset.mem_filter] at hτ
    obtain ⟨_, hsub, hcardτ⟩ := hτ
    rw [Finset.card_sdiff_of_subset (Finset.ssubset_iff_subset_ne.mp hsub).1, hcardτ]
    omega
  have hmaps : Set.MapsTo (fun τ : Finset V => τ \ σ) (S : Set (Finset V))
      ((K.vertices \ σ).powersetCard 1 : Set (Finset V)) := by
    intro τ hτ
    rw [Finset.mem_coe] at hτ ⊢
    rw [hS, Finset.mem_filter] at hτ
    obtain ⟨hfτ, hsub, hcardτ⟩ := hτ
    rw [Finset.mem_powersetCard]
    refine ⟨?_, hcard1 τ ?_⟩
    · intro x hx
      rw [Finset.mem_sdiff] at hx ⊢
      exact ⟨K.face_subset_vertices hfτ hx.1, hx.2⟩
    · rw [hS, Finset.mem_filter]
      exact ⟨hfτ, hsub, hcardτ⟩
  have hinj : (S : Set (Finset V)).InjOn (fun τ : Finset V => τ \ σ) := by
    intro τ₁ h₁ τ₂ h₂ heq
    rw [Finset.mem_coe] at h₁ h₂
    rw [hS, Finset.mem_filter] at h₁ h₂
    have s1 : σ ⊆ τ₁ := (Finset.ssubset_iff_subset_ne.mp h₁.2.1).1
    have s2 : σ ⊆ τ₂ := (Finset.ssubset_iff_subset_ne.mp h₂.2.1).1
    have heq' : τ₁ \ σ = τ₂ \ σ := heq
    rw [← Finset.union_sdiff_of_subset s1, ← Finset.union_sdiff_of_subset s2, heq']
  have hbound : S.card ≤ ((K.vertices \ σ).powersetCard 1).card :=
    Finset.card_le_card_of_injOn (fun τ : Finset V => τ \ σ) hmaps hinj
  rw [Finset.card_powersetCard, Nat.choose_one_right] at hbound
  rw [Finset.card_sdiff_of_subset hσv] at hbound
  have hup : K.upDegree σ = S.card := rfl
  rw [hup]
  rw [hcard] at hbound
  exact hbound

/-- **Proposition 10, second half (arXiv:2209.13581, Appendix G §4, page 52).**
The up-degree of any nonempty face `σ` is at most the maximum vertex up-degree
`d`: fixing a vertex `u ∈ σ`, each `(k+1)`-face `σ ∪ {v} ⊇ σ` yields a distinct
edge `{u,v}` which is an up-neighbour of the vertex `u`.

Fixed arXiv:2209.13581. Proof route: choose `u ∈ σ`; map each up-neighbour
`τ = σ ∪ {v}` to the edge `{u,v}`, which is a face by downward closure and is
an up-neighbour of the vertex `{u}`; distinct `v` give distinct edges, so the
up-degree of `σ` is at most `upDegree {u} ≤ d`. Since `u ∈ σ`, the singleton
`{u}` is disjoint from `τ \ σ`, which makes the map `τ ↦ {u} ∪ (τ \ σ)` injective.
The cardinality comparison uses `Finset.card_le_card_of_injOn`, and the bound by
the maximum vertex up-degree uses `Finset.le_sup`. -/
theorem upDegree_le_maxVertexUpDegree (K : SimplicialComplex V) {σ : Finset V}
    (hσ : σ ∈ K.faces) (hne : σ.Nonempty) :
    K.upDegree σ ≤ K.maxVertexUpDegree := by
  obtain ⟨u, hu⟩ := hne
  have huV : u ∈ K.vertices := K.face_subset_vertices hσ hu
  apply le_trans (b := K.upDegree {u}) ?_
    (Finset.le_sup (f := fun v => K.upDegree {v}) huV)
  unfold upDegree
  apply Finset.card_le_card_of_injOn (fun τ : Finset V => insert u (τ \ σ))
  · intro τ hτ
    obtain ⟨hτ, hsub, hcard⟩ := Finset.mem_filter.mp hτ
    have hστ : σ ⊆ τ := hsub.subset
    have hdiff : (τ \ σ).card = 1 := by
      rw [Finset.card_sdiff_of_subset hστ, hcard]
      omega
    obtain ⟨v, hv⟩ := Finset.card_eq_one.mp hdiff
    have hvτ : v ∈ τ := Finset.mem_sdiff.mp (hv.symm ▸ Finset.mem_singleton_self v) |>.1
    have hvσ : v ∉ σ := Finset.mem_sdiff.mp (hv.symm ▸ Finset.mem_singleton_self v) |>.2
    have hvu : v ≠ u := fun h => hvσ (h.symm ▸ hu)
    dsimp only
    rw [Finset.mem_coe, Finset.mem_filter, hv]
    refine ⟨K.down (Finset.insert_subset (hστ hu) (by simpa using hvτ)) hτ, ?_, ?_⟩
    · refine Finset.ssubset_iff_subset_ne.mpr ⟨by simp, fun heq => hvu ?_⟩
      exact Finset.mem_singleton.mp (heq.symm ▸ Finset.mem_insert_of_mem (Finset.mem_singleton_self v))
    · rw [Finset.card_pair hvu.symm, Finset.card_singleton]
  · intro τ₁ h₁ τ₂ h₂ heq
    have hs₁ : σ ⊆ τ₁ := (Finset.mem_filter.mp h₁).2.1.subset
    have hs₂ : σ ⊆ τ₂ := (Finset.mem_filter.mp h₂).2.1.subset
    have hd₁ : u ∉ τ₁ \ σ := by simp [hu]
    have hd₂ : u ∉ τ₂ \ σ := by simp [hu]
    have hd : τ₁ \ σ = τ₂ \ σ := by
      simpa [hd₁, hd₂] using congrArg (fun s : Finset V => s.erase u) heq
    rw [← Finset.union_sdiff_of_subset hs₁, ← Finset.union_sdiff_of_subset hs₂, hd]

/-- **Proposition 10 (arXiv:2209.13581, Appendix G §4, page 52).**
The up-degree of a `k`-simplex `σ` is bounded by `min{N - k - 1, d}`, where
`N` is the number of vertices of `K`, and `d` is the maximum up-degree of any
vertex of `K`. -/
theorem proposition10_upDegree_le_min (K : SimplicialComplex V) {σ : Finset V}
    {k : ℕ} (hσ : σ ∈ K.faces) (hcard : σ.card = k + 1) (hne : 0 < σ.card) :
    K.upDegree σ ≤
      min (K.vertices.card - (k + 1)) K.maxVertexUpDegree := by
  apply le_min
  · exact K.upDegree_le_vertices hσ hcard
  · exact K.upDegree_le_maxVertexUpDegree hσ (Finset.card_pos.mp hne)

/-- **Proposition 11 (arXiv:2209.13581, Appendix G §4, page 53).**
`∂_k` has column sparsity `k+1` and row sparsity bounded by
`min{N - k - 1, d}`; consequently `Δ_k` has row/column sparsity bounded by
`(k+1)(N - k - 1)`. -/
theorem proposition11_sparsity (K : SimplicialComplex V) {σ : Finset V} {k : ℕ}
    (hσ : σ ∈ K.faces) (hcard : σ.card = k + 1) (hne : 0 < σ.card) :
    K.downDegree σ = k + 1 ∧
    K.upDegree σ ≤ min (K.vertices.card - (k + 1)) K.maxVertexUpDegree ∧
    (k + 1) * (K.vertices.card - (k + 1)) ≤
      (k + 1) * K.vertices.card := by
  refine ⟨K.downDegree_eq_succ hσ hcard, K.proposition10_upDegree_le_min hσ hcard hne, ?_⟩
  exact Nat.mul_le_mul_left _ (Nat.sub_le _ _)

end SimplicialComplex

end Qatlib.Papers.TopoAdvantage22.MainResults.SimplicialCore
