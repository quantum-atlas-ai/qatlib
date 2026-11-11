/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

/-
# Lemma 1: the positive case of the tree-detection span program

Guoming Wang, *Span-program-based quantum algorithm for tree detection*,
fixed arXiv:1309.7713v3 (5 Mar 2014).

Section 3, "Positive case", Lemma 1 and its proof (Eq. (11)):

> Suppose `G_c` contains `T` as a subgraph. Then `P` accepts `G_c`. Moreover, the
> witness size of `P` on `G_c` is `O(1)`.

The proof writes the target vector as the sum of one root vector, one leaf vector
per leaf of `T`, and one edge vector per edge of `T`, i.e. `|E_T|` terms in total;
the paper then reads off witness size `|E_T| = O(1)`. Here the same witness is
exhibited explicitly and its size is shown to be exactly the number of non-root
nodes of `T`, so the `O(1)` bound is unconditional in `n = |V_G|`.
-/

import Qatlib.Papers.SpanProgTree13.MainResults.TreeDetectionProgram

/-!
# PositiveWitness

Paper-specific positive witness constructions and proofs for SpanProgTree13.
-/

set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false
noncomputable section

open scoped BigOperators
open Finset
open Classical

namespace Qatlib.Papers.SpanProgTree13.MainResults

variable {VT VG : Type*} [Fintype VT] [Fintype VG] [DecidableEq VT] [DecidableEq VG]

/-- The witness of Eq. (11): coefficient `1` on the root vector of `ι r`, on the
leaf vector of every leaf `f` at `ι f`, and on the edge vector of every tree edge
`(ι a, ι b)`; coefficient `0` everywhere else. -/
def posWitness (t : RootedTree VT) (emb : VT → VG) : Idx VG VT → ℝ
  | Sum.inl u => if u = emb t.root then 1 else 0
  | Sum.inr (Sum.inl (f, u)) => if t.IsLeaf f ∧ u = emb f then 1 else 0
  | Sum.inr (Sum.inr (u, v)) =>
      if ∃ b, b ≠ t.root ∧ emb (t.parB b) = u ∧ emb b = v then 1 else 0

omit [Fintype VG] in
/-- The witness takes only the values `0` and `1`. -/
theorem posWitness_zero_or_one (t : RootedTree VT) (emb : VT → VG) (j : Idx VG VT) :
    posWitness t emb j = 0 ∨ posWitness t emb j = 1 := by
  rcases j with u | (⟨f, u⟩ | ⟨u, v⟩)
  · by_cases hu : u = emb t.root <;> simp [posWitness, hu]
  · by_cases hf : t.IsLeaf f ∧ u = emb f <;> simp [posWitness, hf]
  · by_cases hex : ∃ b, b ≠ t.root ∧ emb (t.parB b) = u ∧ emb b = v <;> simp [posWitness, hex]

omit [Fintype VG] in
/-- The witness is supported on the available input vectors. -/
theorem posWitness_support (t : RootedTree VT) {G : VG → VG → Prop} {c : VG → VT}
    {emb : VT → VG} (h : CorrectEmbedding t G c emb) {j : Idx VG VT}
    (hj : j ∉ avail t c G) : posWitness t emb j = 0 := by
  rcases j with u | (⟨f, u⟩ | ⟨u, v⟩)
  · by_cases hu : u = emb t.root
    · exfalso
      apply hj
      show c u = t.root
      rw [hu, h.color]
    · simp [posWitness, hu]
  · by_cases hf : t.IsLeaf f ∧ u = emb f
    · exfalso
      apply hj
      exact ⟨hf.1, by rw [hf.2, h.color]⟩
    · simp [posWitness, hf]
  · by_cases hex : ∃ b, b ≠ t.root ∧ emb (t.parB b) = u ∧ emb b = v
    · exfalso
      obtain ⟨b, hb, rfl, rfl⟩ := hex
      apply hj
      refine ⟨?_, ?_⟩
      · exact h.edges (t.parB b) b (t.par_parB hb)
      · show t.par (c (emb b)) = some (c (emb (t.parB b)))
        rw [h.color, h.color]
        exact t.par_parB hb
    · simp [posWitness, hex]

omit [DecidableEq VT] in
/-- `parB` along the ancestor chain is the next ancestor. -/
theorem parB_anc {t : RootedTree VT} {f : VT} {k : ℕ} (h : k < t.depth f) :
    t.parB (t.anc f k) = t.anc f (k + 1) := by
  rw [RootedTree.parB, t.par_anc h]
  rfl

/-- The `b`-indexed edge vector of the positive witness, with the leaf set
`S_{a,b}` of Eq. (10) collapsed to `V^b_{T,l}`. -/
theorem leafInter_child_eq {t : RootedTree VT} {a b : VT} (h : t.child a b) :
    leafInter t a b = vleaf t b := leafInter_child h

omit [Fintype VG] in
/-- Pointwise form of the edge sum: at the coordinate `(u₀,f₀)` the `b`-th edge
vector contributes the ancestor-chain difference, and only leaves survive. -/
theorem sum_edge_apply (t : RootedTree VT) (emb : VT → VG) (u₀ : VG ⊕ Bool) (f₀ : VT) :
    (∑ b ∈ Finset.univ.filter (fun b => b ≠ t.root),
        (vec (VT := VT) (gPt (emb (t.parB b))) (vleaf t b)
          - vec (VT := VT) (gPt (emb b)) (vleaf t b))) (u₀, f₀)
      = if t.IsLeaf f₀ then
          ((if u₀ = gPt (emb t.root) then (1 : ℝ) else 0)
            - (if u₀ = gPt (emb f₀) then (1 : ℝ) else 0))
        else 0 := by
  have hterm : ∀ b ∈ Finset.univ.filter (fun b => b ≠ t.root),
      (vec (VT := VT) (gPt (emb (t.parB b))) (vleaf t b)
        - vec (VT := VT) (gPt (emb b)) (vleaf t b)) (u₀, f₀)
      = if t.IsLeaf f₀ ∧ t.Subtree b f₀ then
          ((if u₀ = gPt (emb (t.parB b)) then (1 : ℝ) else 0)
            - (if u₀ = gPt (emb b) then (1 : ℝ) else 0))
        else 0 := by
    intro b _
    by_cases hb : t.IsLeaf f₀ ∧ t.Subtree b f₀
    · have hmem : f₀ ∈ vleaf t b := mem_vleaf.mpr hb
      rw [Pi.sub_apply, vec, vec, if_pos hb]
      simp only [hmem]
      by_cases hA : u₀ = gPt (emb (t.parB b)) <;> by_cases hB : u₀ = gPt (emb b) <;>
        simp [hA, hB]
    · have hmem : f₀ ∉ vleaf t b := fun hc => hb (mem_vleaf.mp hc)
      rw [Pi.sub_apply, vec, vec, if_neg hb]
      simp [hmem]
  rw [Finset.sum_apply]
  rw [Finset.sum_congr rfl hterm]
  rw [← Finset.sum_filter]
  rw [Finset.filter_filter]
  by_cases hL : t.IsLeaf f₀
  · rw [if_pos hL]
    have hfilter : Finset.univ.filter (fun b => b ≠ t.root ∧ (t.IsLeaf f₀ ∧ t.Subtree b f₀))
        = Finset.univ.filter (fun b => b ≠ t.root ∧ t.Subtree b f₀) := by
      apply Finset.filter_congr
      intro b _
      simp [hL]
    have hshift : ∀ k ∈ Finset.range (t.depth f₀),
        ((if u₀ = gPt (emb (t.parB (t.anc f₀ k))) then (1 : ℝ) else 0)
          - (if u₀ = gPt (emb (t.anc f₀ k)) then (1 : ℝ) else 0))
        = ((fun k => (if u₀ = gPt (emb (t.anc f₀ k)) then (1 : ℝ) else 0)) (k + 1)
            - (fun k => (if u₀ = gPt (emb (t.anc f₀ k)) then (1 : ℝ) else 0)) k) := by
      intro k hk
      rw [parB_anc (Finset.mem_range.mp hk)]
    rw [hfilter,
      t.sum_subtree f₀ (fun b => (if u₀ = gPt (emb (t.parB b)) then (1 : ℝ) else 0)
        - (if u₀ = gPt (emb b) then (1 : ℝ) else 0))]
    rw [Finset.sum_congr rfl hshift]
    rw [t.sum_chain f₀ (fun b => if u₀ = gPt (emb b) then (1 : ℝ) else 0)]
  · rw [if_neg hL]
    have hempty : Finset.univ.filter (fun b => b ≠ t.root ∧ (t.IsLeaf f₀ ∧ t.Subtree b f₀)) = ∅ := by
      rw [Finset.filter_eq_empty_iff]
      intro b _ h
      exact hL h.2.1
    rw [hempty]
    simp

/-- The number of edges `|E_T|` of `T`: the witness size read off in the proof of
Lemma 1, `|E_T| = O(1)` because `T` is fixed. -/
def numEdges (t : RootedTree VT) : ℕ :=
  (Finset.univ.filter (fun b => b ≠ t.root)).card

/-- The edge vector contributed by the tree edge above `b`. -/
def edgeVec (t : RootedTree VT) (emb : VT → VG) (b : VT) : Coord VG VT → ℝ :=
  vec (gPt (emb (t.parB b))) (vleaf t b) - vec (gPt (emb b)) (vleaf t b)

/-- The root part of Eq. (11). -/
theorem sum_root (t : RootedTree VT) (c : VG → VT) (emb : VT → VG) :
    (∑ u : VG, posWitness t emb (Sum.inl u) • (program t c).inp (Sum.inl u))
      = vec sPt (leafSet t) - vec (gPt (emb t.root)) (leafSet t) := by
  rw [Finset.sum_eq_single (emb t.root)]
  · simp [posWitness, program]
  · intro b _ hb
    simp [posWitness, hb]
  · intro h
    exact absurd (Finset.mem_univ _) h

/-- The leaf part of Eq. (11). -/
theorem sum_leaf (t : RootedTree VT) (c : VG → VT) (emb : VT → VG) :
    (∑ p : VT × VG,
        posWitness t emb (Sum.inr (Sum.inl p)) • (program t c).inp (Sum.inr (Sum.inl p)))
      = ∑ f ∈ leafSet t, (basis (gPt (emb f)) f - basis tPt f) := by
  rw [Fintype.sum_prod_type]
  have hinner : ∀ f : VT,
      (∑ u : VG,
          posWitness t emb (Sum.inr (Sum.inl (f, u))) •
            (program t c).inp (Sum.inr (Sum.inl (f, u))))
        = if t.IsLeaf f then (basis (gPt (emb f)) f - basis tPt f) else 0 := by
    intro f
    rw [Finset.sum_eq_single (emb f)]
    · by_cases hL : t.IsLeaf f <;> simp [posWitness, program, hL]
    · intro b _ hb
      simp [posWitness, hb]
    · intro h
      exact absurd (Finset.mem_univ _) h
  rw [Finset.sum_congr rfl (fun f _ => hinner f)]
  rw [← Finset.sum_filter]
  rfl

omit [Fintype VG] [DecidableEq VT] in
/-- The leaf part of Eq. (11) at a single coordinate. -/
theorem sum_leaf_apply (t : RootedTree VT) (emb : VT → VG) (u₀ : VG ⊕ Bool) (f₀ : VT) :
    ((∑ f ∈ leafSet t, (basis (VT := VT) (gPt (emb f)) f - basis tPt f))
      : Coord VG VT → ℝ) (u₀, f₀)
      = if t.IsLeaf f₀ then
          ((if u₀ = gPt (emb f₀) then (1 : ℝ) else 0)
            - (if u₀ = tPt then (1 : ℝ) else 0))
        else 0 := by
  rw [Finset.sum_apply]
  by_cases hL : t.IsLeaf f₀
  · rw [if_pos hL]
    have hmem : f₀ ∈ leafSet t := mem_leafSet.mpr hL
    rw [Finset.sum_eq_single f₀]
    · rw [Pi.sub_apply, basis, basis]
      simp
    · intro b _ hbf
      have hne1 : ¬ ((u₀, f₀) = (gPt (emb b), b)) := by
        rintro h
        exact hbf (Prod.ext_iff.mp h).2.symm
      have hne2 : ¬ ((u₀, f₀) = (tPt, b)) := by
        rintro h
        exact hbf (Prod.ext_iff.mp h).2.symm
      rw [Pi.sub_apply, basis, basis, if_neg hne1, if_neg hne2]
      simp
    · intro hnot
      exact absurd hmem hnot
  · rw [if_neg hL]
    apply Finset.sum_eq_zero
    intro b hb
    rw [Pi.sub_apply, basis, basis]
    have hne1 : ¬ ((u₀, f₀) = (gPt (emb b), b)) := by
      rintro h
      have hfb : f₀ = b := (Prod.ext_iff.mp h).2
      exact hL (by rw [hfb]; exact mem_leafSet.mp hb)
    have hne2 : ¬ ((u₀, f₀) = (tPt, b)) := by
      rintro h
      have hfb : f₀ = b := (Prod.ext_iff.mp h).2
      exact hL (by rw [hfb]; exact mem_leafSet.mp hb)
    rw [if_neg hne1, if_neg hne2]
    simp

/-- The edge part of Eq. (11). -/
theorem sum_edge (t : RootedTree VT) (c : VG → VT) (emb : VT → VG)
    {G : VG → VG → Prop} (h : CorrectEmbedding t G c emb) :
    (∑ p : VG × VG,
        posWitness t emb (Sum.inr (Sum.inr p)) • (program t c).inp (Sum.inr (Sum.inr p)))
      = ∑ b ∈ Finset.univ.filter (fun b => b ≠ t.root), edgeVec t emb b := by
  have hfun : ∀ p : VG × VG,
      posWitness t emb (Sum.inr (Sum.inr p)) • (program t c).inp (Sum.inr (Sum.inr p))
        = (if ∃ b, b ≠ t.root ∧ emb (t.parB b) = p.1 ∧ emb b = p.2 then (1 : ℝ) else 0)
          • (vec (gPt p.1) (leafInter t (c p.1) (c p.2))
              - vec (gPt p.2) (leafInter t (c p.1) (c p.2))) := by
    intro p
    rfl
  rw [Finset.sum_congr rfl (fun p _ => hfun p)]
  let φ : VT → Idx VG VT := fun b => edgeIdx (emb (t.parB b)) (emb b)
  let S : Finset VT := Finset.univ.filter (fun b => b ≠ t.root)
  have hinj : Set.InjOn φ ↑S := by
    intro a _ b _ hab
    have h2 : emb a = emb b := by
      have := congrArg (fun j => match j with
        | Sum.inl _ => emb a
        | Sum.inr (Sum.inl _) => emb a
        | Sum.inr (Sum.inr p) => p.2) hab
      simpa [φ, edgeIdx] using this
    exact h.1 h2
  have hzero : ∀ p ∈ (Finset.univ : Finset (VG × VG)),
      p ∉ S.image (fun b => (emb (t.parB b), emb b)) →
      (if ∃ b, b ≠ t.root ∧ emb (t.parB b) = p.1 ∧ emb b = p.2 then (1 : ℝ) else 0)
        • (vec (gPt p.1) (leafInter t (c p.1) (c p.2))
            - vec (gPt p.2) (leafInter t (c p.1) (c p.2))) = 0 := by
    intro p _ hp
    have hno : ¬ ∃ b, b ≠ t.root ∧ emb (t.parB b) = p.1 ∧ emb b = p.2 := by
      rintro ⟨b, hb, h1, h2⟩
      exact hp (Finset.mem_image.mpr ⟨b, by simp [S, hb], by simp [h1, h2]⟩)
    rw [if_neg hno, zero_smul]
  rw [← Finset.sum_subset (Finset.subset_univ _) hzero]
  rw [Finset.sum_image]
  · refine Finset.sum_congr rfl ?_
    intro b hb
    rw [Finset.mem_filter] at hb
    obtain ⟨-, hbne⟩ := hb
    have hchild : t.child (t.parB b) b := t.par_parB hbne
    have hci : leafInter t (c (emb (t.parB b))) (c (emb b)) = vleaf t b := by
      rw [h.color, h.color]
      exact leafInter_child hchild
    rw [hci]
    rw [if_pos ⟨b, hbne, rfl, rfl⟩, one_smul]
    rw [edgeVec]
  · intro a _ b _ hab
    have h2 : emb a = emb b := by
      have := congrArg Prod.snd hab
      simpa using this
    exact h.1 h2
/-- Eqs. (11) and (5)-(10): the witness of Eq. (11) reconstructs the target vector
as the sum of one root vector, one leaf vector per leaf, and one edge vector per
edge of `T`. -/
theorem sum_inp (t : RootedTree VT) (c : VG → VT) (emb : VT → VG)
    {G : VG → VG → Prop} (h : CorrectEmbedding t G c emb) :
    (∑ j, posWitness t emb j • (program t c).inp j)
      = (vec sPt (leafSet t) - vec (gPt (emb t.root)) (leafSet t))
        + ((∑ f ∈ leafSet t, (basis (gPt (emb f)) f - basis tPt f))
            + (∑ b ∈ Finset.univ.filter (fun b => b ≠ t.root), edgeVec t emb b)) := by
  rw [Fintype.sum_sum_type]
  rw [Fintype.sum_sum_type]
  rw [sum_root t c emb, sum_leaf t c emb, sum_edge t c emb h]

/-- Lemma 1 of arXiv:1309.7713v3: if `G_c` contains `T` as a subgraph then `P`
accepts `G_c`, with a positive witness of size exactly `|E_T|`. -/
theorem lemma1_positive (t : RootedTree VT) {G : VG → VG → Prop} {c : VG → VT}
    {emb : VT → VG} (h : CorrectEmbedding t G c emb) :
    (program t c).HasPositiveWitnessOfSizeAtMost (avail t c G) (numEdges t : ℝ) := by
  refine ⟨posWitness t emb, ⟨fun j hj => posWitness_support t h hj, ?_⟩, ?_⟩
  · rw [sum_inp t c emb h]
    funext p
    obtain ⟨u₀, f₀⟩ := p
    rw [Pi.add_apply, Pi.add_apply, Pi.sub_apply, sum_leaf_apply t emb u₀ f₀]
    have hedge : (∑ b ∈ Finset.univ.filter (fun b => b ≠ t.root), edgeVec t emb b) (u₀, f₀)
        = if t.IsLeaf f₀ then
            ((if u₀ = gPt (emb t.root) then (1 : ℝ) else 0)
              - (if u₀ = gPt (emb f₀) then (1 : ℝ) else 0))
          else 0 := by
      have := sum_edge_apply t emb u₀ f₀
      simpa only [edgeVec] using this
    rw [hedge]
    simp only [program, Pi.sub_apply, vec]
    by_cases hL : t.IsLeaf f₀
    · simp [mem_leafSet, hL]
    · simp [mem_leafSet, hL]
  · rw [SpanProgram.positiveSize]
    let S : Finset VT := Finset.univ.filter (fun b => b ≠ t.root)
    let φ : VT → Idx VG VT := fun b => edgeIdx (emb (t.parB b)) (emb b)
    have hinj : Set.InjOn φ ↑S := by
      intro a _ b _ hab
      have h2 : emb a = emb b := by
        have := congrArg (fun j => match j with
          | Sum.inl _ => emb a
          | Sum.inr (Sum.inl _) => emb a
          | Sum.inr (Sum.inr p) => p.2) hab
        simpa [φ, edgeIdx] using this
      exact h.1 h2
    have hsub : S.image φ ⊆ Finset.univ.filter
        (fun j => j ∈ avail t c G ∧ j ∉ freeIdx) := by
      intro j hj
      obtain ⟨b, hb, rfl⟩ := Finset.mem_image.mp hj
      rw [Finset.mem_filter] at hb ⊢
      obtain ⟨-, hbne⟩ := hb
      have hchild : t.child (t.parB b) b := t.par_parB hbne
      refine ⟨Finset.mem_univ _, ?_, ?_⟩
      · refine ⟨h.edges (t.parB b) b hchild, ?_⟩
        show t.par (c (emb b)) = some (c (emb (t.parB b)))
        rw [h.color, h.color]
        exact t.par_parB hbne
      · simp [φ, edgeIdx, freeIdx]
    have hzero : ∀ j ∈ Finset.univ.filter (fun j => j ∈ avail t c G ∧ j ∉ freeIdx),
        j ∉ S.image φ → (posWitness t emb j) ^ 2 = 0 := by
      intro j hj hnot
      rw [Finset.mem_filter] at hj
      obtain ⟨-, -, hnf⟩ := hj
      rcases posWitness_zero_or_one t emb j with h0 | h1
      · rw [h0]; ring
      · exfalso
        rcases j with u | (⟨f, u⟩ | ⟨u, v⟩)
        · exact hnf (by simp [freeIdx])
        · exact hnf (by simp [freeIdx])
        · by_cases hex : ∃ b, b ≠ t.root ∧ emb (t.parB b) = u ∧ emb b = v
          · obtain ⟨b, hb, h1', h2'⟩ := hex
            exact hnot (Finset.mem_image.mpr ⟨b, by simp [S, hb], by simp [φ, edgeIdx, h1', h2']⟩)
          · simp [posWitness, hex] at h1
    have hfree : (program t c).freeIdx = freeIdx := rfl
    rw [hfree]
    rw [← Finset.sum_subset hsub hzero]
    have hw1 : ∀ b ∈ S, posWitness t emb (φ b) = 1 := by
      intro b hb
      rw [Finset.mem_filter] at hb
      obtain ⟨-, hbne⟩ := hb
      simp only [φ, edgeIdx, posWitness]
      rw [if_pos ⟨b, hbne, rfl, rfl⟩]
    have hconst : ∀ x ∈ S.image φ, (posWitness t emb x) ^ 2 = 1 := by
      intro x hx
      obtain ⟨b, hb, rfl⟩ := Finset.mem_image.mp hx
      rw [hw1 b hb]
      ring
    rw [Finset.sum_congr rfl hconst, Finset.sum_const]
    simp [Finset.card_image_of_injOn hinj, numEdges, S]

/-- Lemma 1, first half: if `G_c` contains `T` as a subgraph then `P` accepts `G_c`
(Eq. (1) applied to the witness of Eq. (11)). -/
theorem lemma1_accepts (t : RootedTree VT) {G : VG → VG → Prop} {c : VG → VT}
    {emb : VT → VG} (h : CorrectEmbedding t G c emb) :
    (program t c).accepts (avail t c G) :=
  SpanProgram.accepts_of_positiveWitness (lemma1_positive t h)

end Qatlib.Papers.SpanProgTree13.MainResults
