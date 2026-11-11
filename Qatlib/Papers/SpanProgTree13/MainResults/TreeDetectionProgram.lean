/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

/-
# The tree-detection span program of arXiv:1309.7713v3, Section 3

Guoming Wang, *Span-program-based quantum algorithm for tree detection*,
fixed arXiv:1309.7713v3 (5 Mar 2014).

Section 3, Eqs. (5)-(10): the ambient space spanned by `|u⟩ ⊗ |f⟩` with
`u ∈ {s,t} ∪ V_G` and `f ∈ V_{T,l}`; the target vector `|τ⟩` of Eq. (6); the free
root and leaf input vectors of Eqs. (7)-(8); and the edge input vectors of
Eq. (9) with the compact description of Eq. (10).

Eq. (9) introduces the edge input vectors only for correctly coloured endpoint
pairs, i.e. for `u ∈ c^{-1}(x)`, `v ∈ c^{-1}(y)` with `y` a child of `x`. The
index family below instead ranges over all vertex pairs with the colour condition
moved into the availability predicate `avail`. The available sets, the accepted
inputs, and the positive witness sizes are unchanged by this enlargement: an
input vector whose endpoints are not in admissible blocks is simply never
available.
-/

import Qatlib.Papers.SpanProgTree13.MainResults.SpanProgramCore
import Qatlib.Papers.SpanProgTree13.MainResults.RootedTreeChain

/-!
# TreeDetectionProgram

Paper-specific tree detection program constructions and proofs for SpanProgTree13.
-/

set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false
noncomputable section

open scoped BigOperators
open Finset
open Classical

namespace Qatlib.Papers.SpanProgTree13.MainResults

variable {VT VG : Type*} [Fintype VT] [Fintype VG]

/-- The leaf set `V_{T,l}` of `T` (Section 2.1). -/
def leafSet (t : RootedTree VT) : Finset VT := Finset.univ.filter t.IsLeaf

/-- The leaf set `V^a_{T,l}` of the subtree `T^a` (Section 2.1). -/
def vleaf (t : RootedTree VT) (a : VT) : Finset VT :=
  Finset.univ.filter (fun f => t.IsLeaf f ∧ t.Subtree a f)

/-- The leaf set is the set of `T`-vertices without children. -/
theorem mem_leafSet {t : RootedTree VT} {f : VT} :
    f ∈ leafSet t ↔ t.IsLeaf f := by
  simp [leafSet]

/-- `V^a_{T,l}` consists of the leaves lying below `a`. -/
theorem mem_vleaf {t : RootedTree VT} {a f : VT} :
    f ∈ vleaf t a ↔ t.IsLeaf f ∧ t.Subtree a f := by
  simp [vleaf]

/-- The set `S_{x,y} = V^x_{T,l} ∩ V^y_{T,l}` of Eq. (5) and Eq. (10). -/
def leafInter [DecidableEq VT] (t : RootedTree VT) (x y : VT) : Finset VT :=
  vleaf t x ∩ vleaf t y

/-- A `T`-node `b` strictly below the root has its leaf set inside the leaf set
of its parent block. -/
theorem vleaf_subset_parent {t : RootedTree VT} {b : VT} (hb : b ≠ t.root) :
    vleaf t b ⊆ vleaf t (t.parB b) := by
  intro f hf
  rw [mem_vleaf] at hf ⊢
  refine ⟨hf.1, ?_⟩
  obtain ⟨k, hk⟩ := hf.2
  refine ⟨k + 1, ?_⟩
  rw [t.ancOpt_succ, hk]
  simp only [Option.bind_some]
  exact t.par_parB hb

/-- Eq. (10): the edge input vector between blocks `x` and `y` is supported on
`S_{x,y}`. For a parent block `a` and a child block `b` this is the leaf set of
`T^b`. -/
theorem leafInter_child [DecidableEq VT] {t : RootedTree VT} {a b : VT}
    (h : t.child a b) :
    leafInter t a b = vleaf t b := by
  have hb : b ≠ t.root := by
    intro hroot
    have h' : t.par b = some a := h
    rw [hroot, t.par_root] at h'
    simp at h'
  have hparB : t.parB b = a := by
    rw [RootedTree.parB, h]; rfl
  rw [leafInter, ← hparB]
  exact Finset.inter_eq_right.mpr (vleaf_subset_parent hb)

/-- The ambient coordinate set `{s,t} ∪ V_G` of Eq. (5), paired with the leaf
label `f ∈ V_{T,l}`. Non-leaf labels never occur in the construction, but keeping
the full vertex type `VT` as label type costs nothing and avoids subtype coercions. -/
abbrev Coord (VG VT : Type*) := (VG ⊕ Bool) × VT

/-- The special source vertex `s`. -/
def sPt {VG : Type*} : VG ⊕ Bool := Sum.inr true

/-- The special sink vertex `t`. -/
def tPt {VG : Type*} : VG ⊕ Bool := Sum.inr false

/-- A graph vertex, viewed as a coordinate label. -/
def gPt {VG : Type*} (u : VG) : VG ⊕ Bool := Sum.inl u

/-- The vector `|u⟩ ⊗ (∑_{f ∈ S} |f⟩)` of Eq. (10). -/
def vec {VG : Type*} (u : VG ⊕ Bool) (S : Finset VT) : Coord VG VT → ℝ :=
  fun p => if p.1 = u ∧ p.2 ∈ S then 1 else 0

/-- The basis vector `|u⟩ ⊗ |f⟩`. -/
def basis {VG : Type*} (u : VG ⊕ Bool) (f : VT) : Coord VG VT → ℝ :=
  fun p => if p = (u, f) then 1 else 0

omit [Fintype VT] [Fintype VG] in
/-- The basis vector `|u⟩ ⊗ |f⟩` is the singleton block vector. -/
theorem basis_eq_vec {u : VG ⊕ Bool} {f : VT} (p : Coord VG VT) :
    basis u f p = vec u {f} p := by
  by_cases hp : p = (u, f)
  · rw [basis, if_pos hp, vec, if_pos]
    exact ⟨by rw [hp], by rw [hp]; simp⟩
  · rw [basis, if_neg hp, vec, if_neg]
    rintro ⟨h1, h2⟩
    exact hp (Prod.ext h1 (Finset.mem_singleton.mp h2))

/-- The input-vector index set: root vectors, leaf vectors, and edge vectors. -/
abbrev Idx (VG VT : Type*) := VG ⊕ (VT × VG) ⊕ (VG × VG)

/-- The free root input vector `|(s,u)⟩` of Eq. (7), indexed by `u ∈ c^{-1}(r)`. -/
def rootIdx {VG VT : Type*} (u : VG) : Idx VG VT := Sum.inl u

/-- The free leaf input vector `|(u,t)⟩` of Eq. (8), indexed by `f ∈ V_{T,l}` and
`u ∈ c^{-1}(f)`. -/
def leafIdx {VG VT : Type*} (f : VT) (u : VG) : Idx VG VT := Sum.inr (Sum.inl (f, u))

/-- The edge input vector `|(u,v)⟩` of Eq. (9). -/
def edgeIdx {VG VT : Type*} (u v : VG) : Idx VG VT := Sum.inr (Sum.inr (u, v))

variable (t : RootedTree VT)

/-- The available input vectors of `P` on the coloured graph `G_c`: the free root
and leaf vectors are available on the blocks they are attached to, and an edge
vector is available exactly when the edge is present in `G_c`, i.e. when the
underlying graph edge exists and the two endpoints sit in adjacent blocks. -/
def avail (c : VG → VT) (G : VG → VG → Prop) : Set (Idx VG VT) :=
  { j | match j with
      | Sum.inl u => c u = t.root
      | Sum.inr (Sum.inl (f, u)) => t.IsLeaf f ∧ c u = f
      | Sum.inr (Sum.inr (u, v)) => G u v ∧ t.child (c u) (c v) }

/-- The free input vectors `I_free` of Definition 1: the root and leaf vectors. -/
def freeIdx : Set (Idx VG VT) :=
  { j | match j with
      | Sum.inl _ => True
      | Sum.inr (Sum.inl _) => True
      | Sum.inr (Sum.inr _) => False }

/-- Eqs. (5)-(10): the span program `P` for the subgraph/not-a-minor problem for `T`. -/
def program [DecidableEq VT] (c : VG → VT) : SpanProgram (Coord VG VT) (Idx VG VT) where
  target := vec sPt (leafSet t) - vec tPt (leafSet t)
  inp := fun j =>
    match j with
    | Sum.inl u => vec sPt (leafSet t) - vec (gPt u) (leafSet t)
    | Sum.inr (Sum.inl (f, u)) => basis (gPt u) f - basis tPt f
    | Sum.inr (Sum.inr (u, v)) =>
        vec (gPt u) (leafInter t (c u) (c v)) - vec (gPt v) (leafInter t (c u) (c v))
  freeIdx := freeIdx

/-- The colouring `c` together with a correctly coloured copy of `T`: an injection
`ι : V_T → V_G` with `c ∘ ι = id` whose tree edges are graph edges. This is the
"`G_c` contains a correctly coloured `T`-subgraph" hypothesis of Lemma 1. -/
structure CorrectEmbedding (G : VG → VG → Prop) (c : VG → VT) (emb : VT → VG) : Prop where
  /-- Distinct tree nodes are embedded at distinct graph vertices. -/
  injective : Function.Injective emb
  /-- The embedding respects the colouring: `c (ι a) = a`. -/
  color : ∀ a, c (emb a) = a
  /-- Every edge of `T` is present in `G_c`. -/
  edges : ∀ a b, t.child a b → G (emb a) (emb b)

end Qatlib.Papers.SpanProgTree13.MainResults
