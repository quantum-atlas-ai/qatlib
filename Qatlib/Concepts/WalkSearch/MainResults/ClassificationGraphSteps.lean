/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.WalkSearch.Primitives.DegreeConcentration
import Qatlib.Concepts.WalkSearch.Primitives.RemovalTriangleFact5

/-!
# Graph steps in pair classification

`presentGraph` restricts a graph to a symmetric set of candidate pairs, and `highEadd` collects
the pairs removed by a high degree step. The fiber count `highProgressFibers_card` yields a
lower bound on the progress of that step when all remaining pairs meet the common neighbor
threshold. For background on quantum search and amplitude amplification, see [BrassardEtAl2002].

## Main statements

* `pairSetSymmetric`: The finite set of ordered pairs is closed under swapping its coordinates.
* `highEadd_progress`: If every pair in the symmetric set `S` has at least `τ` common neighbors
  in `S`, the high degree step removes at least `τ` times the degree of `v` in `presentGraph`
  pairs.

## References

* [Brassard et al., 2002][BrassardEtAl2002]
-/

set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

open Qatlib.Concepts.WalkSearch.Primitives
set_option autoImplicit false
set_option maxHeartbeats 1200000
noncomputable section
namespace Qatlib.Concepts.WalkSearch.MainResults
open scoped Classical BigOperators
variable {n : ℕ}

/-- The finite set of ordered pairs is closed under swapping its coordinates. -/
def pairSetSymmetric (S : Finset (Fin n×Fin n)) : Prop := ∀ a b,(a,b)∈S→(b,a)∈S

/-- For a symmetric pair set, membership in `nbrOf S a` is equivalent to membership of the
ordered pair `(a, b)` in `S`. -/
theorem mem_symmetric_nbr_iff (S : Finset (Fin n×Fin n)) (hS : pairSetSymmetric S) (a b : Fin n) :
    b∈nbrOf S a ↔ (a,b)∈S := by
  rw [mem_nbrOf_iff]
  exact ⟨fun h=>h.elim id (hS b a),Or.inl⟩

/-- Restrict `G` to the intersection of its edges with the symmetric candidate pair set `S`. -/
def presentGraph (G : UGraph n) (S : Finset (Fin n×Fin n)) (hS : pairSetSymmetric S) : UGraph n where
  edges := G.edges∩S
  symm := by
    intro a b h
    rw [Finset.mem_inter] at h ⊢
    exact ⟨G.symm a b h.1,hS a b h.2⟩
  loopless := by
    intro a h
    exact G.loopless a (Finset.mem_inter.mp h).1

/-- The neighbors in `presentGraph` are the intersection of the graph neighbors and the
candidate pair neighbors. -/
theorem presentGraph_neighbors (G : UGraph n) (S : Finset (Fin n×Fin n)) (hS : pairSetSymmetric S) (v : Fin n) :
    nbrOf (presentGraph G S hS).edges v=nbrOf G.edges v∩nbrOf S v := by
  ext x
  rw [mem_graph_nbr_iff]
  change ((v,x)∈G.edges∩S) ↔ x∈nbrOf G.edges v∩nbrOf S v
  simp only [Finset.mem_inter,mem_graph_nbr_iff,mem_symmetric_nbr_iff S hS]

/-- Select pairs of `S` incident to `v` or crossing between the graph neighborhood of `v` and
its neighborhood in `S`, in either orientation. -/
def highEadd (G : UGraph n) (S : Finset (Fin n×Fin n)) (v : Fin n) : Finset (Fin n×Fin n) :=
  S.filter fun p=>p.1=v ∨ p.2=v ∨
    (p.1∈nbrOf G.edges v ∧ p.2∈nbrOf S v) ∨ (p.2∈nbrOf G.edges v ∧ p.1∈nbrOf S v)

/-- The pair set selected by a high degree step is symmetric whenever `S` is symmetric. -/
theorem highEadd_symmetric (G : UGraph n) (S : Finset (Fin n×Fin n)) (hS : pairSetSymmetric S) (v : Fin n) :
    pairSetSymmetric (highEadd G S v) := by
  intro a b h
  simp only [highEadd,Finset.mem_filter] at h ⊢
  refine ⟨hS a b h.1,?_⟩
  tauto

/-- The difference of two symmetric finite pair sets is symmetric. -/
theorem symmetric_sdiff {S T : Finset (Fin n×Fin n)} (hS : pairSetSymmetric S) (hT : pairSetSymmetric T) :
    pairSetSymmetric (S\T) := by
  intro a b h
  simp only [Finset.mem_sdiff] at h ⊢
  exact ⟨hS a b h.1,fun hb=>h.2 (hT b a hb)⟩

/-- Collect ordered pairs `(x, y)` with `x` in `P` and `y` a common neighbor of `v` and `x` in
`S`. -/
def highProgressFibers (S : Finset (Fin n×Fin n)) (v : Fin n) (P : Finset (Fin n)) : Finset (Fin n×Fin n) :=
  P.biUnion fun x=>(nbrOf S v∩nbrOf S x).image (fun y=>(x,y))

/-- The cardinality of `highProgressFibers S v P` is the sum of the common neighbor counts `tOf
S v x` over `x` in `P`. -/
theorem highProgressFibers_card (S : Finset (Fin n×Fin n)) (v : Fin n) (P : Finset (Fin n)) :
    (highProgressFibers S v P).card=∑ x∈P,tOf S v x := by
  unfold highProgressFibers
  rw [Finset.card_biUnion]
  · apply Finset.sum_congr rfl
    intro x _
    exact Finset.card_image_of_injOn (fun a _ b _ h=>(Prod.mk.inj h).2)
  · intro x _ y _ hxy
    apply Finset.disjoint_left.mpr
    intro e he hf
    obtain ⟨a,_,ha⟩:=Finset.mem_image.mp he
    obtain ⟨b,_,hb⟩:=Finset.mem_image.mp hf
    exact hxy (congrArg Prod.fst (ha.trans hb.symm))

/-- If every pair in the symmetric set `S` has at least `τ` common neighbors in `S`, the high
degree step removes at least `τ` times the degree of `v` in `presentGraph` pairs. -/
theorem highEadd_progress (G : UGraph n) (S : Finset (Fin n×Fin n)) (hS : pairSetSymmetric S)
    (v : Fin n) (τ : ℕ) (hthin : ∀ a b,(a,b)∈S→τ≤tOf S a b) :
    degOf (presentGraph G S hS).edges v*τ≤(highEadd G S v).card := by
  let P := nbrOf G.edges v∩nbrOf S v
  have hsub : highProgressFibers S v P⊆highEadd G S v := by
    intro e he
    obtain ⟨x,hx,he⟩:=Finset.mem_biUnion.mp he
    obtain ⟨y,hy,rfl⟩:=Finset.mem_image.mp he
    have hxG : x∈nbrOf G.edges v := (Finset.mem_inter.mp hx).1
    have hyS : y∈nbrOf S v := (Finset.mem_inter.mp hy).1
    have heS : (x,y)∈S := (mem_symmetric_nbr_iff S hS x y).mp (Finset.mem_inter.mp hy).2
    exact Finset.mem_filter.mpr ⟨heS,Or.inr (Or.inr (Or.inl ⟨hxG,hyS⟩))⟩
  have hc : P.card*τ≤(highProgressFibers S v P).card := by
    rw [highProgressFibers_card]
    calc
      _ = ∑ _x∈P,τ := by simp
      _ ≤ _ := Finset.sum_le_sum (fun x hx=>hthin v x ((mem_symmetric_nbr_iff S hS v x).mp (Finset.mem_inter.mp hx).2))
  simpa only [degOf,presentGraph_neighbors,P] using hc.trans (Finset.card_le_card hsub)
end Qatlib.Concepts.WalkSearch.MainResults
