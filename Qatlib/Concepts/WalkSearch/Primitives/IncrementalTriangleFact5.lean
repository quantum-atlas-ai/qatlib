/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.WalkSearch.Primitives.IncrementalTriangleEncoding

/-!
# Incremental triangle counting

`admissionThirdVertices` records the common neighbors present immediately before an edge's first
admission. Combining these sets into `admissionTriangleTarget` and injecting triangles into that
target proves `fact5_incremental`.

This finite counting argument is used in subset-search reductions, with algorithmic background
in [ChildsEisenberg2003].

## Main statements

* `admissionThirdVertices_card_le`: bound each edge's available third vertices.
* `fact5_incremental`: at most `n.choose 2 * τ` triangles under the prefix common-neighbor
  bound.

## References

* [Childs and Eisenberg, 2003][ChildsEisenberg2003]
-/

set_option autoImplicit false
set_option maxHeartbeats 700000
noncomputable section
namespace Qatlib.Concepts.WalkSearch.Primitives
open scoped Classical BigOperators
variable {n : ℕ}

/-- The common neighbors of an edge's endpoints before its first admission, or the empty set
when neither orientation occurs. -/
def admissionThirdVertices (l : List (Fin n×Fin n)) (e : Fin n×Fin n) : Finset (Fin n) :=
  if edgeAdmissionRank l e < l.length then
    nbrOf (l.take (edgeAdmissionRank l e)).toFinset e.1 ∩ nbrOf (l.take (edgeAdmissionRank l e)).toFinset e.2
  else ∅

/-- If every inserted edge has at most `τ` earlier common neighbors, each
`admissionThirdVertices` set has cardinality at most `τ`. -/
theorem admissionThirdVertices_card_le (l : List (Fin n×Fin n)) (τ : ℕ)
    (hc : ∀ i,(h : i < l.length)→tOf (l.take i).toFinset l[i].1 l[i].2 ≤ τ) (e : Fin n×Fin n) :
    (admissionThirdVertices l e).card ≤ τ := by
  unfold admissionThirdVertices
  split_ifs with h
  · have hh := hc (edgeAdmissionRank l e) h
    rcases edgeAdmissionRank_getElem l e h with he | he
    · simpa only [he,tOf] using hh
    · simpa only [he,Prod.fst_swap,Prod.snd_swap,tOf,Finset.inter_comm] using hh
  · simp

/-- The finite set of canonical edges paired with their common neighbors at first admission. -/
def admissionTriangleTarget (l : List (Fin n×Fin n)) : Finset ((Fin n×Fin n)×Fin n) :=
  (canonicalPairs n).biUnion (fun e=>(admissionThirdVertices l e).image (fun v=>(e,v)))

/-- The last-edge encoding of every canonical triangle belongs to `admissionTriangleTarget l`. -/
theorem triangle_encoding_mem_target (l : List (Fin n×Fin n)) (x : Fin n×Fin n×Fin n)
    (hx : x∈trianglesOf l.toFinset) : triangleLastEdge l x∈admissionTriangleTarget l := by
  have hg := triangleLastEdge_good l x hx
  unfold admissionTriangleTarget
  apply Finset.mem_biUnion.mpr
  refine ⟨(triangleLastEdge l x).1,by simp only [canonicalPairs,Finset.mem_filter,Finset.mem_univ,true_and];exact hg.1,?_⟩
  apply Finset.mem_image.mpr
  refine ⟨(triangleLastEdge l x).2,?_,Prod.eta _⟩
  simpa only [admissionThirdVertices,if_pos hg.2.1] using hg.2.2

/-- Proves `fact5`: the prefix common-neighbor bound implies `triCount T ≤ n.choose 2 * τ`. -/
theorem fact5_incremental : fact5 := by
  intro n τ T l hT _hNodup hc
  have heq : T=l.toFinset := by ext p;simpa only [List.mem_toFinset] using hT p
  subst T
  have hm : (trianglesOf l.toFinset).card ≤ (admissionTriangleTarget l).card := by
    apply Finset.card_le_card_of_injOn (triangleLastEdge l)
    · exact triangle_encoding_mem_target l
    · exact triangleLastEdge_injective l
  have ht : (admissionTriangleTarget l).card ≤ (canonicalPairs n).card*τ := by
    apply (Finset.card_biUnion_le).trans
    calc _ ≤ ∑ e∈canonicalPairs n,τ := Finset.sum_le_sum (fun e _=>
           (Finset.card_image_le).trans (admissionThirdVertices_card_le l τ hc e))
         _=(canonicalPairs n).card*τ := by simp
  exact hm.trans (ht.trans (Nat.mul_le_mul_right τ (canonicalPairs_card_le_choose n)))
end Qatlib.Concepts.WalkSearch.Primitives
