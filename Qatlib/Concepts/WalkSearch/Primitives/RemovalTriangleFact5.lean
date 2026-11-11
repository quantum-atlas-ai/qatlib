/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.WalkSearch.Primitives.IncrementalTriangleFact5

/-!
# Triangle counting along an edge-removal order

`fact5_removal` bounds the triangle count using common-neighbor counts in successive suffixes of
a duplicate-free edge list. This is the removal-order counterpart of incremental counting, a
combinatorial ingredient for graph subset-search reductions [ChildsEisenberg2003].

## Main statements

* `fact5_removal`: at most `n.choose 2 * τ` triangles under the suffix bound.

## References

* [Childs and Eisenberg, 2003][ChildsEisenberg2003]
-/

set_option warningAsError false
set_option autoImplicit false
set_option maxHeartbeats 1000000
noncomputable section
namespace Qatlib.Concepts.WalkSearch.Primitives
open scoped Classical BigOperators

/-- If a duplicate-free listing of `T` has at most `τ` common neighbors for each edge in its
remaining suffix, then `triCount T ≤ n.choose 2 * τ`. -/
theorem fact5_removal (n τ : ℕ) (T : Finset (Fin n×Fin n)) (l : List (Fin n×Fin n))
    (hT : ∀ p,p∈T↔p∈l) (hN : l.Nodup)
    (hc : ∀ i,(h : i<l.length)→tOf (l.drop i).toFinset l[i].1 l[i].2≤τ) :
    triCount T≤n.choose 2*τ := by
  apply fact5_incremental n τ T l.reverse
  · intro p
    simpa only [List.mem_reverse] using hT p
  · simpa only [List.nodup_reverse] using hN
  · intro i hi
    have hi' : i<l.length := by simpa only [List.length_reverse] using hi
    have hj : l.length-1-i<l.length := by omega
    have hh := hc (l.length-1-i) hj
    rw [List.getElem_reverse hi]
    apply (tOf_mono (a:=l[l.length-1-i].1) (b:=l[l.length-1-i].2) ?_).trans hh
    rw [List.take_reverse,List.toFinset_reverse]
    intro e he
    rw [List.mem_toFinset] at he ⊢
    exact List.drop_subset_drop_left l (by omega : l.length-1-i≤l.length-i) he
end Qatlib.Concepts.WalkSearch.Primitives
