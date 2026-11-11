/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.WalkSearch.MainResults.PairedDrain

/-!
# Bounds on paired removal traces

`removalTraceBound` bounds a removed pair against the final remainder together with the suffix
of pairs not yet removed from the trace. `drainPaired_trace_nodup` and `drainPaired_trace_bound`
verify that paired draining produces a duplicate free trace satisfying this bound. For
background on quantum search and amplitude amplification, see [BrassardEtAl2002].

## Main statements

* `removalTraceBound`: At each list index, the common neighbor count of the listed pair in the
  final remainder united with the current suffix is at most `τ`.
* `drainPaired_trace_bound`: The removal trace of paired draining satisfies `removalTraceBound`
  relative to its final remainder and threshold `τ`.

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

/-- At each list index, the common neighbor count of the listed pair in the final remainder
united with the current suffix is at most `τ`. -/
def removalTraceBound (left : Finset (Fin n×Fin n)) (l : List (Fin n×Fin n)) (τ : ℕ) : Prop :=
  ∀ i,(h : i< l.length)→tOf (left∪(l.drop i).toFinset) l[i].1 l[i].2≤τ

/-- The removal trace produced by `drainPaired` has no repeated pairs. -/
theorem drainPaired_trace_nodup (S : Finset (Fin n×Fin n)) (τ fuel : ℕ) :
    (drainPaired S τ fuel).2.Nodup := by
  induction fuel generalizing S with
  | zero => simp [drainPaired]
  | succ fuel ih =>
    rw [drainPaired]
    cases hh : (S.filter (fun p=>tOf S p.1 p.2<τ)).toList.head? with
    | none => simp
    | some p =>
      (try dsimp only)
      apply List.nodup_append.mpr
      refine ⟨(edgePairBlock S p).nodup_toList,ih _,?_⟩
      intro e he f hf hef
      subst f
      have hD : e∈edgePairBlock S p := Finset.mem_toList.mp he
      have hF : e∈(S\edgePairBlock S p) :=
          (drainPaired_partition (S\edgePairBlock S p) τ fuel).2.1
          (by simpa only [List.mem_toFinset] using hf)
      exact (Finset.mem_sdiff.mp hF).2 hD

/-- The removal trace of paired draining satisfies `removalTraceBound` relative to its final
remainder and threshold `τ`. -/
theorem drainPaired_trace_bound (S : Finset (Fin n×Fin n)) (τ fuel : ℕ) :
    removalTraceBound (drainPaired S τ fuel).1 (drainPaired S τ fuel).2 τ := by
  induction fuel generalizing S with
  | zero => simp [drainPaired,removalTraceBound]
  | succ fuel ih =>
    rw [drainPaired]
    cases hh : (S.filter (fun p=>tOf S p.1 p.2<τ)).toList.head? with
    | none => simp [removalTraceBound]
    | some p =>
      (try dsimp only)
      have hp : p∈S ∧ tOf S p.1 p.2<τ :=
          Finset.mem_filter.mp (Finset.mem_toList.mp (List.mem_of_head? hh))
      let D:=edgePairBlock S p
      let left:=(drainPaired (S\D) τ fuel).1
      let l:=(drainPaired (S\D) τ fuel).2
      have hpart:=drainPaired_partition (S\D) τ fuel
      change removalTraceBound left (D.toList++l) τ
      intro i hi
      by_cases hprefix : i< D.toList.length
      · have hsub : left∪((D.toList++l).drop i).toFinset⊆S := by
          apply Finset.union_subset (hpart.1.trans Finset.sdiff_subset)
          intro e he
          have hm : e∈D.toList++l := List.drop_subset _ _ (List.mem_toFinset.mp he)
          rcases List.mem_append.mp hm with he | he
          · exact edgePairBlock_subset S p (Finset.mem_toList.mp he)
          · exact Finset.sdiff_subset (hpart.2.1 (List.mem_toFinset.mpr he))
        have he : D.toList[i]∈D := Finset.mem_toList.mp (List.getElem_mem hprefix)
        have hE : D.toList[i]=p ∨ D.toList[i]=p.swap := (Finset.mem_filter.mp he).2
        rw [List.getElem_append_left hprefix]
        apply (tOf_mono hsub _ _).trans
        rcases hE with hE | hE
        · simpa only [hE] using hp.2.le
        · simpa only [hE,Prod.fst_swap,Prod.snd_swap,tOf_symm] using hp.2.le
      · have hge : D.toList.length≤ i := by omega
        have hi' : i-D.toList.length< l.length := by rw [List.length_append] at hi;omega
        have hrec := ih (S\D) (i-D.toList.length) hi'
        change tOf (left∪(l.drop (i-D.toList.length)).toFinset) l[i-D.toList.length].1 l[i-D.toList.length].2≤τ at hrec
        rw [List.getElem_append_right hge,List.drop_append,List.drop_eq_nil_iff.mpr hge,List.nil_append]
        exact hrec
end Qatlib.Concepts.WalkSearch.MainResults
