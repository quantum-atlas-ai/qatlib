/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.TrotterFormula.GeneralOrder.NestedCommutatorScalingCorrected

/-!
# Counting prefix commutator tuples

This module embeds prefix-selected commutator tuples into all tuples of one greater length. The
injectivity of `pfPrefixTuple` bounds any nonnegative sum over prefix tuples by the unrestricted
tuple sum.

Applied to nested commutator norms, this counting argument controls the sum of prefix budgets by
`pfCommAlphaSelf xs (p + 1)`, as used in commutator-scaled product-formula estimates
[ChildsEtAl2021Trotter].

## Main statements

* `pfPrefixTuple_injective`: proves injectivity of the prefix-tuple encoding.
* `pfPrefixTuple_sum_le`: compares nonnegative prefix and unrestricted tuple sums.
* `pf_prefix_commutator_budget_le`: bounds the sum of prefix commutator budgets.

## References

* [Childs et al., 2021][ChildsEtAl2021Trotter]
-/

set_option warningAsError false
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 700000
noncomputable section
namespace Qatlib.Concepts.TrotterFormula.GeneralOrder
open scoped Classical BigOperators

/-- The tuple with first entry `j` and remaining entries selected from indices strictly below
`j`. -/
def pfPrefixTuple {p m : ℕ} (j : Fin m) (v : Fin p→Fin j.val) : Fin (p+1)→Fin m :=
  fun i=>if h : i.val=0 then j else
    ⟨(v ⟨i.val-1,by have hi:=i.isLt;omega⟩).val,
      by have hv:=(v ⟨i.val-1,by have hi:=i.isLt;omega⟩).isLt;have hj:=j.isLt;omega⟩

/-- The encoding of a prefix index and its lower-index tuple by `pfPrefixTuple` is injective. -/
theorem pfPrefixTuple_injective (p m : ℕ) :
    Function.Injective (fun z : (j : Fin m) × (Fin p→Fin j.val)=>pfPrefixTuple z.1 z.2) := by
  intro ⟨j,v⟩ ⟨j',v'⟩ he
  have hj := congrFun he (0 : Fin (p+1))
  simp [pfPrefixTuple] at hj
  subst j'
  have hv : v=v' := by
    funext i
    have hi : ¬i.succ.val=0 := by simp only [Fin.val_succ];omega
    have hh := congrFun he i.succ
    simp only [pfPrefixTuple,dif_neg hi] at hh
    apply Fin.ext
    have hl := congrArg Fin.val hh
    change (v i).val=(v' i).val at hl
    exact hl
  rw [hv]

/-- For a nonnegative function, summing over encoded prefix tuples is bounded by summing over
all tuples. -/
theorem pfPrefixTuple_sum_le (p m : ℕ) (f : (Fin (p+1)→Fin m)→ℝ) (hf : ∀ i,0≤f i) :
    (∑ j : Fin m,∑ v : Fin p→Fin j.val,f (pfPrefixTuple j v))≤∑ i : Fin (p+1)→Fin m,f i := by
  let e := fun z : (j : Fin m) × (Fin p→Fin j.val)=>pfPrefixTuple z.1 z.2
  have he : Function.Injective e := pfPrefixTuple_injective p m
  have hs : (∑ z : (j : Fin m) × (Fin p→Fin j.val),f (e z))=
      ∑ i∈Finset.univ.image e,f i := (Finset.sum_image (fun _ _ _ _ h=>he h)).symm
  rw [Fintype.sum_sigma] at hs
  exact hs.le.trans (Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) (fun i _ _=>hf i))
open Matrix
open scoped Matrix.Norms.L2Operator
variable {I : Type} [Fintype I] [DecidableEq I]

omit [DecidableEq I] in

/-- The generator list selected by a tuple of indices below the prefix bound `j`. -/
def pfPrefixSel (xs : List (Matrix I I ℂ)) (j : Fin xs.length) {p : ℕ}
    (v : Fin p→Fin j.val) : List (Matrix I I ℂ) := List.ofFn (fun i=>xs.getD (v i).val 0)

omit [DecidableEq I] in

/-- Selecting generators along a prefix tuple gives the generator at `j` followed by the
selected prefix list. -/
theorem pfChosenList_prefix_tuple (xs : List (Matrix I I ℂ)) (j : Fin xs.length) (p : ℕ)
    (v : Fin p→Fin j.val) :
    pfChosenList xs (pfPrefixTuple j v)=xs.getD j.val 0::pfPrefixSel xs j v := by
  unfold pfChosenList pfPrefixSel
  rw [List.finRange,List.map_ofFn,List.ofFn_succ]
  simp only [Function.comp_def]
  have hz : pfPrefixTuple j v 0=j := by simp [pfPrefixTuple]
  rw [hz]
  apply congrArg (List.cons (xs.getD j.val 0))
  apply congrArg List.ofFn
  funext i
  have hi : ¬i.succ.val=0 := by simp only [Fin.val_succ];omega
  simp only [pfPrefixTuple,dif_neg hi]
  rfl

/-- The sum of prefix commutator budgets is bounded by the full self-commutator statistic at
order `p + 1`. -/
theorem pf_prefix_commutator_budget_le (xs : List (Matrix I I ℂ)) (p : ℕ) :
    (∑ j : Fin xs.length,pfCommAlphaInner (xs.take j.val) (xs.getD j.val 0) p)≤pfCommAlphaSelf xs (p+1) := by
  let g := fun (j : Fin xs.length) (v : Fin p→Fin j.val)=>
    ‖pfNestedCommList (xs.getD j.val 0::pfPrefixSel xs j v)‖
  have hα (j : Fin xs.length) : pfCommAlphaInner (xs.take j.val) (xs.getD j.val 0) p=∑ v : Fin p→Fin j.val,g j v := by
    have hlen : (xs.take j.val).length=j.val := by rw [List.length_take,Nat.min_eq_left j.isLt.le]
    let e := Equiv.piCongrRight (fun _ : Fin p=>finCongr hlen)
    apply Fintype.sum_equiv e
    intro v
    change ‖pfNestedCommList (xs.getD j.val 0::pfChosenList (xs.take j.val) v)‖=g j (e v)
    apply congrArg norm
    apply congrArg pfNestedCommList
    congr 1
    simp only [pfChosenList,List.finRange,List.map_ofFn,Function.comp_def,pfPrefixSel]
    apply congrArg List.ofFn
    funext i
    have hv := (v i).isLt
    have hle : (xs.take j.val).length≤xs.length := by
      rw [List.length_take];exact Nat.min_le_right _ _
    have hvx : (v i).val<xs.length := hv.trans_le hle
    have hev : (e v i).val=(v i).val := rfl
    rw [hev,List.getD_eq_getElem _ _ (v i).isLt,List.getD_eq_getElem _ _ hvx,List.getElem_take]
  simp_rw [hα]
  have hb := pfPrefixTuple_sum_le p xs.length
    (fun idx=>‖pfNestedCommList (pfChosenList xs idx)‖) (fun _=>norm_nonneg _)
  simpa only [pfChosenList_prefix_tuple,g,pfCommAlphaSelf] using! hb

end Qatlib.Concepts.TrotterFormula.GeneralOrder
