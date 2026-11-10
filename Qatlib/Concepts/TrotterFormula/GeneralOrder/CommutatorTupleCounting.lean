/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.TrotterFormula.GeneralOrder.ConjugationCommutatorExpansion
import Qatlib.Concepts.TrotterFormula.GeneralOrder.GeneralTrotterOrderConsumers
set_option warningAsError false
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 700000
noncomputable section
open Qatlib.Concepts.TrotterFormula.LieStrang

namespace Qatlib.Concepts.TrotterFormula.GeneralOrder
open scoped Classical BigOperators

def pfBlockTuple {p m : ℕ} (j : Fin (p+1)) (v : Fin (p-j.val)→Fin m) : Fin p→Fin (m+1) :=
  fun i=>if hi : i.val<p-j.val then (v ⟨i.val,hi⟩).succ else 0

theorem pfBlockTuple_injective (p m : ℕ) :
    Function.Injective (fun z : (j : Fin (p+1)) × (Fin (p-j.val)→Fin m)=>pfBlockTuple z.1 z.2) := by
  intro ⟨j,v⟩ ⟨j',v'⟩ he
  have hj : j=j' := by
    apply Fin.ext
    rcases lt_trichotomy (p-j.val) (p-j'.val) with hlt | heq | hgt
    · let i : Fin p := ⟨p-j.val,by omega⟩
      have hh := congrFun he i
      have h1 : ¬i.val<p-j.val := by dsimp [i];omega
      have h2 : i.val<p-j'.val := hlt
      simp only [pfBlockTuple,dif_neg h1,dif_pos h2] at hh
      exact False.elim ((Fin.succ_ne_zero _) hh.symm)
    · omega
    · let i : Fin p := ⟨p-j'.val,by omega⟩
      have hh := congrFun he i
      have h1 : i.val<p-j.val := hgt
      have h2 : ¬i.val<p-j'.val := by dsimp [i];omega
      simp only [pfBlockTuple,dif_pos h1,dif_neg h2] at hh
      exact False.elim ((Fin.succ_ne_zero _) hh)
  subst j'
  have hv : v=v' := by
    funext i
    let k : Fin p := ⟨i.val,by have hi:=i.isLt;omega⟩
    have hk : k.val<p-j.val := i.isLt
    have hh := congrFun he k
    simp only [pfBlockTuple,dif_pos hk] at hh
    apply Fin.ext
    have hl := congrArg Fin.val hh
    change (v i).val+1=(v' i).val+1 at hl
    omega
  rw [hv]

theorem pfBlockTuple_sum_le (p m : ℕ) (f : (Fin p→Fin (m+1))→ℝ) (hf : ∀ i,0≤f i) :
    (∑ j : Fin (p+1),∑ v : Fin (p-j.val)→Fin m,f (pfBlockTuple j v))≤∑ i : Fin p→Fin (m+1),f i := by
  let e := fun z : (j : Fin (p+1)) × (Fin (p-j.val)→Fin m)=>pfBlockTuple z.1 z.2
  have he : Function.Injective e := pfBlockTuple_injective p m
  have hs : (∑ z : (j : Fin (p+1)) × (Fin (p-j.val)→Fin m),f (e z))=
      ∑ i∈Finset.univ.image e,f i := (Finset.sum_image (fun _ _ _ _ h=>he h)).symm
  rw [Fintype.sum_sigma] at hs
  exact hs.le.trans (Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
    (fun i _ _=>hf i))
open Matrix
open scoped Matrix.Norms.L2Operator
variable {I : Type} [Fintype I] [DecidableEq I]

omit [DecidableEq I] in

theorem pfChosenList_length (xs : List (Matrix I I ℂ)) {n : ℕ} (idx : Fin n→Fin xs.length) :
    (pfChosenList xs idx).length=n := by simp [pfChosenList]

omit [DecidableEq I] in

theorem pfChosenList_block (X : Matrix I I ℂ) (xs : List (Matrix I I ℂ)) (p : ℕ)
    (j : Fin (p+1)) (v : Fin (p-j.val)→Fin xs.length) :
    pfChosenList (X::xs) (pfBlockTuple j v)=pfChosenList xs v++List.replicate j.val X := by
  apply List.ext_getElem
  · simp only [pfChosenList_length,List.length_append,List.length_replicate]
    have hj:=j.isLt
    omega
  · intro i hi hi'
    have hp : i<p := by simpa only [pfChosenList_length] using! hi
    simp only [pfChosenList,List.getElem_map,List.getElem_finRange,List.getElem_append,List.length_map,List.length_finRange]
    by_cases hij : i<p-j.val
    · simp only [pfBlockTuple,Fin.val_cast,dif_pos hij,Fin.val_succ,List.getD_cons_succ]
      apply congrArg (fun q : Fin (p-j.val)=>xs.getD (v q).val 0)
      exact Fin.ext rfl
    · simp only [pfBlockTuple,Fin.val_cast,dif_neg hij,Fin.val_zero,List.getD_cons_zero,List.getElem_replicate]

omit [DecidableEq I] in

private theorem foldl_replicate_ad (X B : Matrix I I ℂ) (n : ℕ) :
    (List.replicate n X).foldl (fun D Y=>pfComm Y D) B=pfAdPower X B n := by
  induction n generalizing B with
  | zero => rfl
  | succ n ih =>
    simp only [List.replicate_succ,List.foldl_cons,ih]
    exact Function.iterate_succ_apply _ _ _

omit [DecidableEq I] in

theorem pf_nested_block (X B : Matrix I I ℂ) (xs : List (Matrix I I ℂ)) (p : ℕ)
    (j : Fin (p+1)) (v : Fin (p-j.val)→Fin xs.length) :
    pfNestedCommList (B::pfChosenList (X::xs) (pfBlockTuple j v))=
      pfAdPower X (pfNestedCommList (B::pfChosenList xs v)) j.val := by
  rw [pfChosenList_block]
  simp only [pfNestedCommList,List.foldl_append,foldl_replicate_ad]

theorem pf_inner_block_sum_le_map (X B : Matrix I I ℂ) (xs : List (Matrix I I ℂ)) (p : ℕ)
    (L : Matrix I I ℂ→ₗ[ℝ]Matrix I I ℂ) :
    (∑ j : Fin (p+1),∑ v : Fin (p-j.val)→Fin xs.length,
      ‖L (pfAdPower X (pfNestedCommList (B::pfChosenList xs v)) j.val)‖)≤
      ∑ idx : Fin p→Fin (X::xs).length,‖L (pfNestedCommList (B::pfChosenList (X::xs) idx))‖ := by
  have hh := pfBlockTuple_sum_le p xs.length
    (fun idx=>‖L (pfNestedCommList (B::pfChosenList (X::xs) idx))‖) (fun _=>norm_nonneg _)
  simpa only [pf_nested_block] using! hh

def pfInnerAdSum (X B : Matrix I I ℂ) (xs : List (Matrix I I ℂ)) (k j : ℕ) : ℝ :=
  ∑ idx : Fin k→Fin xs.length,‖pfAdPower X (pfNestedCommList (B::pfChosenList xs idx)) j‖

theorem pf_inner_block_split (X B : Matrix I I ℂ) (xs : List (Matrix I I ℂ)) (p : ℕ) :
    (∑ j : Fin (p+1),pfInnerAdSum X B xs (p-j.val) j.val)=
      pfCommAlphaInner xs B p+∑ k : Fin p,pfInnerAdSum X B xs k.val (p-k.val) := by
  let f := fun j : Fin (p+1)=>pfInnerAdSum X B xs (p-j.val) j.val
  let g := fun k : Fin p=>pfInnerAdSum X B xs k.val (p-k.val)
  have hz : f 0=pfCommAlphaInner xs B p := by
    simp only [f,Fin.val_zero,Nat.sub_zero,pfInnerAdSum,pfAdPower_zero,pfCommAlphaInner]
  have hg (i : Fin p) : g i.rev=f i.succ := by
    dsimp only [f,g]
    rw [Fin.val_rev,Fin.val_succ,Nat.sub_sub_self (Nat.succ_le_of_lt i.isLt)]
  change (∑ j : Fin (p+1),f j)=pfCommAlphaInner xs B p+∑ k : Fin p,g k
  rw [Fin.sum_univ_succ,hz]
  congr 1
  calc (∑ i : Fin p,f i.succ)=(∑ i : Fin p,g i.rev) := Finset.sum_congr rfl (fun i _=>(hg i).symm)
       _=∑ i : Fin p,g i := Equiv.sum_comp (show Equiv.Perm (Fin p) from ⟨Fin.rev,Fin.rev,Fin.rev_rev,Fin.rev_rev⟩) g

theorem pf_inner_remainder_budget_le (X B : Matrix I I ℂ) (xs : List (Matrix I I ℂ)) (p : ℕ) :
    pfCommAlphaInner xs B p+∑ k : Fin p,pfInnerAdSum X B xs k.val (p-k.val)≤pfCommAlphaInner (X::xs) B p := by
  rw [← pf_inner_block_split]
  exact pf_inner_block_sum_le_map X B xs p (LinearMap.id)

end Qatlib.Concepts.TrotterFormula.GeneralOrder
