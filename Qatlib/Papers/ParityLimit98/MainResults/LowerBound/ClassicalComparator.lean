/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.ParityLimit98.MainResults.LowerBound.ParityBalance
import Qatlib.Concepts.QueryComplexity.DegreeMethod.ClassicalQuery
set_option warningAsError false

set_option autoImplicit false
namespace Qatlib.Papers.ParityLimit98.MainResults.LowerBound
open Qatlib.Concepts.QueryComplexity.DegreeMethod

def inspected {I O : Type} [DecidableEq I] (f : I → Bool) : BoolQueryTree I O → Finset I
  | .halt _ => ∅
  | .ask i a b => insert i (if f i then inspected f b else inspected f a)

theorem inspected_card_le_calls {I O : Type} [DecidableEq I]
    (f : I → Bool) (T : BoolQueryTree I O) :
    (inspected f T).card ≤ (BoolQueryTree.Run f T).2 := by
  induction T with
  | halt o => simp [inspected, BoolQueryTree.Run]
  | ask i a b ha hb =>
    cases hf : f i <;> simp only [inspected, BoolQueryTree.Run, hf, Bool.false_eq_true,
      if_false, if_true]
    · exact (Finset.card_insert_le _ _).trans (Nat.add_le_add_right ha 1)
    · exact (Finset.card_insert_le _ _).trans (Nat.add_le_add_right hb 1)

theorem classical_run_eq_of_inspected_agreement {I O : Type} [DecidableEq I]
    (f g : I → Bool) (T : BoolQueryTree I O)
    (h : ∀ i ∈ inspected f T, f i = g i) : BoolQueryTree.Run f T = BoolQueryTree.Run g T := by
  induction T with
  | halt o => rfl
  | ask i a b ha hb =>
    have hi : f i = g i := h i (Finset.mem_insert_self _ _)
    cases hf : f i
    · have hg : g i = false := hi.symm.trans hf
      have ht : ∀ j ∈ inspected f a, f j = g j := fun j hj =>
        h j (Finset.mem_insert_of_mem (by simpa [hf] using hj))
      simp only [BoolQueryTree.Run, hf, hg, Bool.false_eq_true, if_false, ha ht]
    · have hg : g i = true := hi.symm.trans hf
      have ht : ∀ j ∈ inspected f b, f j = g j := fun j hj =>
        h j (Finset.mem_insert_of_mem (by simpa [hf] using hj))
      simp only [BoolQueryTree.Run, hf, hg, if_true, hb ht]

theorem parityOddB_flip_ne {I : Type} [Fintype I] [DecidableEq I] (i : I) (f : I → Bool) :
    parityOddB (flipAt i f) ≠ parityOddB f := by
  intro h
  have hs := boolSign_flipAt i f
  rw [boolSign_eq_ite, boolSign_eq_ite, h] at hs
  cases hp : parityOddB f <;> norm_num [hp] at hs

theorem classical_parity_inspects_all {I : Type} [Fintype I] [DecidableEq I]
    (T : BoolQueryTree I Bool) (hc : ∀ f, (BoolQueryTree.Run f T).1 = parityOddB f)
    (f : I → Bool) : inspected f T = Finset.univ := by
  apply Finset.eq_univ_of_forall
  intro i
  by_contra hi
  have hrun := classical_run_eq_of_inspected_agreement f (flipAt i f) T (by
    intro j hj
    have hji : j ≠ i := fun he => hi (he ▸ hj)
    simp [flipAt, Function.update_of_ne hji])
  have hout := congrArg Prod.fst hrun
  rw [hc f, hc (flipAt i f)] at hout
  exact parityOddB_flip_ne i f hout.symm

theorem classical_parity_query_lower {I : Type} [Fintype I] [DecidableEq I]
    (T : BoolQueryTree I Bool) (hc : ∀ f, (BoolQueryTree.Run f T).1 = parityOddB f)
    (f : I → Bool) : Fintype.card I ≤ (BoolQueryTree.Run f T).2 := by
  have h := inspected_card_le_calls f T
  rw [classical_parity_inspects_all T hc f, Finset.card_univ] at h
  exact h

end Qatlib.Papers.ParityLimit98.MainResults.LowerBound
