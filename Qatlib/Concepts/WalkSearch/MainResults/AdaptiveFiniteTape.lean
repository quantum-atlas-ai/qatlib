/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.WalkSearch.Primitives.FiniteMajority
set_option warningAsError false
set_option backward.isDefEq.respectTransparency false
set_option autoImplicit false
set_option maxHeartbeats 1200000
noncomputable section
namespace Qatlib.Concepts.WalkSearch.MainResults
open scoped Classical BigOperators

def adaptiveTapeGood {A X State : Type} (next : A→State→X→State) (correct : A→State→X→Prop) :
    List A→State→(A→X)→Prop
  | [],_,_=>True
  | a::as,s,t=>correct a s (t a) ∧ adaptiveTapeGood next correct as (next a s (t a)) t

theorem adaptiveTapeGood_congr {A X State : Type} (next : A→State→X→State) (correct : A→State→X→Prop)
    (as : List A) (s : State) (t u : A→X) (h : ∀ a∈as,t a=u a) :
    adaptiveTapeGood next correct as s t↔adaptiveTapeGood next correct as s u := by
  induction as generalizing s with
  | nil => rfl
  | cons a as ih =>
    have ha:=h a List.mem_cons_self
    simp only [adaptiveTapeGood,ha]
    exact and_congr_right (fun _=>ih _ (fun b hb=>h b (List.mem_cons_of_mem a hb)))

def extendCoordinate {A X : Type} [DecidableEq A] (a : A) (x : X) (r : {b : A // b≠a}→X) : A→X :=
  (Equiv.funSplitAt a X).symm (x,r)

theorem extendCoordinate_self {A X : Type} [DecidableEq A] (a : A) (x : X) (r : {b : A // b≠a}→X) :
    extendCoordinate a x r a=x := by simp [extendCoordinate,Equiv.funSplitAt,Equiv.piSplitAt]

theorem extendCoordinate_ne {A X : Type} [DecidableEq A] (a : A) (x : X) (r : {b : A // b≠a}→X)
    (b : A) (h : b≠a) : extendCoordinate a x r b=r ⟨b,h⟩ := by
  simp [extendCoordinate,Equiv.funSplitAt,Equiv.piSplitAt,h]

theorem function_event_card_split {A X : Type} [Fintype A] [DecidableEq A] [Fintype X]
    (a : A) (P : (A→X)→Prop) [DecidablePred P] :
    (Finset.univ.filter P).card=∑ x : X,(Finset.univ.filter (fun r : {b : A // b≠a}→X=>P (extendCoordinate a x r))).card := by
  classical
  calc
    _ = ∑ t : A→X,if P t then (1:ℕ) else 0 := by simp only [← Finset.sum_filter,Finset.sum_const,nsmul_eq_mul,mul_one,Nat.cast_id]
    _ = ∑ z : X×({b : A // b≠a}→X),if P ((Equiv.funSplitAt a X).symm z) then 1 else 0 := (Equiv.sum_comp (Equiv.funSplitAt a X).symm (fun t=>if P t then (1:ℕ) else 0)).symm
    _ = _ := by
      rw [Fintype.sum_prod_type]
      simp only [← Finset.sum_filter,Finset.sum_const,nsmul_eq_mul,mul_one,Nat.cast_id,extendCoordinate]

theorem independent_coordinate_event_card {A X : Type} [Fintype A] [DecidableEq A] [Fintype X]
    (a : A) (P : (A→X)→Prop) [DecidablePred P]
    (hP : ∀ t u,(∀ b,b≠a→t b=u b)→(P t↔P u)) (x : X) :
    (Finset.univ.filter P).card=Fintype.card X*
      (Finset.univ.filter (fun r : {b : A // b≠a}→X=>P (extendCoordinate a x r))).card := by
  rw [function_event_card_split a P]
  have he : ∀ y : X,Finset.univ.filter (fun r : {b : A // b≠a}→X=>P (extendCoordinate a y r))=
      Finset.univ.filter (fun r=>P (extendCoordinate a x r)) := by
    intro y
    ext r
    simp only [Finset.mem_filter,Finset.mem_univ,true_and]
    apply hP
    intro b hb
    simp only [extendCoordinate_ne a y r b hb,extendCoordinate_ne a x r b hb]
  simp only [he,Finset.sum_const,Finset.card_univ,nsmul_eq_mul,Nat.cast_id]
end Qatlib.Concepts.WalkSearch.MainResults
