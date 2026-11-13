/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.WalkSearch.MainResults.AdaptiveFiniteTape

/-!
# A union bound for adaptive finite tapes

`adaptiveTape_bad_card_bound` bounds the number of tapes on which a stateful computation fails.
A uniform error bound at each coordinate accumulates linearly along a list without repeated
coordinates, even though subsequent states depend on earlier tape values. For background on
quantum search and amplitude amplification, see [BrassardEtAl2002].

## Main statements

* `adaptiveTape_bad_card_bound`: For a list of distinct coordinates and a uniform local bound
  `bad * R ≤ C * Fintype.card X`, the number of failing tapes times `R` is at most the list
  length times `C` times the total tape count.

## References

* [Brassard et al., 2002][BrassardEtAl2002]
-/

set_option backward.isDefEq.respectTransparency false
set_option autoImplicit false
set_option maxHeartbeats 1600000
noncomputable section
namespace Qatlib.Concepts.WalkSearch.MainResults
open scoped Classical BigOperators

/-- For a list of distinct coordinates and a uniform local bound `bad * R ≤ C * Fintype.card X`,
the number of failing tapes times `R` is at most the list length times `C` times the total
tape count. -/
theorem adaptiveTape_bad_card_bound {A X State : Type} [Fintype A] [DecidableEq A]
    [Fintype X] [Nonempty X] (next : A→State→X→State) (correct : A→State→X→Prop)
    (R C : ℕ) (herr : ∀ a s,(Finset.univ.filter (fun x : X=>¬correct a s x)).card*R≤C*Fintype.card X)
    (as : List A) (hN : as.Nodup) (s : State) :
    (Finset.univ.filter (fun t : A→X=>¬adaptiveTapeGood next correct as s t)).card*R≤
      as.length*C*Fintype.card (A→X) := by
  classical
  induction as generalizing s with
  | nil => simp [adaptiveTapeGood]
  | cons a as ih =>
    have hn:=List.nodup_cons.mp hN
    let Rest : Type := {b : A // b≠a}→X
    let B : X→Finset Rest :=
        fun x=>Finset.univ.filter (fun r=>¬adaptiveTapeGood next correct as (next a s x) (extendCoordinate a x r))
    have hfull : Fintype.card (A→X)=Fintype.card X*Fintype.card Rest :=
      (Fintype.card_congr (Equiv.funSplitAt a X)).trans (Fintype.card_prod _ _)
    have hX : 0<Fintype.card X := Fintype.card_pos
    have hfiber : ∀ x,(B x).card*R≤as.length*C*Fintype.card Rest := by
      intro x
      have hi:=ih hn.2 (next a s x)
      have he:=independent_coordinate_event_card a (fun t : A→X=>¬adaptiveTapeGood next correct as (next a s x) t) (by
        intro t u htu
        apply not_congr
        apply adaptiveTapeGood_congr
        intro b hb
        exact htu b (fun he=>hn.1 (by simpa only [he] using hb))) x
      rw [he,hfull] at hi
      have hh : Fintype.card X*((B x).card*R)≤Fintype.card X*(as.length*C*Fintype.card Rest) := by
        dsimp [B]
        nlinarith [hi]
      exact (mul_le_mul_iff_left₀ hX).mp (by simpa only [Nat.mul_comm] using hh)
    have hroot : (Finset.univ.filter (fun t : A→X=>¬adaptiveTapeGood next correct (a::as) s t)).card≤
        (Finset.univ.filter (fun x : X=>¬correct a s x)).card*Fintype.card Rest+∑ x,(B x).card := by
      rw [function_event_card_split a]
      have hOne (x : X) : (Finset.univ.filter (fun r : Rest=>¬adaptiveTapeGood next correct (a::as) s (extendCoordinate a x r))).card≤
          (if ¬correct a s x then Fintype.card Rest else 0)+(B x).card := by
        have hs : Finset.univ.filter (fun r : Rest=>¬adaptiveTapeGood next correct (a::as) s (extendCoordinate a x r)) ⊆
            (if ¬correct a s x then Finset.univ else ∅)∪B x := by
          intro r hr
          have hh:= (Finset.mem_filter.mp hr).2
          simp only [adaptiveTapeGood,extendCoordinate_self,not_and_or] at hh
          rcases hh with hc | ht
          · exact Finset.mem_union_left _ (by rw [if_pos hc];exact Finset.mem_univ _)
          · exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨Finset.mem_univ _,ht⟩)
        have hh:=(Finset.card_le_card hs).trans (Finset.card_union_le _ _)
        by_cases hc : ¬correct a s x
        · simpa only [if_pos hc,Finset.card_univ] using hh
        · simpa only [if_neg hc,Finset.card_empty] using hh
      apply (Finset.sum_le_sum (fun x _=>hOne x)).trans_eq
      rw [Finset.sum_add_distrib]
      simp only [← Finset.sum_filter,Finset.sum_const,nsmul_eq_mul,Nat.cast_id]
    have hsum : (∑ x,(B x).card)*R≤Fintype.card X*(as.length*C*Fintype.card Rest) := by
      rw [Finset.sum_mul]
      apply (Finset.sum_le_sum (fun x _=>hfiber x)).trans_eq
      simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul,Nat.cast_id]
    have herror:=Nat.mul_le_mul_right (Fintype.card Rest) (herr a s)
    have hh:=Nat.mul_le_mul_right R hroot
    rw [hfull,List.length_cons]
    nlinarith
end Qatlib.Concepts.WalkSearch.MainResults
