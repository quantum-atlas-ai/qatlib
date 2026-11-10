/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.ElemDistinct00.MainResults.Defs
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Disjoint
import Mathlib.Data.Int.Basic
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Tactic
set_option backward.isDefEq.respectTransparency false
set_option warningAsError false

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.ElemDistinct00.MainResults.RelatedProblems

open Qatlib.Papers.ElemDistinct00.MainResults.Defs

variable {N : ℕ}

def fibre (f : Fin N → Fin N) (z : Fin N) : Finset (Fin N) :=
  Finset.univ.filter fun x => f x = z

@[simp] theorem mem_fibre {f : Fin N → Fin N} {z x : Fin N} :
    x ∈ fibre f z ↔ f x = z := by
  simp [fibre]

def FibresLeTwo (f : Fin N → Fin N) : Prop := ∀ z, (fibre f z).card ≤ 2

theorem fibre_card_pos (f : Fin N → Fin N) (x : Fin N) : 0 < (fibre f (f x)).card :=
  Finset.card_pos.mpr ⟨x, by simp⟩

theorem sum_fibre_card (f : Fin N → Fin N) : ∑ z, (fibre f z).card = N := by
  have h := Finset.card_eq_sum_card_fiberwise
    (s := (Finset.univ : Finset (Fin N))) (t := (Finset.univ : Finset (Fin N)))
    (f := f) (fun x _ => Finset.mem_univ (f x))
  simpa [fibre] using h.symm

theorem fibre_update (f : Fin N → Fin N) (x w z : Fin N) :
    fibre (Function.update f x w) z
      = (fibre f z).erase x ∪ (if z = w then {x} else ∅) := by
  ext y
  by_cases hy : y = x
  · subst hy
    by_cases hz : z = w
    · subst hz
      simp [fibre, Function.update_self]
    · have hzw : w ≠ z := fun h => hz h.symm
      simp [fibre, Function.update_self, hz, hzw]
  · by_cases hz : z = w
    · simp [fibre, Function.update_apply, hy, hz]
    · simp [fibre, Function.update_apply, hy, hz]

theorem card_fibre_update (f : Fin N → Fin N) (x w z : Fin N) :
    (fibre (Function.update f x w) z).card
      = (fibre f z).card + (if z = w then 1 else 0) - (if z = f x then 1 else 0) := by
  rw [fibre_update]
  have hdisj : Disjoint ((fibre f z).erase x)
      (if z = w then ({x} : Finset (Fin N)) else ∅) := by
    rw [Finset.disjoint_left]
    intro y hy1
    rw [Finset.mem_erase] at hy1
    by_cases hz : z = w
    · rw [if_pos hz]
      simpa using hy1.1
    · rw [if_neg hz]
      simp
  rw [Finset.card_union_of_disjoint hdisj]
  by_cases hx : x ∈ fibre f z
  · have hfz : f x = z := by simpa using hx
    have hcard : 1 ≤ (fibre f z).card := Finset.card_pos.mpr ⟨x, hx⟩
    rw [Finset.card_erase_of_mem hx, hfz]
    have hifcard : (if z = w then ({x} : Finset (Fin N)) else ∅).card
        = (if z = w then 1 else 0) := by
      by_cases hz : z = w <;> simp [hz]
    have hzz : (if z = z then (1 : ℕ) else 0) = 1 := if_pos rfl
    rw [hifcard, hzz]
    clear hifcard hzz hfz hx hdisj
    omega
  · have hfz : f x ≠ z := by simpa using hx
    rw [Finset.erase_eq_of_notMem hx]
    have hifcard : (if z = w then ({x} : Finset (Fin N)) else ∅).card
        = (if z = w then 1 else 0) := by
      by_cases hz : z = w <;> simp [hz]
    have hzfx : (if z = f x then (1 : ℕ) else 0) = 0 := by
      rw [if_neg (Ne.symm hfz)]
    rw [hifcard, hzfx]
    simp

def collSum (f : Fin N → Fin N) : ℕ := ∑ z, (fibre f z).card.choose 2

theorem sum_sub_eq_two_points {α : Type*} [Fintype α] [DecidableEq α]
    (F G : α → ℤ) (a b : α) (hab : a ≠ b)
    (h : ∀ z, z ≠ a → z ≠ b → G z = F z) :
    (∑ z, G z) - (∑ z, F z) = (G a - F a) + (G b - F b) := by
  rw [← Finset.sum_sub_distrib]
  have hsub : ∑ z ∈ ({a, b} : Finset α), (G z - F z) = ∑ z, (G z - F z) := by
    refine Finset.sum_subset (Finset.subset_univ _) ?_
    intro z _ hz
    have hza : z ≠ a := fun hh => hz (by simp [hh])
    have hzb : z ≠ b := fun hh => hz (by simp [hh])
    simp [h z hza hzb]
  rw [← hsub, Finset.sum_pair hab]

theorem collSum_update_delta (f : Fin N → Fin N) (x w : Fin N) (hw : w ≠ f x) :
    ((collSum (Function.update f x w) : ℤ) - (collSum f : ℤ))
      = ((fibre f w).card : ℤ) - (((fibre f (f x)).card : ℤ) - 1) := by
  have hF : (collSum f : ℤ) = ∑ z, ((fibre f z).card.choose 2 : ℤ) := by
    simp [collSum]
  have hG : (collSum (Function.update f x w) : ℤ)
      = ∑ z, ((fibre (Function.update f x w) z).card.choose 2 : ℤ) := by
    simp [collSum]
  have hpt : ∀ z, z ≠ w → z ≠ f x →
      ((fibre (Function.update f x w) z).card.choose 2 : ℤ)
        = ((fibre f z).card.choose 2 : ℤ) := by
    intro z hzw hzx
    rw [card_fibre_update f x w z]
    have h1 : (if z = w then (1 : ℕ) else 0) = 0 := by simp [hzw]
    have h2 : (if z = f x then (1 : ℕ) else 0) = 0 := by simp [hzx]
    rw [h1, h2]
    simp
  have hmain := sum_sub_eq_two_points
    (F := fun z => ((fibre f z).card.choose 2 : ℤ))
    (G := fun z => ((fibre (Function.update f x w) z).card.choose 2 : ℤ))
    w (f x) hw hpt
  rw [hF, hG, hmain]
  have hwcard : (fibre (Function.update f x w) w).card = (fibre f w).card + 1 := by
    rw [card_fibre_update f x w w]
    have h1 : (if w = f x then (1 : ℕ) else 0) = 0 := by simp [hw]
    rw [h1]
    simp
  have hzcard : (fibre (Function.update f x w) (f x)).card
      = (fibre f (f x)).card - 1 := by
    rw [card_fibre_update f x w (f x)]
    have h1 : (if f x = w then (1 : ℕ) else 0) = 0 := by rw [if_neg (Ne.symm hw)]
    rw [h1]
    simp
  have hchoose_succ : ((fibre f w).card + 1).choose 2
      = (fibre f w).card.choose 2 + (fibre f w).card := by
    have h := Nat.choose_succ_succ (fibre f w).card 1
    rw [Nat.choose_one_right] at h
    exact h.trans (Nat.add_comm _ _)
  have hnz : 1 ≤ (fibre f (f x)).card := fibre_card_pos f x
  have hchoose_pred : (fibre f (f x)).card.choose 2
      = ((fibre f (f x)).card - 1).choose 2 + ((fibre f (f x)).card - 1) := by
    have h := Nat.choose_succ_succ ((fibre f (f x)).card - 1) 1
    have hs : ((fibre f (f x)).card - 1).succ = (fibre f (f x)).card := by
      rw [Nat.succ_eq_add_one, Nat.sub_add_cancel hnz]
    rw [hs, Nat.choose_one_right, Nat.add_comm] at h
    exact h
  have hsucc' : ((fibre (Function.update f x w) w).card.choose 2 : ℤ)
      = ((fibre f w).card.choose 2 : ℤ) + ((fibre f w).card : ℤ) := by
    rw [hwcard]
    have h1 : ((((fibre f w).card + 1).choose 2 : ℕ) : ℤ)
        = (((fibre f w).card.choose 2 + (fibre f w).card : ℕ) : ℤ) := by
      rw [hchoose_succ]
    rw [Nat.cast_add] at h1
    exact h1
  have hpred' : ((fibre f (f x)).card.choose 2 : ℤ)
      = ((fibre (Function.update f x w) (f x)).card.choose 2 : ℤ)
        + (((fibre f (f x)).card : ℤ) - 1) := by
    have hsub : (((fibre f (f x)).card - 1 : ℕ) : ℤ) = ((fibre f (f x)).card : ℤ) - 1 := by
      rw [Nat.cast_sub hnz, Nat.cast_one]
    rw [hzcard]
    have h1 : (((fibre f (f x)).card.choose 2 : ℕ) : ℤ)
        = ((((fibre f (f x)).card - 1).choose 2 + ((fibre f (f x)).card - 1) : ℕ) : ℤ) := by
      rw [hchoose_pred]
    rw [Nat.cast_add, hsub] at h1
    exact h1
  try dsimp only
  rw [hsucc', hpred']
  ring

theorem collSum_eq_card_doubles (f : Fin N → Fin N) (h2 : FibresLeTwo f) :
    collSum f = (Finset.univ.filter fun z => (fibre f z).card = 2).card := by
  unfold collSum
  have hpoint : ∀ z, (fibre f z).card.choose 2
      = (if (fibre f z).card = 2 then 1 else 0) := by
    intro z
    have hz := h2 z
    have hcases : (fibre f z).card = 0 ∨ (fibre f z).card = 1 ∨ (fibre f z).card = 2 := by
      omega
    rcases hcases with h | h | h <;> rw [h] <;> norm_num
  calc ∑ z, (fibre f z).card.choose 2
      = ∑ z, (if (fibre f z).card = 2 then 1 else 0) :=
        Finset.sum_congr rfl (fun z _ => hpoint z)
    _ = (Finset.univ.filter fun z => (fibre f z).card = 2).card := by
        simp

theorem card_singletons_add (f : Fin N → Fin N) (h2 : FibresLeTwo f) :
    (Finset.univ.filter fun z => (fibre f z).card = 1).card
      + 2 * (Finset.univ.filter fun z => (fibre f z).card = 2).card = N := by
  have hsum := sum_fibre_card f
  have hpoint : ∀ z, (fibre f z).card
      = (if (fibre f z).card = 1 then 1 else 0)
        + 2 * (if (fibre f z).card = 2 then 1 else 0) := by
    intro z
    have hz := h2 z
    have hcases : (fibre f z).card = 0 ∨ (fibre f z).card = 1 ∨ (fibre f z).card = 2 := by
      omega
    rcases hcases with h | h | h <;> rw [h] <;> norm_num
  calc (Finset.univ.filter fun z => (fibre f z).card = 1).card
        + 2 * (Finset.univ.filter fun z => (fibre f z).card = 2).card
      = (∑ z, (if (fibre f z).card = 1 then 1 else 0))
        + 2 * (∑ z, (if (fibre f z).card = 2 then 1 else 0)) := by
        simp
    _ = ∑ z, ((if (fibre f z).card = 1 then 1 else 0)
        + 2 * (if (fibre f z).card = 2 then 1 else 0)) := by
        rw [Finset.sum_add_distrib, Finset.mul_sum]
    _ = ∑ z, (fibre f z).card := Finset.sum_congr rfl (fun z _ => (hpoint z).symm)
    _ = N := hsum

end Qatlib.Papers.ElemDistinct00.MainResults.RelatedProblems
