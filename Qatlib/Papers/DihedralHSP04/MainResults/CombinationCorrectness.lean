/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.DihedralHSP04.MainResults.Defs
set_option backward.isDefEq.respectTransparency false
set_option warningAsError false

set_option autoImplicit false

noncomputable section

namespace Qatlib.Papers.DihedralHSP04.MainResults

open scoped BigOperators

theorem dotCoeff_maskSub (l : ℕ) (b₁ b₂ : Mask l) (y : SampleSpace l) :
    dotCoeff l (maskSub l b₁ b₂) y = dotMod l b₂ y - dotMod l b₁ y := by
  unfold dotCoeff dotMod maskSub
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  by_cases h₂ : b₂ j <;> by_cases h₁ : b₁ j <;> simp [h₂, h₁]

theorem combinedLabel_eq_zero (l : ℕ) (b₁ b₂ : Mask l) (y : SampleSpace l)
    (z : ZMod (2 ^ l)) (h₁ : dotMod l b₁ y = z) (h₂ : dotMod l b₂ y = z) :
    dotCoeff l (maskSub l b₁ b₂) y = 0 := by
  rw [dotCoeff_maskSub, h₂, h₁, sub_self]

theorem combinedLabel_hasLowBitsZero (l : ℕ) (b₁ b₂ : Mask l)
    (y : SampleSpace l) (z : ZMod (2 ^ l))
    (h₁ : dotMod l b₁ y = z) (h₂ : dotMod l b₂ y = z) :
    hasLowBitsZero l (dotCoeff l (maskSub l b₁ b₂) y).val := by
  have hzero : dotCoeff l (maskSub l b₁ b₂) y = 0 :=
    combinedLabel_eq_zero l b₁ b₂ y z h₁ h₂
  unfold hasLowBitsZero
  rw [hzero, Nat.mod_eq_of_lt]
  · simp
  · exact ZMod.val_lt 0

theorem dotMod_zero_mask (l : ℕ) (y : SampleSpace l) :
    dotMod l (fun _ => false) y = 0 := by
  simp [dotMod]

theorem sum_matchCount (l : ℕ) (y : SampleSpace l) :
    (∑ z : ZMod (2 ^ l), matchCount l y z) = 2 ^ (l + 4) := by
  have h := Finset.card_eq_sum_card_fiberwise
    (s := (Finset.univ : Finset (Mask l)))
    (t := (Finset.univ : Finset (ZMod (2 ^ l))))
    (f := fun b => dotMod l b y) (fun x _ => Finset.mem_univ _)
  have hcard : (Finset.univ : Finset (Mask l)).card = 2 ^ (l + 4) := by
    simp [Mask]
  rw [hcard] at h
  rw [h]
  refine Finset.sum_congr rfl (fun z _ => ?_)
  unfold matchCount matchSet
  rfl

theorem exists_two_distinct_matching_masks (l : ℕ) (y : SampleSpace l)
    (z : ZMod (2 ^ l)) (hs : combinationSucceeds l y z) :
    ∃ b₁ b₂ : Mask l, b₁ ≠ b₂ ∧ dotMod l b₁ y = z ∧ dotMod l b₂ y = z := by
  obtain ⟨hb1, hb2⟩ := hs
  have h1 : 1 < (matchSet l y z).card := by
    unfold matchCount at hb1
    omega
  rw [Finset.one_lt_card] at h1
  obtain ⟨b₁, hmem₁, b₂, hmem₂, hne⟩ := h1
  refine ⟨b₁, b₂, hne, ?_, ?_⟩
  · exact (Finset.mem_filter.mp hmem₁).2
  · exact (Finset.mem_filter.mp hmem₂).2

end Qatlib.Papers.DihedralHSP04.MainResults
