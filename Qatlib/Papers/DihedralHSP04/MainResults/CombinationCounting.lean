/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.DihedralHSP04.MainResults.CombinationCorrectness
set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false

noncomputable section

namespace Qatlib.Papers.DihedralHSP04.MainResults

open scoped BigOperators

def linForm (l : ℕ) (b : Mask l) : SampleSpace l →+ ZMod (2 ^ l) where
  toFun := fun y => dotMod l b y
  map_zero' := by simp [dotMod]
  map_add' := by
    intro x y
    simp only [dotMod, Pi.add_apply]
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    by_cases h : b j <;> simp [h]

theorem linForm_apply (l : ℕ) (b : Mask l) (y : SampleSpace l) :
    linForm l b y = dotMod l b y := rfl

theorem natCard_sampleSpace (l : ℕ) :
    Nat.card (SampleSpace l) = (2 ^ l) ^ (l + 4) := by
  rw [Nat.card_fun]
  simp [Nat.card_eq_fintype_card]

theorem natCard_outcome (l : ℕ) : Nat.card (ZMod (2 ^ l)) = 2 ^ l := by
  rw [Nat.card_eq_fintype_card, ZMod.card]

theorem exists_true_of_ne_zero {l : ℕ} {b : Mask l} (hb : b ≠ zeroMask l) :
    ∃ j : Fin (l + 4), b j = true := by
  by_contra h
  push_neg at h
  apply hb
  funext j
  cases hbj : b j
  · rfl
  · exact absurd hbj (h j)

theorem linForm_surjective {l : ℕ} {b : Mask l} (hb : b ≠ zeroMask l) :
    Function.Surjective (linForm l b) := by
  intro z
  obtain ⟨j, hj⟩ := exists_true_of_ne_zero hb
  refine ⟨Function.update (0 : SampleSpace l) j z, ?_⟩
  rw [linForm_apply]
  unfold dotMod
  rw [Finset.sum_eq_single j]
  · simp [hj]
  · intro j' _ hjne
    simp [Function.update_of_ne hjne, hjne]
  · intro hjnot
    exact absurd (Finset.mem_univ j) hjnot

theorem linForm_fiber_card {l : ℕ} {b : Mask l} (hb : b ≠ zeroMask l)
    (z : ZMod (2 ^ l)) :
    (Finset.univ.filter (fun y : SampleSpace l => dotMod l b y = z)).card =
      (2 ^ l) ^ (l + 3) := by
  have hsurj := linForm_surjective hb
  have hz : z ∈ Set.range (linForm l b) := hsurj z
  have h0 : (0 : ZMod (2 ^ l)) ∈ Set.range (linForm l b) := ⟨0, map_zero _⟩
  have hsame := AddMonoidHom.card_fiber_eq_of_mem_range (linForm l b) hz h0

  have hleft : (Finset.univ.filter (fun y : SampleSpace l => dotMod l b y = z)).card
      = (Finset.univ.filter (fun y : SampleSpace l => linForm l b y = z)).card := by
    simp [linForm_apply]
  have hright : (Finset.univ.filter (fun y : SampleSpace l => linForm l b y = (0 : ZMod (2 ^ l)))).card
      = Nat.card (linForm l b).ker := by
    rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
    congr 1

  have hker : Nat.card (linForm l b).ker = (2 ^ l) ^ (l + 3) := by
    have hmul := (linForm l b).ker.card_mul_index
    rw [AddSubgroup.index_ker] at hmul
    have hrange : Nat.card (linForm l b).range = 2 ^ l := by
      have htop : (linForm l b).range = ⊤ :=
        AddMonoidHom.range_eq_top.mpr hsurj
      rw [htop]
      rw [show Nat.card (⊤ : AddSubgroup (ZMod (2 ^ l))) = Nat.card (ZMod (2 ^ l)) from
        Nat.card_congr (AddSubgroup.topEquiv).toEquiv]
      exact natCard_outcome l
    rw [hrange, natCard_sampleSpace] at hmul
    have hfac : (2 ^ l) ^ (l + 4) = 2 ^ l * (2 ^ l) ^ (l + 3) := by
      rw [show l + 4 = (l + 3) + 1 by omega, pow_succ']
    rw [hfac] at hmul
    rw [mul_comm (Nat.card (linForm l b).ker) (2 ^ l)] at hmul
    exact Nat.eq_of_mul_eq_mul_left (Nat.two_pow_pos l) hmul
  rw [hleft, hsame, hright, hker]

end Qatlib.Papers.DihedralHSP04.MainResults
