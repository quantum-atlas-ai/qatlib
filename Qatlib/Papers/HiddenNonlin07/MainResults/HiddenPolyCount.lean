/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Order.Interval.Finset.Fin
import Mathlib.Tactic

/-!
# A binomial inequality for polynomial counting

This module proves a finite combinatorial inequality used in the hidden-polynomial counting
arguments associated with [ChildsSchulmanVazirani2007]. For `d ≥ 2` and `1 ≤ t' < t`,
`choose_add_choose_le` bounds the sum of two binomial counts by `(d + t).choose d`.

The proof compares size-`d` subsets in two intervals of a finite ordered set. Their families
intersect in one subset, while a further size-`d` subset lies outside their union.

## Main statements

* `choose_add_choose_le`: establishes the binomial-count inequality.

## References

* [Childs et al., 2007][ChildsSchulmanVazirani2007]
-/

set_option autoImplicit false

namespace Qatlib.Papers.HiddenNonlin07.MainResults.HiddenPolyCount

open Finset

/-- For `d ≥ 2` and `1 ≤ t' < t`, the sum of `(d + t').choose d` and `(d + t - t').choose d` is
at most `(d + t).choose d`. [ChildsSchulmanVazirani2007]. -/
theorem choose_add_choose_le {d t t' : ℕ} (hd : 2 ≤ d) (ht' : 1 ≤ t') (htt' : t' < t) :
    (d + t').choose d + (d + t - t').choose d ≤ (d + t).choose d := by
  classical
  set n : ℕ := d + t with hn
  have hdt : d ≤ n := by omega
  have hlt : d + t' < n := by omega
  have ht'n : t' < n := by omega
  have hd1 : d - 1 < n := by omega
  let P : Finset (Finset (Fin n)) := Finset.univ.powersetCard d
  let low : Finset (Fin n) := Finset.Iio (⟨d + t', hlt⟩ : Fin n)
  let high : Finset (Fin n) := Finset.Ici (⟨t', ht'n⟩ : Fin n)
  let F1 : Finset (Finset (Fin n)) := P.filter (fun S => S ⊆ low)
  let F2 : Finset (Finset (Fin n)) := P.filter (fun S => S ⊆ high)
  have hP : P.card = (d + t).choose d := by
    simp [P, hn]
  have hlow : low.card = d + t' := by
    simp [low]
  have hhigh : high.card = d + t - t' := by
    simp [high, hn]
  have hF1 : F1.card = (d + t').choose d := by
    have hEq : F1 = low.powersetCard d := by
      ext S
      simp [F1, P, Finset.mem_powersetCard, and_comm]
    rw [hEq, Finset.card_powersetCard, hlow]
  have hF2 : F2.card = (d + t - t').choose d := by
    have hEq : F2 = high.powersetCard d := by
      ext S
      simp [F2, P, Finset.mem_powersetCard, and_comm]
    rw [hEq, Finset.card_powersetCard, hhigh]
  have hlowhigh : (low ∩ high).card = d := by
    have hEq : low ∩ high = Finset.Ico (⟨t', ht'n⟩ : Fin n) (⟨d + t', hlt⟩ : Fin n) := by
      ext i
      simp only [low, high, Finset.mem_inter, Finset.mem_Iio, Finset.mem_Ici,
        Finset.mem_Ico, Fin.lt_def, Fin.le_def]
      omega
    rw [hEq]
    simp only [Fin.card_Ico]
    omega
  have hinter : F1 ∩ F2 = (low ∩ high).powersetCard d := by
    ext S
    simp only [F1, F2, P, Finset.mem_inter, Finset.mem_filter, Finset.mem_powersetCard,
      Finset.subset_univ, true_and]
    constructor
    · rintro ⟨⟨hcd, h1⟩, ⟨-, h2⟩⟩
      exact ⟨Finset.subset_inter h1 h2, hcd⟩
    · rintro ⟨hsub, hcd⟩
      exact ⟨⟨hcd, hsub.trans Finset.inter_subset_left⟩,
        hcd, hsub.trans Finset.inter_subset_right⟩
  have hinit : (F1 ∩ F2).card = 1 := by
    rw [hinter, Finset.card_powersetCard, hlowhigh]
    simp
  let last : Fin n := ⟨n - 1, by omega⟩
  let S0 : Finset (Fin n) := Finset.Iio (⟨d - 1, hd1⟩ : Fin n) ∪ {last}
  have hlastnot : last ∉ Finset.Iio (⟨d - 1, hd1⟩ : Fin n) := by
    simp only [Finset.mem_Iio, Fin.lt_def, last]
    omega
  have hS0card : S0.card = d := by
    have : S0 = insert last (Finset.Iio (⟨d - 1, hd1⟩ : Fin n)) := by
      simp [S0, Finset.union_singleton]
    rw [this, Finset.card_insert_of_notMem hlastnot]
    simp only [Fin.card_Iio]
    omega
  have hS0memP : S0 ∈ P := by
    simp [P, Finset.mem_powersetCard, hS0card]
  have hlast0 : last.val = n - 1 := rfl
  have hS0notF1 : S0 ∉ F1 := by
    simp only [F1, Finset.mem_filter, hS0memP, true_and]
    intro hsub
    have hlastmem : last ∈ low := hsub (by simp [S0])
    simp only [low, Finset.mem_Iio, Fin.lt_def, hlast0] at hlastmem
    omega
  have hzero : (⟨0, by omega⟩ : Fin n) ∈ S0 := by
    have hmem : (⟨0, by omega⟩ : Fin n) ∈ Finset.Iio (⟨d - 1, hd1⟩ : Fin n) := by
      simp only [Finset.mem_Iio, Fin.lt_def]
      omega
    simp [S0, hmem]
  have hS0notF2 : S0 ∉ F2 := by
    simp only [F2, Finset.mem_filter, hS0memP, true_and]
    intro hsub
    have hmem : (⟨0, by omega⟩ : Fin n) ∈ high := hsub hzero
    simp only [high, Finset.mem_Ici, Fin.le_def] at hmem
    omega
  have hsub : F1 ∪ F2 ⊆ P := by
    intro S hS
    rcases Finset.mem_union.mp hS with h | h
    · exact (Finset.mem_filter.mp h).1
    · exact (Finset.mem_filter.mp h).1
  have hne : F1 ∪ F2 ≠ P := by
    intro heq
    have hmem : S0 ∈ F1 ∪ F2 := by
      rw [heq]
      exact hS0memP
    rcases Finset.mem_union.mp hmem with h | h
    · exact hS0notF1 h
    · exact hS0notF2 h
  have hltcard : (F1 ∪ F2).card < P.card :=
    Finset.card_lt_card (Finset.ssubset_iff_subset_ne.mpr ⟨hsub, hne⟩)
  have hle : (F1 ∪ F2).card + 1 ≤ (d + t).choose d := by
    rw [← hP]
    exact Nat.succ_le_of_lt hltcard
  have hcard : (F1 ∪ F2).card + (F1 ∩ F2).card = F1.card + F2.card :=
    Finset.card_union_add_card_inter F1 F2
  rw [hinit, hF1, hF2] at hcard
  rw [← hcard]
  exact hle

end Qatlib.Papers.HiddenNonlin07.MainResults.HiddenPolyCount
