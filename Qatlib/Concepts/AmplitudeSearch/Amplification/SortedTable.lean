/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.AmplitudeSearch.Amplification.DiscreteRun
import Mathlib.Data.Finset.Sort
import Mathlib.Data.Prod.Lex
set_option backward.isDefEq.respectTransparency false
set_option warningAsError false

open Qatlib.Concepts.AmplitudeSearch.Amplification.DistinctRankedTable

set_option autoImplicit false

namespace Qatlib.Concepts.AmplitudeSearch.Amplification

structure SortedRankedTable (N : ℕ) (α : Type*) [LinearOrder α] where
  value : Fin N → α
  indexOfRank : Fin N ≃ Fin N
  sorted : Monotone (fun r => value (indexOfRank r))

theorem table_has_sorted_ranks {N : ℕ} {α : Type*} [LinearOrder α] (T : Fin N → α) :
    ∃ e : Fin N ≃ Fin N, Monotone (fun r => T (e r)) := by
  classical
  let pair : Fin N → α ×ₗ Fin N := fun i => toLex (T i, i)
  have hpair : Function.Injective pair := by
    intro i j h
    exact congrArg (fun z : α ×ₗ Fin N => (ofLex z).2) h
  let S : Finset (α ×ₗ Fin N) := Finset.univ.image pair
  have hS : S.card = N := by
    simpa [S] using Finset.card_image_of_injective Finset.univ hpair
  let f : Fin N → S := fun i => ⟨pair i, Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩⟩
  have hf : Function.Bijective f := by
    constructor
    · intro i j h
      exact hpair (congrArg Subtype.val h)
    · intro x
      obtain ⟨i, _, hi⟩ := Finset.mem_image.mp x.property
      exact ⟨i, Subtype.ext hi⟩
  let e : Fin N ≃ S := Equiv.ofBijective f hf
  let o : Fin N ≃o S := S.orderIsoOfFin hS
  have he (i : Fin N) : pair (e.symm (o i)) = (o i).val :=
    congrArg Subtype.val (e.apply_symm_apply (o i))
  refine ⟨o.toEquiv.trans e.symm, ?_⟩
  intro i j hij
  change T (e.symm (o i)) ≤ T (e.symm (o j))
  have hi := congrArg (fun z : α ×ₗ Fin N => (ofLex z).1) (he i)
  have hj := congrArg (fun z : α ×ₗ Fin N => (ofLex z).1) (he j)
  change T (e.symm (o i)) = _ at hi
  change T (e.symm (o j)) = _ at hj
  rw [hi, hj]
  exact Prod.Lex.monotone_fst _ _ (o.monotone hij)

noncomputable def SortedRankedTable.ofTable {N : ℕ} {α : Type*} [LinearOrder α]
    (T : Fin N → α) : SortedRankedTable N α where
  value := T
  indexOfRank := (table_has_sorted_ranks T).choose
  sorted := (table_has_sorted_ranks T).choose_spec

namespace SortedRankedTable

variable {N : ℕ} {α : Type*} [LinearOrder α]

private def nonlower (T : SortedRankedTable N α) (y : Fin N) : Finset (Fin N) :=
  Finset.univ.filter (fun k => ¬ T.value (T.indexOfRank k) < T.value (T.indexOfRank y))

private theorem nonlower_nonempty (T : SortedRankedTable N α) (y : Fin N) :
    (T.nonlower y).Nonempty := ⟨y, by simp [nonlower]⟩

def lowerCut (T : SortedRankedTable N α) (y : Fin N) : Fin N :=
  (T.nonlower y).min' (T.nonlower_nonempty y)

theorem lowerCut_le (T : SortedRankedTable N α) (y : Fin N) : T.lowerCut y ≤ y := by
  exact Finset.min'_le _ y (by simp [nonlower])

theorem smaller_iff_lowerCut (T : SortedRankedTable N α) (y k : Fin N) :
    T.value (T.indexOfRank k) < T.value (T.indexOfRank y) ↔ k < T.lowerCut y := by
  have hnot : ¬ T.value (T.indexOfRank (T.lowerCut y)) < T.value (T.indexOfRank y) :=
    (Finset.mem_filter.mp (Finset.min'_mem _ (T.nonlower_nonempty y))).2
  constructor
  · intro hk
    by_contra h
    exact hnot (lt_of_le_of_lt (T.sorted (le_of_not_gt h)) hk)
  · intro hk
    by_contra h
    have hmem : k ∈ T.nonlower y := Finset.mem_filter.mpr ⟨Finset.mem_univ _, h⟩
    have hle : T.lowerCut y ≤ k := Finset.min'_le _ k hmem
    exact (not_lt_of_ge hle) hk

def skip (T : SortedRankedTable N α) : RankSkip N where
  next y := (T.lowerCut y).val
  le_rank y := T.lowerCut_le y

theorem lowerCut_zero_iff_minimum (T : SortedRankedTable N α) (y : Fin N) :
    (T.lowerCut y).val = 0 ↔ ∀ j, T.value (T.indexOfRank y) ≤ T.value j := by
  constructor
  · intro hz j
    by_contra h
    have hj : T.value (T.indexOfRank (T.indexOfRank.symm j)) < T.value (T.indexOfRank y) := by
      simpa using lt_of_not_ge h
    have hk := (T.smaller_iff_lowerCut y _).mp hj
    change (T.indexOfRank.symm j).val < (T.lowerCut y).val at hk
    omega
  · intro hmin
    by_contra hz
    let z : Fin N := ⟨0, by have := y.isLt; omega⟩
    have hzlt : z < T.lowerCut y := by change 0 < (T.lowerCut y).val; omega
    have hl := (T.smaller_iff_lowerCut y z).mpr hzlt
    exact (not_lt_of_ge (hmin (T.indexOfRank z))) hl

def smallerIndexEquiv (T : SortedRankedTable N α) (y : Fin N) :
    Fin (T.lowerCut y).val ≃ {j : Fin N // T.value j < T.value (T.indexOfRank y)} where
  toFun k := ⟨T.indexOfRank ⟨k.val, lt_trans k.isLt (T.lowerCut y).isLt⟩,
    (T.smaller_iff_lowerCut y _).mpr k.isLt⟩
  invFun j := ⟨(T.indexOfRank.symm j.val).val, by
    apply (T.smaller_iff_lowerCut y _).mp
    simpa using j.property⟩
  left_inv k := by apply Fin.ext; simp
  right_inv j := by apply Subtype.ext; exact T.indexOfRank.apply_symm_apply j.val

theorem marked_card (T : SortedRankedTable N α) (y : Fin N) :
    (Finset.univ.filter (fun j => T.value j < T.value (T.indexOfRank y))).card =
      (T.lowerCut y).val := by
  simpa only [Fintype.card_fin, Fintype.card_subtype] using
    (Fintype.card_congr (T.smallerIndexEquiv y)).symm

end SortedRankedTable
end Qatlib.Concepts.AmplitudeSearch.Amplification
