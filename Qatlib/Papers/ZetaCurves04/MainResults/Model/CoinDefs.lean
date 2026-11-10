/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.ZetaCurves04.MainResults.Model.CurveZetaDefs
set_option warningAsError false

set_option autoImplicit false
noncomputable section

open scoped BigOperators
open Finset

namespace Qatlib.Papers.ZetaCurves04.MainResults.Model

structure CoinAlgo (α : Type*) where

  Coin : Type*

  instFintype : Fintype Coin

  instDecEq : DecidableEq Coin

  run : Coin → Option α

  cost : ℕ

attribute [instance] CoinAlgo.instFintype CoinAlgo.instDecEq

noncomputable def CoinAlgo.indicator {α : Type*} (A : CoinAlgo α) (good : α → Prop)
    (c : A.Coin) : ℝ := by
  classical
  exact if ∃ x, A.run c = some x ∧ good x then 1 else 0

noncomputable def CoinAlgo.succProb {α : Type*} (A : CoinAlgo α) (good : α → Prop) : ℝ :=
  (∑ c : A.Coin, A.indicator good c) / (Fintype.card A.Coin : ℝ)

def CoinAlgo.IsMC {α : Type*} (A : CoinAlgo α) (good : α → Prop) : Prop :=
  (3 : ℝ) / 4 ≤ A.succProb good

theorem CoinAlgo.indicator_mono {α : Type*} (A : CoinAlgo α)
    {good good' : α → Prop} (h : ∀ x, good x → good' x) (c : A.Coin) :
    A.indicator good c ≤ A.indicator good' c := by
  classical
  unfold CoinAlgo.indicator
  by_cases hc : ∃ x, A.run c = some x ∧ good x
  · have hc' : ∃ x, A.run c = some x ∧ good' x := by
      obtain ⟨x, hx, hg⟩ := hc
      exact ⟨x, hx, h x hg⟩
    simp [hc, hc']
  · simp only [hc, if_false]
    split_ifs <;> norm_num

theorem CoinAlgo.succProb_mono {α : Type*} (A : CoinAlgo α)
    {good good' : α → Prop} (h : ∀ x, good x → good' x) :
    A.succProb good ≤ A.succProb good' := by
  unfold CoinAlgo.succProb
  apply div_le_div_of_nonneg_right _ (by positivity)
  exact Finset.sum_le_sum (fun c _ => CoinAlgo.indicator_mono A h c)

def CoinAlgo.map {α β : Type*} (A : CoinAlgo α) (f : α → β) : CoinAlgo β where
  Coin := A.Coin
  instFintype := A.instFintype
  instDecEq := A.instDecEq
  run c := (A.run c).map f
  cost := A.cost

theorem CoinAlgo.map_pred_iff {α β : Type*} (A : CoinAlgo α) (f : α → β)
    (good : β → Prop) (c : A.Coin) :
    (∃ y, (A.run c).map f = some y ∧ good y)
      ↔ ∃ a, A.run c = some a ∧ good (f a) := by
  simp only [Option.map_eq_some_iff]
  constructor
  · rintro ⟨y, ⟨a, ha, rfl⟩, hgood⟩
    exact ⟨a, ha, hgood⟩
  · rintro ⟨a, ha, hgood⟩
    exact ⟨f a, ⟨a, ha, rfl⟩, hgood⟩

theorem CoinAlgo.indicator_map {α β : Type*} (A : CoinAlgo α) (f : α → β)
    (good : β → Prop) (c : A.Coin) :
    (A.map f).indicator good c = A.indicator (fun x => good (f x)) c := by
  classical
  unfold CoinAlgo.indicator
  show (if ∃ y, (A.run c).map f = some y ∧ good y then (1 : ℝ) else 0)
      = (if ∃ a, A.run c = some a ∧ good (f a) then 1 else 0)
  by_cases h : ∃ a, A.run c = some a ∧ good (f a)
  · have h' : ∃ y, (A.run c).map f = some y ∧ good y :=
      (CoinAlgo.map_pred_iff A f good c).mpr h
    simp [h, h']
  · have h' : ¬ ∃ y, (A.run c).map f = some y ∧ good y :=
      fun hh => h ((CoinAlgo.map_pred_iff A f good c).mp hh)
    simp [h, h']

theorem CoinAlgo.succProb_map {α β : Type*} (A : CoinAlgo α) (f : α → β)
    (good : β → Prop) :
    (A.map f).succProb good = A.succProb (fun x => good (f x)) := by
  unfold CoinAlgo.succProb
  congr 1
  apply Finset.sum_congr rfl
  intro c _
  exact CoinAlgo.indicator_map A f good c

theorem CoinAlgo.isMC_map {α β : Type*} (A : CoinAlgo α) (f : α → β)
    {good : β → Prop} {goodα : α → Prop}
    (h : A.IsMC goodα) (hf : ∀ x, goodα x → good (f x)) :
    (A.map f).IsMC good := by
  unfold CoinAlgo.IsMC at h ⊢
  rw [CoinAlgo.succProb_map]
  exact le_trans h (CoinAlgo.succProb_mono A hf)

def CoinAlgo.bind {α β : Type*} (A : CoinAlgo α) (g : α → Option β) : CoinAlgo β where
  Coin := A.Coin
  instFintype := A.instFintype
  instDecEq := A.instDecEq
  run c := (A.run c).bind g
  cost := A.cost

theorem CoinAlgo.bind_imp {α β : Type*} (A : CoinAlgo α) (g : α → Option β)
    {goodα : α → Prop} {goodβ : β → Prop}
    (hg : ∀ x, goodα x → ∃ y, g x = some y ∧ goodβ y) (c : A.Coin)
    (h : ∃ x, A.run c = some x ∧ goodα x) :
    ∃ y, (A.run c).bind g = some y ∧ goodβ y := by
  obtain ⟨x, hx, hgx⟩ := h
  obtain ⟨y, hy, hgy⟩ := hg x hgx
  exact ⟨y, by rw [hx]; exact hy, hgy⟩

theorem CoinAlgo.indicator_bind {α β : Type*} (A : CoinAlgo α) (g : α → Option β)
    {goodα : α → Prop} {goodβ : β → Prop}
    (hg : ∀ x, goodα x → ∃ y, g x = some y ∧ goodβ y) (c : A.Coin) :
    A.indicator goodα c ≤ (A.bind g).indicator goodβ c := by
  classical
  unfold CoinAlgo.indicator
  show (if ∃ x, A.run c = some x ∧ goodα x then (1 : ℝ) else 0)
      ≤ (if ∃ y, (A.run c).bind g = some y ∧ goodβ y then 1 else 0)
  by_cases hp : ∃ x, A.run c = some x ∧ goodα x
  · have hq := CoinAlgo.bind_imp A g hg c hp
    simp [hp, hq]
  · simp only [hp, if_false]
    split_ifs <;> norm_num

theorem CoinAlgo.isMC_bind {α β : Type*} (A : CoinAlgo α) (g : α → Option β)
    {goodα : α → Prop} {goodβ : β → Prop}
    (h : A.IsMC goodα) (hg : ∀ x, goodα x → ∃ y, g x = some y ∧ goodβ y) :
    (A.bind g).IsMC goodβ := by
  unfold CoinAlgo.IsMC at h ⊢
  refine le_trans h ?_
  unfold CoinAlgo.succProb
  apply div_le_div_of_nonneg_right _ (by positivity)
  exact Finset.sum_le_sum (fun c _ => CoinAlgo.indicator_bind A g hg c)

end Qatlib.Papers.ZetaCurves04.MainResults.Model
