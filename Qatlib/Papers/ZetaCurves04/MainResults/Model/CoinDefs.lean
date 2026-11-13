/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.ZetaCurves04.MainResults.Model.CurveZetaDefs

/-!
# Finite-coin algorithms and correctness-preserving maps

The record `CoinAlgo` models an optional output from a finite coin space with a recorded cost.
Its success probability averages a correctness indicator over that space; monotonicity,
deterministic mapping, and optional postprocessing preserve the three-quarter Monte Carlo
correctness threshold when the supplied predicates are respected.

The stored cost alone is unverified. `CoinImplementation` relates runs and costs
to supplied primitive-step semantics. The legacy `map` and `bind` are semantic
maps only and do not charge postprocessing; `mapCosted` and `bindCosted` add an
explicit postprocessing budget. Proving that budget bounds an implementation
remains a separate obligation.

This development forms part of the formalization of [Kedlaya2006].

## Main statements

* `CoinAlgo`: An algorithm record with a finite decidable coin space, an optional output for
  each coin, and a natural cost.
* `CoinAlgo.isMC_map`: A deterministic map sending good outputs to good outputs preserves the
  Monte Carlo correctness threshold.
* `CoinAlgo.isMC_bind`: Optional postprocessing that succeeds correctly on every good input
  preserves the Monte Carlo correctness threshold.

## References

* [Kedlaya, 2006][Kedlaya2006]
-/

set_option autoImplicit false
noncomputable section

open scoped BigOperators
open Finset

namespace Qatlib.Papers.ZetaCurves04.MainResults.Model

/-- An algorithm record with a finite decidable coin space, an optional output for each coin,
and a natural cost. -/
structure CoinAlgo (α : Type*) where

  Coin : Type*

  instFintype : Fintype Coin

  instDecEq : DecidableEq Coin

  run : Coin → Option α

  cost : ℕ

attribute [instance] CoinAlgo.instFintype CoinAlgo.instDecEq

/-- Execution contract relative to a fixed primitive instruction semantics.
Initialization and decoding are supplied by the machine model; their costs must
be included in that model when interpreting a physical runtime claim. -/
structure CoinImplementation {α : Type*} (A : CoinAlgo α)
    (State Step : Type*) (initial : A.Coin → State)
    (step : State → Step → State) (decode : State → Option α) where
  program : List Step
  run_eq : ∀ c, A.run c = decode (program.foldl step (initial c))
  cost_eq : A.cost = program.length

/-- Supplied implementation of optional postprocessing. Each instruction is one
charged primitive call; physical costs of initialization, decoding and primitives
belong to the external machine model. No such implementation is constructed here. -/
structure PostprocessingContract {α β : Type*} (f : α → Option β) (cost : ℕ) where
  State : Type
  Step : Type
  initial : α → State
  step : State → Step → State
  decode : State → Option β
  program : List Step
  output_eq : ∀ x, f x = decode (program.foldl step (initial x))
  cost_eq : cost = program.length

/-- Fixed primitive machine supplied by an implementation model. A program cannot
replace initialization or decoding. Each executed instruction costs one primitive
call; physical initialization, decoding and instruction costs are external. -/
structure PrimitiveMachine (Input Output : Type) where
  Coin : Type
  instFintype : Fintype Coin
  instDecEq : DecidableEq Coin
  State : Type
  Step : Type
  initial : Input → Coin → State
  step : State → Step → State
  decode : State → Option Output

/-- Run a supplied program with cost equal to its executed primitive-call count. -/
def PrimitiveMachine.algorithm {Input Output : Type} (M : PrimitiveMachine Input Output)
    (input : Input) (program : List M.Step) : CoinAlgo Output where
  Coin := M.Coin
  instFintype := M.instFintype
  instDecEq := M.instDecEq
  run c := M.decode (program.foldl M.step (M.initial input c))
  cost := program.length

/-- The real indicator that the selected coin produces an output satisfying `good`. -/
noncomputable def CoinAlgo.indicator {α : Type*} (A : CoinAlgo α) (good : α → Prop)
    (c : A.Coin) : ℝ := by
  classical
  exact if ∃ x, A.run c = some x ∧ good x then 1 else 0

/-- The sum of the correctness indicators divided by the cardinality of the coin space. -/
noncomputable def CoinAlgo.succProb {α : Type*} (A : CoinAlgo α) (good : α → Prop) : ℝ :=
  (∑ c : A.Coin, A.indicator good c) / (Fintype.card A.Coin : ℝ)

/-- The probability of an output satisfying `good` is at least `3 / 4`. -/
def CoinAlgo.IsMC {α : Type*} (A : CoinAlgo α) (good : α → Prop) : Prop :=
  (3 : ℝ) / 4 ≤ A.succProb good

/-- Weakening the output predicate can only increase its correctness indicator at a fixed coin. -/
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

/-- Weakening the output predicate can only increase its success probability. -/
theorem CoinAlgo.succProb_mono {α : Type*} (A : CoinAlgo α)
    {good good' : α → Prop} (h : ∀ x, good x → good' x) :
    A.succProb good ≤ A.succProb good' := by
  unfold CoinAlgo.succProb
  apply div_le_div_of_nonneg_right _ (by positivity)
  exact Finset.sum_le_sum (fun c _ => CoinAlgo.indicator_mono A h c)

/-- Apply a deterministic function to each successful output, retaining the coin space and
recorded cost. -/
def CoinAlgo.map {α β : Type*} (A : CoinAlgo α) (f : α → β) : CoinAlgo β where
  Coin := A.Coin
  instFintype := A.instFintype
  instDecEq := A.instDecEq
  run c := (A.run c).map f
  cost := A.cost

/-- A mapped run produces a good output exactly when the original run produces an output whose
image is good. -/
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

/-- The correctness indicator after mapping is the original indicator for the predicate composed
with the map. -/
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

/-- The success probability after mapping equals the original success probability for the
predicate composed with the map. -/
theorem CoinAlgo.succProb_map {α β : Type*} (A : CoinAlgo α) (f : α → β)
    (good : β → Prop) :
    (A.map f).succProb good = A.succProb (fun x => good (f x)) := by
  unfold CoinAlgo.succProb
  congr 1
  apply Finset.sum_congr rfl
  intro c _
  exact CoinAlgo.indicator_map A f good c

/-- A deterministic map sending good outputs to good outputs preserves the Monte Carlo
correctness threshold. -/
theorem CoinAlgo.isMC_map {α β : Type*} (A : CoinAlgo α) (f : α → β)
    {good : β → Prop} {goodα : α → Prop}
    (h : A.IsMC goodα) (hf : ∀ x, goodα x → good (f x)) :
    (A.map f).IsMC good := by
  unfold CoinAlgo.IsMC at h ⊢
  rw [CoinAlgo.succProb_map]
  exact le_trans h (CoinAlgo.succProb_mono A hf)

/-- Apply an optional postprocessing function to each successful output, retaining the coin
space and recorded cost. -/
def CoinAlgo.bind {α β : Type*} (A : CoinAlgo α) (g : α → Option β) : CoinAlgo β where
  Coin := A.Coin
  instFintype := A.instFintype
  instDecEq := A.instDecEq
  run c := (A.run c).bind g
  cost := A.cost

/-- Semantic mapping with an explicit additional cost budget. Faithfulness of
the budget to reconstruction is an implementation hypothesis, not proved here. -/
def CoinAlgo.mapCosted {α β : Type*} (A : CoinAlgo α) (f : α → β)
    (postCost : ℕ) : CoinAlgo β :=
  { A.map f with cost := A.cost + postCost }

/-- Optional postprocessing with an explicit additional implementation budget. -/
def CoinAlgo.bindCosted {α β : Type*} (A : CoinAlgo α) (f : α → Option β)
    (postCost : ℕ) : CoinAlgo β :=
  { A.bind f with cost := A.cost + postCost }

/-- If postprocessing succeeds with a good output on every good input, a good original run
yields a good postprocessed run. -/
theorem CoinAlgo.bind_imp {α β : Type*} (A : CoinAlgo α) (g : α → Option β)
    {goodα : α → Prop} {goodβ : β → Prop}
    (hg : ∀ x, goodα x → ∃ y, g x = some y ∧ goodβ y) (c : A.Coin)
    (h : ∃ x, A.run c = some x ∧ goodα x) :
    ∃ y, (A.run c).bind g = some y ∧ goodβ y := by
  obtain ⟨x, hx, hgx⟩ := h
  obtain ⟨y, hy, hgy⟩ := hg x hgx
  exact ⟨y, by rw [hx]; exact hy, hgy⟩

/-- Postprocessing that succeeds correctly on every good input does not decrease the correctness
indicator. -/
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

/-- Optional postprocessing that succeeds correctly on every good input preserves the Monte
Carlo correctness threshold. See [Kedlaya2006]. -/
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
