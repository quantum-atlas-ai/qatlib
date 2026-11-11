/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.AmplitudeSearch.Amplification.NativeMinimumConstruction
import Qatlib.Concepts.AmplitudeSearch.Amplification.NativeMinimumConstructionDefs
import Qatlib.Concepts.AmplitudeSearch.Amplification.SearchStoppingDefs

/-!
# Stopping and cost conservation for search

This module proves stopping and resource identities for threshold producers and budgeted minimum
search in the fixed-point-search development [YoderLowChuang2014]. Producer draws and charged
spend are related to their remaining budgets, with explicit early-stop and failed-run behavior.

It also compares amplitude-amplification windows indexed by depths `1, …, M` and `0, …, M - 1`
through an endpoint correction.

## Main statements

* `producer_spend_conservation`: Draws plus remaining budget equal the initial budget.
* `clause41_endpoint`: Budget conservation and spend bounds for minimum search.
* `source_window_avg_diff`: Exact correction between the two depth-window averages.

## References

* [Yoder et al., 2014][YoderLowChuang2014]
-/

set_option warningAsError false
set_option backward.isDefEq.respectTransparency false
open Qatlib.Concepts.LchsSimulation.StaticLchs Qatlib.Foundations.PureStateMath.Reflection
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.AmplitudeSearch.Amplification

set_option autoImplicit false

namespace Qatlib.Papers.FixedPtSearch14.FixedPoint

open Qatlib
open scoped ENNReal BigOperators Classical

/-- Mapping the producer word law through `acceptThreshold N` gives the threshold round law. -/
theorem producer_round_law_eq (N : ℕ) :
    (producerWordLaw N).map (acceptThreshold N) = thresholdRoundLaw N := rfl

/-- If the head word is accepted as `i`, the threshold scan returns `some (i, 0)`. -/
theorem thresholdScan_head_accepted {N : ℕ} {w : Fin (thresholdWords N)}
    {ws : List (Fin (thresholdWords N))} {i : Fin N}
    (h : acceptThreshold N w = some i) :
    thresholdScan N (w :: ws) = some (i, 0) := by
  simp [thresholdScan, h]

/-- If the head word is rejected, scanning the whole list increments the accepted-position count
returned by the tail scan. -/
theorem thresholdScan_head_rejected {N : ℕ} {w : Fin (thresholdWords N)}
    {ws : List (Fin (thresholdWords N))}
    (h : acceptThreshold N w = none) :
    thresholdScan N (w :: ws) = (thresholdScan N ws).map (fun p => (p.1, p.2 + 1)) := by
  simp [thresholdScan, h]

/-- A threshold scan returns `none` when every word in the list is rejected. -/
theorem thresholdScan_none_of_all_rejected {N : ℕ} :
    ∀ (ws : List (Fin (thresholdWords N))),
      (∀ w ∈ ws, acceptThreshold N w = none) → thresholdScan N ws = none := by
  intro ws
  induction ws with
  | nil => rintro _; simp [thresholdScan]
  | cons w ws ih =>
    intro hall
    have hw : acceptThreshold N w = none := hall w (by simp)
    have hws : ∀ x ∈ ws, acceptThreshold N x = none := fun x hx => hall x (by simp [hx])
    rw [thresholdScan_head_rejected hw]
    simp [ih hws]

/-- An outcome accepted at index `n` uses `n.val + 1` producer draws. -/
theorem producer_draws_accepted {N r : ℕ} (i : Fin N) (n : Fin r) :
    producerDraws (ThresholdOutcome.accepted i n : ThresholdOutcome N r) = n.val + 1 := rfl

/-- A failed producer run uses all `r` draws. -/
theorem producer_draws_failed {N r : ℕ} :
    producerDraws (ThresholdOutcome.failed : ThresholdOutcome N r) = r := rfl

/-- Every producer outcome uses at most its draw budget. -/
theorem producer_draws_le_budget {N r : ℕ} (o : ThresholdOutcome N r) :
    producerDraws o ≤ r := by
  cases o with
  | accepted i n => exact Nat.succ_le_of_lt n.isLt
  | failed => exact Nat.le_refl r

/-- Every producer outcome uses strictly fewer than `r + 1` draws. -/
theorem producer_draws_lt_frozen_constant {N r : ℕ} (o : ThresholdOutcome N r) :
    producerDraws o < r + 1 := by
  cases o with
  | accepted i n => exact Nat.succ_lt_succ n.isLt
  | failed => exact Nat.lt_succ_self r

/-- Producer draws and remaining draws sum to the initial budget `r`. -/
theorem producer_spend_conservation {N r : ℕ} (o : ThresholdOutcome N r) :
    producerDraws o + producerRemaining o = r := by
  cases o with
  | accepted i n =>
    show n.val + 1 + (r - (n.val + 1)) = r
    omega
  | failed => show r + (r - r) = r; omega

/-- Acceptance strictly before exhausting the draw budget leaves a positive remaining budget. -/
theorem producer_remaining_pos_of_early {N r : ℕ} (i : Fin N) (n : Fin r)
    (h : n.val + 1 < r) :
    0 < producerRemaining (ThresholdOutcome.accepted i n : ThresholdOutcome N r) := by
  show 0 < r - (n.val + 1)
  omega

/-- A failed producer outcome has zero remaining draws. -/
theorem producer_remaining_eq_zero_of_failed {N r : ℕ} :
    producerRemaining (ThresholdOutcome.failed : ThresholdOutcome N r) = 0 := by
  simp [producerRemaining, producerDraws]

/-- The costed producer law pairs each threshold outcome with its draw count multiplied by the
threshold word width. -/
theorem producer_costed_law_eq (N r : ℕ) :
    producerCostedLaw N r
      = (thresholdRunLaw N r).map (fun o => (o, thresholdWidth N * producerDraws o)) := rfl

/-- The width-weighted draw charge never exceeds the width-weighted budget. -/
theorem producer_charge_le_budget {N r : ℕ} (o : ThresholdOutcome N r) :
    thresholdWidth N * producerDraws o ≤ thresholdWidth N * r :=
  Nat.mul_le_mul_left _ (producer_draws_le_budget o)

/-- Bundles producer draw bounds, draw-budget conservation, and immediate acceptance of an
accepted head word. -/
theorem clause39_endpoint (N : ℕ) (r : ℕ) :
    (∀ o : ThresholdOutcome N r, producerDraws o ≤ r) ∧
    (∀ o : ThresholdOutcome N r, producerDraws o < r + 1) ∧
    (∀ o : ThresholdOutcome N r, producerDraws o + producerRemaining o = r) ∧
    (∀ w : Fin (thresholdWords N),
      ∀ (ws : List (Fin (thresholdWords N))) (i : Fin N),
        acceptThreshold N w = some i → thresholdScan N (w :: ws) = some (i, 0)) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro o; exact producer_draws_le_budget o
  · intro o; exact producer_draws_lt_frozen_constant o
  · intro o; exact producer_spend_conservation o
  · intro w ws i h; exact thresholdScan_head_accepted h

/-- For every supported budgeted minimum-search outcome, charged spend plus the remaining
balance equals the initial budget. -/
theorem charged_spend_conservation {N : ℕ} {α : Type*} [LinearOrder α]
    (T : Fin N → α) (hN : 0 < N) (budget : ℕ) (current : Fin N)
    (x : Fin N × ℕ)
    (hx : x ∈ (minimumBudgetPMFWithInit T (initCharge N) hN budget current).support) :
    chargedSpend budget x + x.2 = budget := by
  have hcons := minimumBudgetPMFWithInit_conservation T (initCharge N) hN budget current x hx
  simpa [chargedSpend] using! hcons

/-- For a singleton search space and positive budget, the outcome retains the entire budget and
has zero charged spend, which differs from its remaining balance. -/
theorem charged_spend_ne_balance_at_one {α : Type*} [LinearOrder α]
    (budget : ℕ) (hpos : 0 < budget) (current : Fin 1) :
    minimumBudgetPMFWithInit (fun _ => (0 : ℕ)) (initCharge 1) (by omega) budget current
      = PMF.pure (current, budget) ∧
    chargedSpend budget (current, budget) = 0 ∧
    chargedSpend budget (current, budget) ≠ (current, budget).2 := by
  refine ⟨?_, ?_, ?_⟩
  · simp [minimumBudgetPMFWithInit]
  · simp [chargedSpend]
  · simp [chargedSpend] at *
    omega

/-- For budgeted minimum search, every supported outcome conserves spend plus balance and has
spend at most the budget; the unchanged initial outcome has zero spend. -/
theorem clause41_endpoint {N : ℕ} {α : Type*} [LinearOrder α]
    (T : Fin N → α) (hN : 0 < N) (budget : ℕ) (current : Fin N) :
    (∀ x ∈ (minimumBudgetPMFWithInit T (initCharge N) hN budget current).support,
        chargedSpend budget x + x.2 = budget) ∧
    (chargedSpend budget (current, budget) = 0 ∨ budget = 0) ∧
    (∀ x ∈ (minimumBudgetPMFWithInit T (initCharge N) hN budget current).support,
        chargedSpend budget x ≤ budget) := by
  refine ⟨?_, ?_, ?_⟩
  · intro x hx; exact charged_spend_conservation T hN budget current x hx
  · by_cases hb : budget = 0
    · exact Or.inr hb
    · exact Or.inl (by simp [chargedSpend])
  · intro x hx
    have hx2 : 0 ≤ x.2 := by
      have := minimumBudgetPMFWithInit_remaining T (initCharge N) hN budget current x hx
      omega
    simp [chargedSpend]

/-- The source window at index `i` uses amplification depth `i.val + 1`. -/
theorem source_window_depth_shift (M : ℕ) (i : Fin M) :
    sourceWindowDepth M i = i.val + 1 := rfl

/-- Shifting a finite sum from indices `0, …, M - 1` to `1, …, M` adds `f M - f 0`. -/
private theorem window_reindex (f : ℕ → ℝ) (M : ℕ) :
    (∑ j ∈ Finset.range M, f (j + 1)) = (∑ k ∈ Finset.range M, f k) + f M - f 0 := by
  induction M with
  | zero => simp
  | succ M ih =>
    rw [Finset.sum_range_succ, Finset.sum_range_succ, ih]
    ring

/-- The difference between the two finite depth-window success sums is the depth-`M` success
mass minus the depth-zero success mass. -/
theorem source_window_success_diff {I : Type} [Fintype I] [DecidableEq I]
    (A : Matrix I I ℂ) (hA : A ∈ Matrix.unitaryGroup I ℂ) (j₀ : I) (S : Finset I)
    (M : ℕ) :
    (∑ i : Fin M, aaDepthMass A j₀ S (sourceWindowDepth M i))
        - (∑ i : Fin M, aaDepthMass A j₀ S i.val)
      = aaDepthMass A j₀ S M - aaDepthMass A j₀ S 0 := by
  have hsrc : (∑ i : Fin M, aaDepthMass A j₀ S (sourceWindowDepth M i))
      = ∑ j ∈ Finset.range M, aaDepthMass A j₀ S (j + 1) := by
    have hstep : (∑ i : Fin M, aaDepthMass A j₀ S (sourceWindowDepth M i))
        = ∑ i : Fin M, aaDepthMass A j₀ S ((i : ℕ) + 1) := by
      exact Finset.sum_congr rfl (fun i _ => by simp [sourceWindowDepth])
    rw [hstep]
    exact Fin.sum_univ_eq_sum_range (fun j : ℕ => aaDepthMass A j₀ S (j + 1)) M
  have hfroz : (∑ i : Fin M, aaDepthMass A j₀ S i.val)
      = ∑ k ∈ Finset.range M, aaDepthMass A j₀ S k := by
    exact Fin.sum_univ_eq_sum_range (fun k : ℕ => aaDepthMass A j₀ S k) M
  rw [hsrc, hfroz]
  have h := window_reindex (fun k : ℕ => aaDepthMass A j₀ S k) M
  linarith [h]

/-- For positive window size, the difference of the source and shifted-window average success
probabilities is the endpoint success-mass difference divided by `M`. -/
theorem source_window_avg_diff {I : Type} [Fintype I] [DecidableEq I]
    (A : Matrix I I ℂ) (hA : A ∈ Matrix.unitaryGroup I ℂ) (j₀ : I) (S : Finset I)
    (M : ℕ) (hM : 0 < M) :
    sourceWindowAvgSuccess A j₀ S M - shiftedWindowAvgSuccess A j₀ S M
      = (aaDepthMass A j₀ S M - aaDepthMass A j₀ S 0) / (M : ℝ) := by
  have h := source_window_success_diff A hA j₀ S M
  simp only [sourceWindowAvgSuccess, shiftedWindowAvgSuccess] at *
  field_simp
  linarith [h]

/-- For prepared marked mass `sin² θ` with `0 < θ < π/2`, the depth-`k` success mass is `sin²
((2k + 1)θ)`. -/
theorem source_window_actual_mass {I : Type} [Fintype I] [DecidableEq I]
    (A : Matrix I I ℂ) (hA : A ∈ Matrix.unitaryGroup I ℂ) (j₀ : I) (S : Finset I)
    (θ : ℝ) (k : ℕ)
    (hθ0 : 0 < θ) (hθ1 : θ < Real.pi / 2)
    (hprob : MeasureProb (preparedAAState A j₀) S = (Real.sin θ)^2) :
    aaDepthMass A j₀ S k = (Real.sin ((2 * (k : ℝ) + 1) * θ))^2 := by
  exact prepared_aa_born_success A j₀ S θ k hA hθ0 hθ1 hprob

/-- Bundles the source-window depth shift, the endpoint correction for its success sum, and the
exact sinusoidal success mass at every depth. -/
theorem clause43_endpoint {I : Type} [Fintype I] [DecidableEq I]
    (A : Matrix I I ℂ) (hA : A ∈ Matrix.unitaryGroup I ℂ) (j₀ : I) (S : Finset I)
    (M : ℕ) (θ : ℝ)
    (hθ0 : 0 < θ) (hθ1 : θ < Real.pi / 2)
    (hprob : MeasureProb (preparedAAState A j₀) S = (Real.sin θ)^2) :
    (∀ i : Fin M, sourceWindowDepth M i = i.val + 1) ∧
    (∑ i : Fin M, aaDepthMass A j₀ S (sourceWindowDepth M i))
        - (∑ i :Fin M, aaDepthMass A j₀ S i.val)
      = aaDepthMass A j₀ S M - aaDepthMass A j₀ S 0 ∧
    (∀ k : ℕ, aaDepthMass A j₀ S k = (Real.sin ((2 * (k : ℝ) + 1) * θ))^2) := by
  refine ⟨?_, ?_, ?_⟩
  · intro i; exact source_window_depth_shift M i
  · exact source_window_success_diff A hA j₀ S M
  · intro k; exact source_window_actual_mass A hA j₀ S θ k hθ0 hθ1 hprob

end Qatlib.Papers.FixedPtSearch14.FixedPoint
