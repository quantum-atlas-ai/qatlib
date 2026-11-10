/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.AmplitudeSearch.Amplification.NativeMinimumConstruction
import Qatlib.Concepts.AmplitudeSearch.Amplification.NativeMinimumConstructionDefs
import Qatlib.Concepts.AmplitudeSearch.Amplification.SearchStoppingDefs
set_option warningAsError false
set_option backward.isDefEq.respectTransparency false
open Qatlib.Concepts.LchsSimulation.StaticLchs Qatlib.Foundations.PureStateMath.Reflection
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.AmplitudeSearch.Amplification

set_option autoImplicit false

namespace Qatlib.Papers.FixedPtSearch14.FixedPoint

open Qatlib
open scoped ENNReal BigOperators Classical

theorem producer_round_law_eq (N : ℕ) :
    (producerWordLaw N).map (acceptThreshold N) = thresholdRoundLaw N := rfl

theorem thresholdScan_head_accepted {N : ℕ} {w : Fin (thresholdWords N)}
    {ws : List (Fin (thresholdWords N))} {i : Fin N}
    (h : acceptThreshold N w = some i) :
    thresholdScan N (w :: ws) = some (i, 0) := by
  simp [thresholdScan, h]

theorem thresholdScan_head_rejected {N : ℕ} {w : Fin (thresholdWords N)}
    {ws : List (Fin (thresholdWords N))}
    (h : acceptThreshold N w = none) :
    thresholdScan N (w :: ws) = (thresholdScan N ws).map (fun p => (p.1, p.2 + 1)) := by
  simp [thresholdScan, h]

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

theorem producer_draws_accepted {N r : ℕ} (i : Fin N) (n : Fin r) :
    producerDraws (ThresholdOutcome.accepted i n : ThresholdOutcome N r) = n.val + 1 := rfl

theorem producer_draws_failed {N r : ℕ} :
    producerDraws (ThresholdOutcome.failed : ThresholdOutcome N r) = r := rfl

theorem producer_draws_le_budget {N r : ℕ} (o : ThresholdOutcome N r) :
    producerDraws o ≤ r := by
  cases o with
  | accepted i n => exact Nat.succ_le_of_lt n.isLt
  | failed => exact Nat.le_refl r

theorem producer_draws_lt_frozen_constant {N r : ℕ} (o : ThresholdOutcome N r) :
    producerDraws o < r + 1 := by
  cases o with
  | accepted i n => exact Nat.succ_lt_succ n.isLt
  | failed => exact Nat.lt_succ_self r

theorem producer_spend_conservation {N r : ℕ} (o : ThresholdOutcome N r) :
    producerDraws o + producerRemaining o = r := by
  cases o with
  | accepted i n =>
    show n.val + 1 + (r - (n.val + 1)) = r
    omega
  | failed => show r + (r - r) = r; omega

theorem producer_remaining_pos_of_early {N r : ℕ} (i : Fin N) (n : Fin r)
    (h : n.val + 1 < r) :
    0 < producerRemaining (ThresholdOutcome.accepted i n : ThresholdOutcome N r) := by
  show 0 < r - (n.val + 1)
  omega

theorem producer_remaining_eq_zero_of_failed {N r : ℕ} :
    producerRemaining (ThresholdOutcome.failed : ThresholdOutcome N r) = 0 := by
  simp [producerRemaining, producerDraws]

theorem producer_costed_law_eq (N r : ℕ) :
    producerCostedLaw N r
      = (thresholdRunLaw N r).map (fun o => (o, thresholdWidth N * producerDraws o)) := rfl

theorem producer_charge_le_budget {N r : ℕ} (o : ThresholdOutcome N r) :
    thresholdWidth N * producerDraws o ≤ thresholdWidth N * r :=
  Nat.mul_le_mul_left _ (producer_draws_le_budget o)

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

theorem charged_spend_conservation {N : ℕ} {α : Type*} [LinearOrder α]
    (T : Fin N → α) (hN : 0 < N) (budget : ℕ) (current : Fin N)
    (x : Fin N × ℕ)
    (hx : x ∈ (minimumBudgetPMFWithInit T (initCharge N) hN budget current).support) :
    chargedSpend budget x + x.2 = budget := by
  have hcons := minimumBudgetPMFWithInit_conservation T (initCharge N) hN budget current x hx
  simpa [chargedSpend] using! hcons

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

theorem source_window_depth_shift (M : ℕ) (i : Fin M) :
    sourceWindowDepth M i = i.val + 1 := rfl

private theorem window_reindex (f : ℕ → ℝ) (M : ℕ) :
    (∑ j ∈ Finset.range M, f (j + 1)) = (∑ k ∈ Finset.range M, f k) + f M - f 0 := by
  induction M with
  | zero => simp
  | succ M ih =>
    rw [Finset.sum_range_succ, Finset.sum_range_succ, ih]
    ring

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

theorem source_window_avg_diff {I : Type} [Fintype I] [DecidableEq I]
    (A : Matrix I I ℂ) (hA : A ∈ Matrix.unitaryGroup I ℂ) (j₀ : I) (S : Finset I)
    (M : ℕ) (hM : 0 < M) :
    sourceWindowAvgSuccess A j₀ S M - shiftedWindowAvgSuccess A j₀ S M
      = (aaDepthMass A j₀ S M - aaDepthMass A j₀ S 0) / (M : ℝ) := by
  have h := source_window_success_diff A hA j₀ S M
  simp only [sourceWindowAvgSuccess, shiftedWindowAvgSuccess] at *
  field_simp
  linarith [h]

theorem source_window_actual_mass {I : Type} [Fintype I] [DecidableEq I]
    (A : Matrix I I ℂ) (hA : A ∈ Matrix.unitaryGroup I ℂ) (j₀ : I) (S : Finset I)
    (θ : ℝ) (k : ℕ)
    (hθ0 : 0 < θ) (hθ1 : θ < Real.pi / 2)
    (hprob : MeasureProb (preparedAAState A j₀) S = (Real.sin θ)^2) :
    aaDepthMass A j₀ S k = (Real.sin ((2 * (k : ℝ) + 1) * θ))^2 := by
  exact prepared_aa_born_success A j₀ S θ k hA hθ0 hθ1 hprob

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
