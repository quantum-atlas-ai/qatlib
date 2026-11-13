/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.AmplitudeSearch.Amplification.NativeMinimumConstructionDefs

/-!
# Source deadlines and charged minimum-search costs

This module relates the source-model clock for minimum search to the integer charged-cost model.
`sourceDeadline` rounds `sourceTimeout` upward, `source_timeout_success` bounds the source-clock
mass attained by that timeout, and the cost decomposition theorems isolate initialization and
verification contributions beyond terminal search duration.

The calibration uses the minimum-finding setting of [DurrHoyer1996]. Further results show that a
supplied minimum index remains a successful interrupted-search threshold and identify the
randomness and charged-cost fields of the combined producer ledger.

## Main statements

* `sourceDeadlineReal_eq_source_formula` gives the source timeout formula, while
  `sourceDeadline_ge` and `sourceDeadline_lt` bound its integer ceiling.
- `source_timeout_success` gives a source-clock truncated mass between one half and one.
* `source_deadline_lt_charged_budget` separates the rounded source deadline from the charged
  budget for positive table size.
* `charged_cost_total_eq_source_total_plus'` decomposes total charged cost into terminal
  duration, initialization charges, and verification contributions.
* `charged_cost_total_gt_source_total` gives strict excess of charged cost for every nonempty
  trace list.

## References

- [Dürr and Høyer, 1996][DurrHoyer1996]. *A quantum algorithm for finding the minimum*. 1996.
-/

set_option backward.isDefEq.respectTransparency false

open Qatlib.Concepts.AmplitudeSearch.InterruptMin.PlannedRetry

open Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw
open Qatlib.Concepts.AmplitudeSearch.Amplification.Experiment
open Qatlib.Concepts.AmplitudeSearch.Amplification.RankedCallLaw
open Qatlib.Concepts.AmplitudeSearch.Amplification.SortedRankedTable
open Qatlib.Concepts.AmplitudeSearch.InterruptMin.CostedLaw

open Qatlib.Concepts.LinearLearning.ConcisePipeline
open Qatlib.Concepts.AmplitudeSearch.InterruptMin

set_option autoImplicit false

open Qatlib
open Qatlib
open Qatlib.Concepts.AmplitudeSearch.Amplification
open Qatlib
open Qatlib.Concepts.AmplitudeSearch.InterruptMin.AQuantumAlgorithmForFindingTheMinimum1999
open Qatlib
open Qatlib.Concepts.SearchStopping.GroverSuccess
open Qatlib.Concepts.SearchStopping.UnknownCount
open Qatlib
open scoped ENNReal BigOperators Classical

namespace Qatlib.Concepts.AmplitudeSearch.Amplification

/-- The real probability of an event under a finite PMF, expressed as a finite sum of point
masses times its indicator. -/
noncomputable def realEvent {α : Type*} [Fintype α] (p : PMF α) (E : α → Prop) : ℝ :=
  ∑ a, (p a).toReal * (if E a then 1 else 0)

/-- The extended nonnegative expectation of an event indicator equals `ENNReal.ofReal` of its
finite real event probability. -/
theorem expectation_indicator {α : Type*} [Fintype α] (p : PMF α) (E : α → Prop) :
    Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectation p (fun b => if E b then (1 : ℝ≥0∞) else 0) =
      ENNReal.ofReal (realEvent p E) := by
  unfold realEvent
  have hfun : (fun b => if E b then (1 : ℝ≥0∞) else 0) =
      (fun b => ENNReal.ofReal (if E b then (1 : ℝ) else 0)) := by
    funext b
    by_cases hb : E b <;> simp [hb]
  rw [hfun]
  exact Qatlib.Concepts.AmplitudeSearch.InterruptMin.CostedLaw.expectation_ofReal_fintype p (fun b => if E b then (1 : ℝ) else 0)
    (by intro b; by_cases hb : E b <;> simp [hb])

/-- The finite real event probability equals the real conversion of the corresponding extended
nonnegative event probability. -/
theorem realEvent_eq_event {α : Type*} [Fintype α] (p : PMF α) (E : α → Prop) :
    realEvent p E = (Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.event p E).toReal := by
  unfold Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.event
  rw [expectation_indicator]
  exact (ENNReal.toReal_ofReal (by
    apply Finset.sum_nonneg
    intro a _
    by_cases ha : E a <;> simp [ha, ENNReal.toReal_nonneg])).symm

/-- The real-valued source-model deadline, defined as `sourceTimeout N`. -/
noncomputable def sourceDeadlineReal (N : ℕ) : ℝ := sourceTimeout N

/-- The natural-number ceiling of the source-model timeout. -/
noncomputable def sourceDeadline (N : ℕ) : ℕ := Nat.ceil (sourceTimeout N)

/-- The real source deadline is `(45 / 2) * sqrt N + (7 / 5) * (binaryLog N) ^ 2`. -/
theorem sourceDeadlineReal_eq_source_formula (N : ℕ) :
    sourceDeadlineReal N = (45 / 2 : ℝ) * Real.sqrt N + (7 / 5 : ℝ) * (binaryLog N) ^ 2 := rfl

/-- The integer source deadline, viewed as a real number, is at least the source timeout. -/
theorem sourceDeadline_ge (N : ℕ) : sourceTimeout N ≤ (sourceDeadline N : ℝ) := by
  simpa [sourceDeadline] using! (Nat.le_ceil (sourceTimeout N))

/-- The integer source deadline, viewed as a real number, is strictly below the source timeout
plus one. -/
theorem sourceDeadline_lt (N : ℕ) : (sourceDeadline N : ℝ) < sourceTimeout N + 1 := by
  have hnonneg : (0 : ℝ) ≤ sourceTimeout N := by
    unfold sourceTimeout
    have h1 : (0 : ℝ) ≤ Real.sqrt N := Real.sqrt_nonneg _
    have h2 : (0 : ℝ) ≤ binaryLog N := by
      unfold binaryLog
      by_cases hN0 : N = 0
      · subst hN0
        simp [Real.log_zero]
      · have : (0 : ℝ) ≤ Real.log N := Real.log_nonneg (by exact_mod_cast Nat.pos_of_ne_zero hN0)
        positivity
    nlinarith [sq_nonneg (binaryLog N)]
  have h := Nat.ceil_lt_add_one hnonneg
  simpa [sourceDeadline] using! h

/-- For positive table size, the source timeout is at least `45 / 2`. -/
theorem sourceDeadlineReal_ge (N : ℕ) (hN : 0 < N) : (45 / 2 : ℝ) ≤ sourceTimeout N := by
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hsqrt : (1 : ℝ) ≤ Real.sqrt N := by
    have hpos : 0 ≤ Real.sqrt N := Real.sqrt_nonneg _
    have hsq : (Real.sqrt N) ^ 2 = N := Real.sq_sqrt (by exact_mod_cast hN.le)
    nlinarith
  have hlog : (0 : ℝ) ≤ binaryLog N := by
    unfold binaryLog
    have : (0 : ℝ) ≤ Real.log N := Real.log_nonneg (by exact_mod_cast hN)
    positivity
  unfold sourceTimeout
  nlinarith [sq_nonneg (binaryLog N)]

/-- The source timeout is positive whenever the table size is positive. -/
theorem sourceDeadlineReal_pos (N : ℕ) (hN : 0 < N) : 0 < sourceTimeout N := by
  have h := sourceDeadlineReal_ge N hN
  linarith

/-- For a nonempty table, the source BBHT initial mass restricted to traces whose run clock is
at most `sourceTimeout N` has a real sum between one half and one. -/
theorem source_timeout_success {N : ℕ} {α : Type*} [LinearOrder α]
    (T : Fin N → α) (hN : 0 < N) :
    ∃ p : ℝ, HasSum (fun x : Fin N × List (SearchTrace N) =>
        if (sourceBBHTLaw (SortedRankedTable.ofTable T).indexOfRank hN).runClock x.2
            ≤ sourceTimeout N
        then (sourceBBHTLaw (SortedRankedTable.ofTable T).indexOfRank hN).initialMass
            (SortedRankedTable.ofTable T).skip x
        else 0) p ∧
      (1 / 2 : ℝ) ≤ p ∧ p ≤ 1 := by
  let ranked := SortedRankedTable.ofTable T
  let law := sourceBBHTLaw ranked.indexOfRank hN
  have ht : (0 : ℝ) < sourceTimeout N := sourceDeadlineReal_pos N hN
  obtain ⟨q, hq, _, hqb⟩ := bbht_source_attainment_moment ranked hN
  obtain ⟨p, hp, hgood, hp1⟩ := amplification_clock_mass
    (law.initialMass ranked.skip) (fun x : Fin N × List (SearchTrace N) => law.runClock x.2)
    (law.initialMass_normalized ranked.skip hN).1
    (law.initialMass_normalized ranked.skip hN).2
    (fun x => law.runClock_nonneg x.2) q (sourceTimeout N) hq ht
  have hratio : q / sourceTimeout N ≤ 1 / 2 := by
    rw [div_le_iff₀ ht]
    have hq' : q ≤ sourceMeanBudget N := hqb
    rw [sourceTimeout_eq_twice]
    nlinarith [sourceMeanBudget_pos N hN]
  refine ⟨p, hp, ?_, hp1⟩
  linarith

/-- For positive table size, the rounded source deadline is strictly smaller than the charged
budget. -/
theorem source_deadline_lt_charged_budget (N : ℕ) (hN : 0 < N) :
    sourceDeadline N < chargedBudget N := by
  have hge : (45 / 2 : ℝ) ≤ sourceTimeout N := sourceDeadlineReal_ge N hN
  have h1 : sourceTimeout N ≤ (sourceDeadline N : ℝ) := sourceDeadline_ge N
  have h2 : (sourceDeadline N : ℝ) < sourceTimeout N + 1 := sourceDeadline_lt N
  have h3 : sourceTimeout N + 1 ≤ 4 * sourceTimeout N := by linarith
  have h4 : (4 * sourceTimeout N : ℝ) ≤ (chargedBudget N : ℝ) := by
    rw [chargedBudget_eq_four_sourceTimeout]
    exact_mod_cast Nat.le_ceil _
  have hlt : (sourceDeadline N : ℝ) < (chargedBudget N : ℝ) := by linarith
  exact_mod_cast hlt

/-- Each charged call cost strictly exceeds its terminal search cost plus `binaryLog N`. -/
theorem charged_call_cost_gt_source_duration (N : ℕ) (x : SearchTrace N) :
    (TerminalCost (ExponentialSizes N) x : ℝ) + binaryLog N < (chargedCallCost N x : ℝ) := by
  have hinit : binaryLog N ≤ (initCharge N : ℝ) := by
    simpa using! (Nat.le_ceil (binaryLog N))
  have hcast : (chargedCallCost N x : ℝ) =
      (initCharge N : ℝ) + (TerminalCost (ExponentialSizes N) x : ℝ) + (x.1 + 1) := by
    simp only [chargedCallCost, TerminalBooleanQueries]
    push_cast
    ring
  rw [hcast]
  have hq : (0 : ℝ) < x.1 + 1 := by positivity
  linarith

/-- The sum of the real-valued terminal search costs over a list of search traces. -/
noncomputable def sourceDurationTotal (N : ℕ) (xs : List (SearchTrace N)) : ℝ :=
  (xs.map (fun x => (TerminalCost (ExponentialSizes N) x : ℝ))).sum

/-- The sum of the natural-number charged call costs over a list of search traces. -/
noncomputable def chargedCostTotal (N : ℕ) (xs : List (SearchTrace N)) : ℕ :=
  (xs.map (chargedCallCost N)).sum

/-- A charged call cost, viewed as a real number, is its terminal search duration plus
`initCharge N` and the verification contribution `x.1 + 1`. -/
theorem charged_call_cost_eq_source_duration_plus (N : ℕ) (x : SearchTrace N) :
    (chargedCallCost N x : ℝ)
      = (TerminalCost (ExponentialSizes N) x : ℝ) + (initCharge N : ℝ)
        + ((x.1 + 1 : ℕ) : ℝ) := by
  simp only [chargedCallCost, TerminalBooleanQueries]
  push_cast
  ring

/-- The sum of charged call costs decomposes into the sum of terminal search durations, one
initialization charge per trace, and the sum of verification contributions. -/
theorem charged_cost_total_eq_source_total_plus (N : ℕ) (xs : List (SearchTrace N)) :
    ((xs.map (chargedCallCost N)).sum : ℝ)
      = ((xs.map (fun x : SearchTrace N => (TerminalCost (ExponentialSizes N) x : ℝ))).sum)
        + (xs.length : ℝ) * (initCharge N : ℝ)
        + (xs.map (fun x : SearchTrace N => ((x.1 + 1 : ℕ) : ℝ))).sum := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
      have hcast := charged_call_cost_eq_source_duration_plus N x
      simp only [List.map_cons, List.sum_cons, List.length_cons, Nat.cast_add, Nat.cast_one]
      rw [ih, hcast]
      push_cast
      ring

/-- The total charged cost equals `sourceDurationTotal` plus the trace count times `initCharge
N` and the sum of the verification contributions. -/
theorem charged_cost_total_eq_source_total_plus' (N : ℕ) (xs : List (SearchTrace N)) :
    (chargedCostTotal N xs : ℝ) = sourceDurationTotal N xs
      + (xs.length : ℝ) * (initCharge N : ℝ)
      + (xs.map (fun x : SearchTrace N => ((x.1 + 1 : ℕ) : ℝ))).sum := by
  simpa [chargedCostTotal, sourceDurationTotal] using!
    charged_cost_total_eq_source_total_plus N xs

/-- The natural-number sum of the verification contributions `x.1 + 1` is at least the number of
traces. -/
theorem verification_sum_ge_length_nat (N : ℕ) (xs : List (SearchTrace N)) :
    (xs.map (fun x : SearchTrace N => x.1 + 1)).sum ≥ xs.length := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
      simp only [List.map_cons, List.sum_cons, List.length_cons]
      omega

/-- Summing the real conversions of the verification contributions agrees with converting their
natural-number sum to a real number. -/
theorem verification_sum_cast (N : ℕ) (xs : List (SearchTrace N)) :
    (xs.map (fun x : SearchTrace N => ((x.1 + 1 : ℕ) : ℝ))).sum
      = ((xs.map (fun x : SearchTrace N => x.1 + 1)).sum : ℝ) := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
      simp only [List.map_cons, List.sum_cons]
      rw [ih]
      push_cast
      ring

/-- The real sum of the verification contributions is at least the trace-list length. -/
theorem verification_sum_ge_length (N : ℕ) (xs : List (SearchTrace N)) :
    (xs.map (fun x : SearchTrace N => ((x.1 + 1 : ℕ) : ℝ))).sum ≥ (xs.length : ℝ) := by
  rw [verification_sum_cast]
  have h := verification_sum_ge_length_nat N xs
  exact_mod_cast h

/-- For a nonempty trace list, total charged cost strictly exceeds total terminal search
duration. -/
theorem charged_cost_total_gt_source_total (N : ℕ) (xs : List (SearchTrace N)) (hne : xs ≠ []) :
    (chargedCostTotal N xs : ℝ) > sourceDurationTotal N xs := by
  rw [charged_cost_total_eq_source_total_plus']
  have hlen : 0 < xs.length := by
    cases xs with
    | nil => exact absurd rfl hne
    | cons a t => simp
  have hverif := verification_sum_ge_length N xs
  have hinit : (0 : ℝ) ≤ (initCharge N : ℝ) := by exact_mod_cast (Nat.zero_le _)
  have hlen' : (0 : ℝ) < (xs.length : ℝ) := by exact_mod_cast hlen
  have hprod : (0 : ℝ) ≤ (xs.length : ℝ) * (initCharge N : ℝ) := by
    have h := mul_nonneg (le_of_lt hlen') hinit
    simpa using! h
  have hsum : (0 : ℝ) < (xs.map (fun x : SearchTrace N => ((x.1 + 1 : ℕ) : ℝ))).sum := by
    have h1 := verification_sum_ge_length N xs
    linarith
  linarith

/-- If a nonempty trace list has total terminal search duration equal to the source timeout, its
charged cost strictly exceeds that timeout. -/
theorem source_deadline_exhausted_not_charged (N : ℕ) (hN : 0 < N)
    (xs : List (SearchTrace N)) (hne : xs ≠ [])
    (hexhaust : sourceDurationTotal N xs = sourceTimeout N) :
    (chargedCostTotal N xs : ℝ) > sourceTimeout N := by
  have hgt := charged_cost_total_gt_source_total N xs hne
  rwa [hexhaust] at hgt

/-- The finite set of indices whose table values are no larger than the value at any other
index. -/
def minimumIndices {N : ℕ} {α : Type*} [LinearOrder α] (T : Fin N → α) : Finset (Fin N) :=
  Finset.univ.filter (fun i => ∀ j, T i ≤ T j)

/-- Starting interrupted minimum search at a global minimum gives success probability one for
every budget, with initialization charge `initCharge N`. -/
theorem producer_threshold_feeds_interrupted {N : ℕ} {α : Type*} [LinearOrder α]
    (T : Fin N → α) (hN : 0 < N) (budget : ℕ) (i : Fin N)
    (hmin : ∀ j, T i ≤ T j) :
    interruptedMinimumSuccessWithInit T (initCharge N) budget i = 1 :=
  interrupted_success_of_minimum T (initCharge N) hN budget i hmin

/-- Every supported output of interrupted minimum search started at a global minimum retains
that same index. -/
theorem producer_threshold_kept_by_interrupted {N : ℕ} {α : Type*} [LinearOrder α]
    (T : Fin N → α) (hN : 0 < N) (budget : ℕ) (i : Fin N)
    (hmin : ∀ j, T i ≤ T j) (x : Fin N × ℕ)
    (hx : x ∈ (interruptedMinimumPMFWithInit T (initCharge N) hN budget i).support) :
    x.1 = i :=
  interrupted_minimum_output T (initCharge N) hN budget i hmin x hx

/-- The combined ledger constructed with a trace list's charged cost records exactly
`chargedCostTotal N xs` in its charged-cost field. -/
theorem unified_ledger_carries_frozen_charged_cost (N r : ℕ) (draws rejections : ℕ)
    (h : rejections ≤ draws) (xs : List (SearchTrace N)) :
    (PublicProgramLedger.ofRun N r draws rejections h (chargedCostTotal N xs)).chargedCost
      = chargedCostTotal N xs := rfl

/-- The combined ledger's total randomness quantity is `thresholdWidth N * draws` plus the
producer workspace `thresholdWidth N + thresholdWidth (rejections + 1)`. -/
theorem unified_ledger_randomness_is_producer (N r : ℕ) (draws rejections : ℕ)
    (h : rejections ≤ draws) (chargedCost : ℕ) :
    (PublicProgramLedger.ofRun N r draws rejections h chargedCost).totalRandomness
      = thresholdWidth N * draws
        + (thresholdWidth N + thresholdWidth (rejections + 1)) := by
  simp [PublicProgramLedger.totalRandomness, PublicProgramLedger.ofRun,
    ThresholdLedger.totalBits, ThresholdLedger.ofRun]

/-- A threshold ledger built from run counts records total bits equal to `thresholdWidth N *
draws`. -/
theorem ledger_total_bits (N r : ℕ) (draws rejections : ℕ) (h : rejections ≤ draws) :
    (ThresholdLedger.ofRun N r draws rejections h).totalBits
      = thresholdWidth N * draws := by
  simp [ThresholdLedger.totalBits, ThresholdLedger.ofRun]

/-- Scanning a singleton list containing an accepted word returns its index with zero preceding
rejections. -/
theorem scan_first_accepted (N : ℕ) (w : Fin (thresholdWords N)) (i : Fin N)
    (h : acceptThreshold N w = some i) :
    thresholdScan N (w :: []) = some (i, 0) := by
  simp [thresholdScan, h]
end Qatlib.Concepts.AmplitudeSearch.Amplification
