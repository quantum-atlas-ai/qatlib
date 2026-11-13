/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.AmplitudeSearch.InterruptMin.ClockZeroRetry
import Qatlib.Concepts.AmplitudeSearch.InterruptMin.ClockCompleteReward
import Qatlib.Concepts.AmplitudeSearch.InterruptMin.ClockOuter
import Qatlib.Concepts.AEMeanReadout.LocalAEBackend.SearchStopping
import Qatlib.Concepts.AmplitudeSearch.Amplification.ClockedPrefix
import Qatlib.Concepts.AmplitudeSearch.Amplification.MinimumBudgetCore

/-!
# A probability law for clocked minimum search

This module constructs `sourceCallPMF` and `sourceMinimumPMF` for search calls and minimum
finding with source-clock cutoffs. Matching evaluators compute extended nonnegative
expectations, and completion rewards are bounded by the resulting minimum events.

The final bound `source_timeout_half` gives success probability at least one half at
`sourceTimeout`, connecting the executable probability law to the minimum-search analysis of
[DurrHoyer1996].

## Main statements

* `sourceMinimumEval_eq_expectation`: The minimum-search evaluator equals expectation under
  `sourceMinimumPMF`.
* `source_timeout_half`: At `sourceTimeout N`, the clocked minimum-search law succeeds with
  probability at least one half, as in the minimum-finding guarantee of [DurrHoyer1996].
* `frontier1`: Combines the one-half success bound at `sourceTimeout N` with the expectation
  representation of the uniformly initialized evaluator.

## References

* [Dürr and Høyer, 1996][DurrHoyer1996]
* [Boyer et al., 1998][BoyerEtAl1998]
-/

set_option backward.isDefEq.respectTransparency false
open Qatlib.Concepts.AEMeanReadout.LocalAEBackend
open Qatlib.Concepts.SearchStopping.UnknownCount
open Qatlib.Concepts.AmplitudeSearch.Amplification
open Qatlib.Concepts.AmplitudeSearch.Amplification.Experiment
open Qatlib.Concepts.AmplitudeSearch.Amplification.RankedCallLaw
open Qatlib.Concepts.AmplitudeSearch.Amplification.SortedRankedTable
open Qatlib.Concepts.AmplitudeSearch.InterruptMin

set_option autoImplicit false
set_option maxHeartbeats 1500000
noncomputable section
namespace Qatlib.Concepts.AmplitudeSearch.InterruptMin
open Qatlib
open scoped Classical BigOperators ENNReal

/-- A source escape token with no successful output has a strictly positive iteration count. -/
theorem token_none_pos (N : ℕ) (hN : 1 < N) (stage : ℕ) (x : SourceToken N hN stage)
    (ho : x.2.val.2 = none) : 0 < x.2.val.1.val := by
  by_contra hn
  have hz : x.2.val.1.val = 0 := by omega
  apply x.2.property
  exact Prod.ext (Fin.ext hz) ho

/-- A search-call result consisting of an observed index and an optional remaining budget. -/
abbrev CallResult (N : ℕ) := Fin N × Option ℕ

/-- The probability law of a source-clock search call, returning a remaining budget on
completion and `none` on interruption. -/
def sourceCallPMF (N : ℕ) (hN : 1 < N) (A : Finset (Fin N))
    (stage budget : ℕ) : PMF (CallResult N) :=
  (sourceEscapePMF N hN A stage).bind fun x =>
    if hc : x.2.val.1.val < budget then
      match ho : x.2.val.2 with
      | some i => PMF.pure (i,some (budget-x.2.val.1.val))
      | none =>
        have hj := token_none_pos N hN stage x ho
        sourceCallPMF N hN A (advance stage x.1+1) (budget-x.2.val.1.val)
    else
      (partialObsPMF (by simpa using! (show 0 < N by omega)) A x.2.val.1.val budget).bind
        fun i => PMF.pure (i,none)
termination_by budget

/-- The extended nonnegative expectation of a payoff under a probability mass function. -/
def expectation {S : Type} (p : PMF S) (f : S → ℝ≥0∞) : ℝ≥0∞ := ∑' s, p s * f s

/-- The recursive payoff evaluator for a source-clock search call. -/
def sourceCallEval (N : ℕ) (hN : 1 < N) (A : Finset (Fin N))
    (stage budget : ℕ) (payoff : CallResult N → ℝ≥0∞) : ℝ≥0∞ :=
  ∑' x : SourceToken N hN stage, sourceEscapePMF N hN A stage x *
    (if hc : x.2.val.1.val < budget then
      match ho : x.2.val.2 with
      | some i => payoff (i,some (budget-x.2.val.1.val))
      | none =>
        have hj := token_none_pos N hN stage x ho
        sourceCallEval N hN A (advance stage x.1+1) (budget-x.2.val.1.val) payoff
    else
      ∑' i : Fin N, partialObsPMF (by simpa using! (show 0 < N by omega))
        A x.2.val.1.val budget i * payoff (i,none))
termination_by budget

/-- Expectation under a bound probability law equals the expectation of the conditional
expectations. -/
theorem expectation_bind {S T : Type} (p : PMF S) (f : S → PMF T) (g : T → ℝ≥0∞) :
    expectation (p.bind f) g = expectation p (fun s => expectation (f s) g) := by
  unfold expectation
  simp only [PMF.bind_apply]
  simp_rw [← ENNReal.tsum_mul_right]
  rw [ENNReal.tsum_comm]
  simp_rw [mul_assoc,ENNReal.tsum_mul_left]

/-- Expectation under a pure probability law is evaluation at its point mass. -/
theorem expectation_pure {S : Type} (s : S) (f : S → ℝ≥0∞) :
    expectation (PMF.pure s) f = f s := by
  simp [expectation,PMF.pure_apply]

/-- The source-call evaluator equals expectation under `sourceCallPMF`. -/
theorem sourceCallEval_eq_expectation (N : ℕ) (hN : 1 < N) (A : Finset (Fin N))
    (stage budget : ℕ) (payoff : CallResult N → ℝ≥0∞) :
    sourceCallEval N hN A stage budget payoff = expectation (sourceCallPMF N hN A stage budget) payoff := by
  induction budget using Nat.strong_induction_on generalizing stage payoff with
  | h b ih =>
    rw [sourceCallEval,sourceCallPMF,expectation_bind,expectation]
    apply tsum_congr
    intro x
    congr 1
    split_ifs with hc
    · split
      next i _ => simp only [expectation_pure]
      next ho =>
        have hj := token_none_pos N hN stage x ho
        exact ih (b-x.2.val.1.val) (Nat.sub_lt (by omega) hj) _ payoff
    · rw [expectation_bind]
      change _ = ∑' i : Fin N, _ * expectation (PMF.pure (i,none)) payoff
      simp only [expectation_pure]

/-- A source-call result reporting more remaining budget than the initial budget has zero
probability. -/
theorem sourceCallPMF_zero_of_remaining_gt (N : ℕ) (hN : 1 < N) (A : Finset (Fin N))
    (stage budget : ℕ) (i : Fin N) (r : ℕ) (hr : budget < r) :
    sourceCallPMF N hN A stage budget (i,some r) = 0 := by
  induction budget using Nat.strong_induction_on generalizing stage with
  | h b ih =>
    rw [sourceCallPMF,PMF.bind_apply]
    apply ENNReal.tsum_eq_zero.mpr
    intro x
    split_ifs with hc
    · split
      next j _ =>
        have hh : r ≠ b-x.2.val.1.val := by omega
        simp [PMF.pure_apply,Prod.mk.injEq,hh]
      next ho =>
        have hj := token_none_pos N hN stage x ho
        rw [ih (b-x.2.val.1.val) (Nat.sub_lt (by omega) hj) _
          (lt_of_le_of_lt (Nat.sub_le _ _) hr)]
        simp
    · simp [PMF.bind_apply,PMF.pure_apply]

/-- Any source-call result of nonzero probability reports at most the initial budget as
remaining. -/
theorem sourceCallPMF_remaining_le (N : ℕ) (hN : 1 < N) (A : Finset (Fin N))
    (stage budget : ℕ) (i : Fin N) (r : ℕ)
    (hp : sourceCallPMF N hN A stage budget (i,some r) ≠ 0) : r ≤ budget := by
  by_contra h
  exact hp (sourceCallPMF_zero_of_remaining_gt N hN A stage budget i r (by omega))

/-- For `N > 1`, the initialization charge `binaryLog N` is at least one. -/
theorem source_init_ge_one (N : ℕ) (hN : 1 < N) : 1 ≤ binaryLog N := by
  have h2 : (2:ℝ) ≤ N := by exact_mod_cast hN
  unfold binaryLog
  apply (le_div_iff₀ (Real.log_pos (by norm_num : (1:ℝ) < 2))).mpr
  simpa using! Real.log_le_log (by norm_num : (0:ℝ) < 2) h2

/-- The natural query boundary `Nat.floor remaining + 1` associated with a real remaining
budget. -/
def queryBoundary (remaining : ℝ) : ℕ := Nat.floor remaining + 1

/-- The output law of the outer minimum-search loop with finite fuel and a real source-clock
budget. -/
def outerPMF {N : ℕ} {α : Type*} [LinearOrder α] (T : Fin N → α) (hN : 1 < N) :
    ℕ → ℝ → Fin N → PMF (Fin N)
  | 0,_,current => PMF.pure current
  | fuel+1,remaining,current =>
    if remaining < 0 then PMF.pure current else
      let afterInit := remaining-binaryLog N
      if afterInit < 0 then
        (partialObsPMF (by simpa using! (show 0 < N by omega)) (strictMarked T current) 0 0).bind
          fun candidate => PMF.pure (checkedUpdate T current candidate)
      else
        let boundary := queryBoundary afterInit
        (sourceCallPMF N hN (strictMarked T current) 0 boundary).bind fun x =>
          let next := checkedUpdate T current x.1
          match x.2 with
          | none => PMF.pure next
          | some r => outerPMF T hN fuel (afterInit-((boundary-r : ℕ) : ℝ)) next

/-- The recursive nonnegative payoff evaluator for the outer minimum-search loop. -/
def outerEval {N : ℕ} {α : Type*} [LinearOrder α] (T : Fin N → α) (hN : 1 < N) :
    ℕ → ℝ → Fin N → (Fin N → ℝ≥0∞) → ℝ≥0∞
  | 0,_,current,payoff => payoff current
  | fuel+1,remaining,current,payoff =>
    if remaining < 0 then payoff current else
      let afterInit := remaining-binaryLog N
      if afterInit < 0 then
        ∑' candidate : Fin N, partialObsPMF (by simpa using! (show 0 < N by omega))
          (strictMarked T current) 0 0 candidate * payoff (checkedUpdate T current candidate)
      else
        let boundary := queryBoundary afterInit
        sourceCallEval N hN (strictMarked T current) 0 boundary (fun x =>
          let next := checkedUpdate T current x.1
          match x.2 with
          | none => payoff next
          | some r => outerEval T hN fuel (afterInit-((boundary-r : ℕ) : ℝ)) next payoff)

/-- The outer-loop evaluator equals expectation under `outerPMF`. -/
theorem outerEval_eq_expectation {N : ℕ} {α : Type*} [LinearOrder α]
    (T : Fin N → α) (hN : 1 < N) (fuel : ℕ) (remaining : ℝ) (current : Fin N)
    (payoff : Fin N → ℝ≥0∞) :
    outerEval T hN fuel remaining current payoff = expectation (outerPMF T hN fuel remaining current) payoff := by
  induction fuel generalizing remaining current with
  | zero => simp only [outerEval,outerPMF,expectation_pure]
  | succ fuel ih =>
    rw [outerEval,outerPMF]
    (try dsimp only)
    split_ifs
    · exact (expectation_pure _ _).symm
    · rw [expectation_bind]
      change _ = ∑' i : Fin N, _ * expectation (PMF.pure (checkedUpdate T current i)) payoff
      simp only [expectation_pure]
    · rw [sourceCallEval_eq_expectation,expectation_bind]
      apply tsum_congr
      intro x
      congr 1
      (try dsimp only)
      cases x.2 with
      | none => simpa only using! (expectation_pure (checkedUpdate T current x.1) payoff).symm
      | some r => exact ih _ _

/-- Once the real remaining budget is below the fuel, adding further fuel leaves the output law
unchanged. -/
theorem outerPMF_fuel_stable {N : ℕ} {α : Type*} [LinearOrder α]
    (T : Fin N → α) (hN : 1 < N) (fuel extra : ℕ) (remaining : ℝ) (current : Fin N)
    (hf : remaining < fuel) :
    outerPMF T hN (fuel+extra) remaining current = outerPMF T hN fuel remaining current := by
  induction fuel generalizing remaining current with
  | zero =>
    cases extra with
    | zero => rfl
    | succ e =>
      have hr : remaining < 0 := by simpa using! hf
      simp [outerPMF,hr]
  | succ fuel ih =>
    have heq : fuel+1+extra = (fuel+extra)+1 := by omega
    rw [heq,outerPMF,outerPMF]
    (try dsimp only)
    split_ifs
    · rfl
    · rfl
    · apply congrArg (PMF.bind (sourceCallPMF N hN (strictMarked T current) 0
        (queryBoundary (remaining-binaryLog N))))
      funext x
      cases x.2 with
      | none => rfl
      | some r =>
        apply ih
        have hinit := source_init_ge_one N hN
        have hcost : (0:ℝ) ≤ ((queryBoundary (remaining-binaryLog N)-r : ℕ) : ℝ) :=
          Nat.cast_nonneg _
        push_cast at hf
        linarith

/-- The clocked minimum-search output law from a specified initial index, with fuel chosen from
the cutoff. -/
def sourceMinimumPMF {N : ℕ} {α : Type*} [LinearOrder α] (T : Fin N → α) (hN : 0 < N)
    (cutoff : ℝ) (current : Fin N) : PMF (Fin N) :=
  if h1 : N = 1 then PMF.pure current else
    outerPMF T (by omega) (Nat.floor cutoff+1) cutoff current

/-- The payoff evaluator for clocked minimum search from a specified initial index. -/
def sourceMinimumEval {N : ℕ} {α : Type*} [LinearOrder α] (T : Fin N → α) (hN : 0 < N)
    (cutoff : ℝ) (current : Fin N) (payoff : Fin N → ℝ≥0∞) : ℝ≥0∞ :=
  if h1 : N = 1 then payoff current else
    outerEval T (by omega) (Nat.floor cutoff+1) cutoff current payoff

/-- The minimum-search evaluator equals expectation under `sourceMinimumPMF`. -/
theorem sourceMinimumEval_eq_expectation {N : ℕ} {α : Type*} [LinearOrder α]
    (T : Fin N → α) (hN : 0 < N) (cutoff : ℝ) (current : Fin N)
    (payoff : Fin N → ℝ≥0∞) :
    sourceMinimumEval T hN cutoff current payoff = expectation (sourceMinimumPMF T hN cutoff current) payoff := by
  unfold sourceMinimumEval sourceMinimumPMF
  split_ifs
  · exact (expectation_pure _ _).symm
  · exact outerEval_eq_expectation T _ _ _ _ _

/-- The clocked minimum-search law with a uniformly sampled initial index. -/
def sourceInitialPMF {N : ℕ} {α : Type*} [LinearOrder α] (T : Fin N → α) (hN : 0 < N)
    (cutoff : ℝ) : PMF (Fin N) :=
  (iterationPMF N hN).bind (sourceMinimumPMF T hN cutoff)

/-- The minimum-search payoff evaluator averaged over a uniformly sampled initial index. -/
def sourceInitialEval {N : ℕ} {α : Type*} [LinearOrder α] (T : Fin N → α) (hN : 0 < N)
    (cutoff : ℝ) (payoff : Fin N → ℝ≥0∞) : ℝ≥0∞ :=
  ∑' current : Fin N, iterationPMF N hN current * sourceMinimumEval T hN cutoff current payoff

/-- The uniformly initialized evaluator equals expectation under `sourceInitialPMF`. -/
theorem sourceInitialEval_eq_expectation {N : ℕ} {α : Type*} [LinearOrder α]
    (T : Fin N → α) (hN : 0 < N) (cutoff : ℝ) (payoff : Fin N → ℝ≥0∞) :
    sourceInitialEval T hN cutoff payoff = expectation (sourceInitialPMF T hN cutoff) payoff := by
  rw [sourceInitialPMF,expectation_bind]
  unfold sourceInitialEval expectation
  apply tsum_congr
  intro current
  rw [sourceMinimumEval_eq_expectation]
  rfl

/-- The real probability that uniformly initialized clocked minimum search returns a global
minimum. -/
def sourceSuccess {N : ℕ} {α : Type*} [LinearOrder α] (T : Fin N → α) (hN : 0 < N)
    (cutoff : ℝ) : ℝ :=
  (sourceInitialEval T hN cutoff (fun i => if ∀ j, T i ≤ T j then 1 else 0)).toReal

/-- The outer-loop output law is concentrated at the current index whenever that index is a
global minimum. -/
theorem outerPMF_preserves_minimum {N : ℕ} {α : Type*} [LinearOrder α]
    (T : Fin N → α) (hN : 1 < N) (fuel : ℕ) (remaining : ℝ) (current : Fin N)
    (hmin : ∀ j, T current ≤ T j) : outerPMF T hN fuel remaining current = PMF.pure current := by
  have hupdate (candidate : Fin N) : checkedUpdate T current candidate = current :=
    checkedUpdate_preserves_minimum T current candidate hmin
  induction fuel generalizing remaining with
  | zero => rfl
  | succ fuel ih =>
    rw [outerPMF]
    (try dsimp only)
    split_ifs
    · rfl
    · simp only [hupdate]
      exact PMF.bind_const _ _
    · simp only [hupdate]
      have he : (fun x : CallResult N => match x.2 with
          | none => PMF.pure current
          | some r => outerPMF T hN fuel
              (remaining-binaryLog N-((queryBoundary (remaining-binaryLog N)-r : ℕ) : ℝ)) current) =
          fun _ => PMF.pure current := by
        funext x
        cases x.2 <;> simp only [ih]
      rw [he]
      exact PMF.bind_const _ _

/-- The clocked minimum-search law preserves a current index that is already a global minimum. -/
theorem sourceMinimumPMF_preserves_minimum {N : ℕ} {α : Type*} [LinearOrder α]
    (T : Fin N → α) (hN : 0 < N) (cutoff : ℝ) (current : Fin N)
    (hmin : ∀ j, T current ≤ T j) : sourceMinimumPMF T hN cutoff current = PMF.pure current := by
  unfold sourceMinimumPMF
  split_ifs
  · rfl
  · exact outerPMF_preserves_minimum T _ _ _ current hmin

/-- The reward of one raw attempt, continuing on failure and using a partial observation when
the budget interrupts the attempt. -/
def rawAttemptReward (N : ℕ) (hN : 1 < N) (A : Finset (Fin N))
    (stage budget : ℕ) (payoff : CallResult N → ℝ≥0∞)
    (o : Fin (ExponentialSizes N stage) × Option (Fin N)) : ℝ≥0∞ :=
  if o.1.val < budget then
    match o.2 with
    | some i => payoff (i,some (budget-o.1.val))
    | none => sourceCallEval N hN A (stage+1) (budget-o.1.val) payoff
  else ∑' i : Fin N, partialObsPMF (by simpa using! (show 0 < N by omega)) A o.1.val budget i *
    payoff (i,none)

/-- The source-call evaluator is the escape sum of the raw-attempt rewards. -/
theorem sourceCallEval_eq_escapeSum (N : ℕ) (hN : 1 < N) (A : Finset (Fin N))
    (stage budget : ℕ) (payoff : CallResult N → ℝ≥0∞) :
    sourceCallEval N hN A stage budget payoff =
      escapeSum (sourceRow N A stage) (sourceDead N hN stage)
        (fun n x => rawAttemptReward N hN A (advance stage n) budget payoff x.val) := by
  rw [sourceCallEval]
  trans (∑' x : SourceToken N hN stage, sourceEscapePMF N hN A stage x *
      rawAttemptReward N hN A (advance stage x.1) budget payoff x.2.val)
  · apply tsum_congr
    intro x
    congr 1
    unfold rawAttemptReward
    split_ifs
    · split
      next i ho => simp only [ho]
      next ho => simp only [ho]
    · rfl
  · exact escapePMF_sum (sourceRow N A stage) (sourceDead N hN stage)
      (sourceRow_nonneg N hN A stage) (sourceRow_sum N hN A stage)
      (sourceDead_half N hN A stage)
      (fun n x => rawAttemptReward N hN A (advance stage n) budget payoff x.val)

/-- For a positive budget, the zero-iteration failure reward is the next-stage source-call
evaluation with the same budget. -/
theorem rawAttemptReward_dead (N : ℕ) (hN : 1 < N) (A : Finset (Fin N))
    (stage budget : ℕ) (hb : 0 < budget) (payoff : CallResult N → ℝ≥0∞) :
    rawAttemptReward N hN A stage budget payoff (sourceDead N hN stage 0) =
      sourceCallEval N hN A (stage+1) budget payoff := by
  simp [rawAttemptReward,sourceDead,advance,hb]

/-- For a positive budget, the source-call evaluator equals the attempt-mass average of
`rawAttemptReward`. -/
theorem sourceCallEval_bellman (N : ℕ) (hN : 1 < N) (A : Finset (Fin N))
    (stage budget : ℕ) (hb : 0 < budget) (payoff : CallResult N → ℝ≥0∞) :
    sourceCallEval N hN A stage budget payoff =
      ∑ o : Fin (ExponentialSizes N stage) × Option (Fin N),
        ENNReal.ofReal (AttemptMass A (ExponentialSizes N stage) o) *
          rawAttemptReward N hN A stage budget payoff o := by
  rw [sourceCallEval_eq_escapeSum,
    escapeSum_head _ _ (sourceRow_nonneg N hN A stage)]
  change (∑' x : {x : SourceOutcome N stage 0 // x ≠ sourceDead N hN stage 0},
      ENNReal.ofReal (sourceRow N A stage 0 x) * rawAttemptReward N hN A stage budget payoff x.val) +
      ENNReal.ofReal (sourceRow N A stage 0 (sourceDead N hN stage 0)) *
        escapeSum (sourceRow N A (stage+1)) (sourceDead N hN (stage+1))
          (fun n x => rawAttemptReward N hN A (advance (stage+1) n) budget payoff x.val) = _
  rw [← sourceCallEval_eq_escapeSum N hN A (stage+1) budget payoff]
  rw [tsum_fintype,← rawAttemptReward_dead N hN A stage budget hb payoff]
  exact sum_nondead_add (Ω := SourceOutcome N stage) 0 (sourceDead N hN stage 0)
    (fun o => ENNReal.ofReal (sourceRow N A stage 0 o) * rawAttemptReward N hN A stage budget payoff o)

/-- The exponential attempt-size schedule shifted to start at `stage`. -/
def shiftedSizes (N stage k : ℕ) : ℕ := ExponentialSizes N (advance stage k)

/-- Every finite prefix of successful completion rewards is bounded by the source-call evaluator
for a positive budget. -/
theorem sourceCall_rewardPrefix_le (N : ℕ) (hN : 1 < N) (A : Finset (Fin N))
    (stage budget depth : ℕ) (hb : 0 < budget) (payoff : CallResult N → ℝ≥0∞) :
    Qatlib.Concepts.AmplitudeSearch.InterruptMin.rewardPrefix A (shiftedSizes N stage) budget depth payoff ≤
      sourceCallEval N hN A stage budget payoff := by
  have hcard : 0 < Fintype.card (Fin N) := by simpa using! (show 0 < N by omega)
  induction depth generalizing stage budget with
  | zero =>
    simp only [Qatlib.Concepts.AmplitudeSearch.InterruptMin.rewardPrefix,Finset.range_zero,Finset.sum_empty]
    exact zero_le
  | succ depth ih =>
    rw [Qatlib.Concepts.AmplitudeSearch.InterruptMin.rewardPrefix_succ hcard,sourceCallEval_bellman N hN A stage budget hb payoff,
      Fintype.sum_prod_type]
    apply Finset.sum_le_sum
    intro j _
    by_cases hc : j.val < budget
    · rw [if_pos hc,Fintype.sum_option]
      simp only [rawAttemptReward,if_pos hc]
      have hrec : Qatlib.Concepts.AmplitudeSearch.InterruptMin.rewardPrefix A (TailSizes (shiftedSizes N stage))
          (budget-j.val) depth payoff ≤ sourceCallEval N hN A (stage+1) (budget-j.val) payoff := by
        simpa only [TailSizes,shiftedSizes,advance] using! ih (stage+1) (budget-j.val) (by omega)
      rw [add_comm]
      exact add_le_add (mul_le_mul_right hrec _) le_rfl
    · rw [if_neg hc]
      exact zero_le

/-- The full payoff mass of terminal traces completing strictly before a positive budget is
bounded by the source-call evaluator. -/
theorem sourceCall_completion_le (N : ℕ) (hN : 1 < N) (A : Finset (Fin N))
    (stage budget : ℕ) (hb : 0 < budget) (payoff : CallResult N → ℝ≥0∞) :
    (∑' x : TerminalTrace (Fin N) (shiftedSizes N stage),
      if TerminalCost (shiftedSizes N stage) x < budget then
        ENNReal.ofReal (TerminalMass A (shiftedSizes N stage) x) *
          payoff (TerminalOutput x,some (budget-TerminalCost (shiftedSizes N stage) x)) else 0) ≤
      sourceCallEval N hN A stage budget payoff := by
  have heq : (∑' x : TerminalTrace (Fin N) (shiftedSizes N stage),
      if TerminalCost (shiftedSizes N stage) x < budget then
        ENNReal.ofReal (TerminalMass A (shiftedSizes N stage) x) *
          payoff (TerminalOutput x,some (budget-TerminalCost (shiftedSizes N stage) x)) else 0) =
      ∑' n, Qatlib.Concepts.AmplitudeSearch.InterruptMin.rewardRow A (shiftedSizes N stage) budget n payoff := by
    calc
      _ = ∑' n, ∑' x : TerminalStage (Fin N) (shiftedSizes N stage) n,
          if TerminalCost (shiftedSizes N stage) ⟨n,x⟩ < budget then
            ENNReal.ofReal (TerminalMass A (shiftedSizes N stage) ⟨n,x⟩) *
              payoff (TerminalOutput ⟨n,x⟩,some (budget-TerminalCost (shiftedSizes N stage) ⟨n,x⟩)) else 0 :=
        ENNReal.tsum_sigma _
      _ = _ := by simp_rw [tsum_fintype,Qatlib.Concepts.AmplitudeSearch.InterruptMin.rewardRow_terminal]
  rw [heq]
  apply ENNReal.tsum_le_of_sum_range_le
  intro depth
  exact sourceCall_rewardPrefix_le N hN A stage budget depth hb payoff

/-- The exponential schedule shifted by zero equals the original schedule. -/
theorem shiftedSizes_zero (N : ℕ) : shiftedSizes N 0 = ExponentialSizes N := by
  funext k
  simp [shiftedSizes,advance_eq]

/-- For nonnegative `remaining`, `cost < queryBoundary remaining` holds exactly when the real
cost is at most `remaining`. -/
theorem queryBoundary_iff (remaining : ℝ) (h : 0 ≤ remaining) (cost : ℕ) :
    cost < queryBoundary remaining ↔ (cost : ℝ) ≤ remaining := by
  rw [queryBoundary,Nat.lt_succ_iff,Nat.le_floor_iff h]

/-- The outer-loop evaluator returns the current payoff whenever the current index is a global
minimum. -/
theorem outerEval_of_minimum {N : ℕ} {α : Type*} [LinearOrder α]
    (T : Fin N → α) (hN : 1 < N) (fuel : ℕ) (remaining : ℝ) (current : Fin N)
    (hmin : ∀ j, T current ≤ T j) (payoff : Fin N → ℝ≥0∞) :
    outerEval T hN fuel remaining current payoff = payoff current := by
  rw [outerEval_eq_expectation,outerPMF_preserves_minimum T hN fuel remaining current hmin,
    expectation_pure]

/-- The expectation of a payoff bounded above by one is at most one. -/
theorem expectation_le_one {S : Type} (p : PMF S) (f : S → ℝ≥0∞) (hf : ∀ x, f x ≤ 1) :
    expectation p f ≤ 1 := by
  calc
    _ ≤ ∑' x, p x := by
      apply ENNReal.tsum_le_tsum
      intro x
      exact (mul_le_mul_right (hf x) (p x)).trans_eq (mul_one _)
    _ = 1 := p.tsum_coe

/-- The source rank-process completion mass is bounded by the minimum-event evaluation of the
finite-fuel outer loop when the budget is below its fuel. -/
theorem source_completion_le_outer {N : ℕ} {α : Type*} [LinearOrder α]
    (T : SortedRankedTable N α) (hN : 1 < N) (initial : Fin N)
    (fuel : ℕ) (budget : ℝ) (hf : budget < fuel) :
    Qatlib.Concepts.AmplitudeSearch.InterruptMin.completion (sourceBBHTLaw T.indexOfRank (by omega)) T.skip
      (T.skip.next initial) budget ≤
        outerEval T.value hN fuel budget (T.indexOfRank initial)
          (fun i => if ∀ j, T.value i ≤ T.value j then 1 else 0) := by
  let law := sourceBBHTLaw T.indexOfRank (show 0 < N by omega)
  let payoff : Fin N → ℝ≥0∞ := fun i => if ∀ j, T.value i ≤ T.value j then 1 else 0
  have hall : ∀ t : ℕ, ∀ y : Fin N, T.skip.next y = t → ∀ (f : ℕ) (b : ℝ), b < f →
      Qatlib.Concepts.AmplitudeSearch.InterruptMin.completion law T.skip t b ≤ outerEval T.value hN f b (T.indexOfRank y) payoff := by
    intro t
    induction t using Nat.strong_induction_on with
    | h t ih =>
      intro y hy f b hfb
      cases f with
      | zero =>
        rw [Qatlib.Concepts.AmplitudeSearch.InterruptMin.completion_neg law T.skip t b (by simpa using! hfb)]
        exact zero_le
      | succ f =>
        cases t with
        | zero =>
          have hmin : ∀ j, T.value (T.indexOfRank y) ≤ T.value j :=
              (T.lowerCut_zero_iff_minimum y).mp hy
          rw [outerEval_of_minimum T.value hN (f+1) b (T.indexOfRank y) hmin payoff]
          have hp : payoff (T.indexOfRank y) = 1 := by simp [payoff,hmin]
          rw [hp]
          exact Qatlib.Concepts.AmplitudeSearch.InterruptMin.completion_le_one law T.skip 0 (by omega) b
        | succ t =>
          have htN : t+1 < N := by
            rw [← hy]
            exact lt_of_le_of_lt (T.skip.le_rank y) y.isLt
          by_cases hb : b < 0
          · rw [Qatlib.Concepts.AmplitudeSearch.InterruptMin.completion_neg law T.skip (t+1) b hb]
            exact zero_le
          · by_cases hpaid : b-binaryLog N < 0
            · rw [Qatlib.Concepts.AmplitudeSearch.InterruptMin.completion_step law T.skip (t+1) (by omega) htN b]
              have he : (fun x : SearchTrace N => if law.duration x ≤ b then ENNReal.ofReal (law.mass (t+1) x) *
                  Qatlib.Concepts.AmplitudeSearch.InterruptMin.completion law T.skip (T.skip.next (law.outputRank x)) (b-law.duration x) else 0) =
                  fun _ => 0 := by
                funext x
                have hd :
                    law.duration x = (TerminalCost (ExponentialSizes N) x : ℝ) + binaryLog N := rfl
                have hc : ¬law.duration x ≤ b := by
                  rw [hd]
                  have hn := Nat.cast_nonneg (α := ℝ) (TerminalCost (ExponentialSizes N) x)
                  linarith
                rw [if_neg hc]
              rw [he,tsum_zero]
              exact zero_le
            · have hafter : 0 ≤ b-binaryLog N := le_of_not_gt hpaid
              let A := strictMarked T.value (T.indexOfRank y)
              let cap := queryBoundary (b-binaryLog N)
              let S : CallResult N → ℝ≥0∞ := fun x =>
                let next := checkedUpdate T.value (T.indexOfRank y) x.1
                match x.2 with
                | none => payoff next
                | some r => outerEval T.value hN f (b-binaryLog N-((cap-r : ℕ) : ℝ)) next payoff
              have hmarked : A = rankMarked T.indexOfRank (t+1) := by
                have h := rankMarked_eq_strict_values T y
                change rankMarked T.indexOfRank (T.skip.next y) = A at h
                rw [hy] at h
                exact h.symm
              have hm (x : SearchTrace N) : law.mass (t+1) x = TerminalMass A (ExponentialSizes N) x := by
                simp only [law,sourceBBHTLaw,bbhtJointLaw,
                  if_pos (show 0 < t+1 ∧ t+1 < N from ⟨by omega,htN⟩),← hmarked]
              have hd (x : SearchTrace N) : law.duration x =
                  (TerminalCost (ExponentialSizes N) x : ℝ) + binaryLog N := rfl
              have hpoint (x : SearchTrace N) :
                  (if law.duration x ≤ b then ENNReal.ofReal (law.mass (t+1) x) *
                    Qatlib.Concepts.AmplitudeSearch.InterruptMin.completion law T.skip (T.skip.next (law.outputRank x)) (b-law.duration x) else 0) ≤
                  (if TerminalCost (ExponentialSizes N) x < cap then
                    ENNReal.ofReal (TerminalMass A (ExponentialSizes N) x) *
                      S (TerminalOutput x,some (cap-TerminalCost (ExponentialSizes N) x)) else 0) := by
                have hciff : law.duration x ≤ b ↔ TerminalCost (ExponentialSizes N) x < cap := by
                  rw [hd]
                  dsimp [cap]
                  rw [queryBoundary_iff _ hafter]
                  constructor <;> intro h <;> linarith
                by_cases hc : TerminalCost (ExponentialSizes N) x < cap
                · rw [if_pos (hciff.mpr hc),if_pos hc,← hm]
                  have hcancel :
                      cap-(cap-TerminalCost (ExponentialSizes N) x) = TerminalCost
                      (ExponentialSizes N) x := by omega
                  dsimp [S]
                  rw [hcancel]
                  by_cases hx : (law.outputRank x).val < t+1
                  · have hnext : T.skip.next (law.outputRank x) < t+1 := lt_of_le_of_lt (T.skip.le_rank _) hx
                    have hlow : T.value (T.indexOfRank (law.outputRank x)) < T.value (T.indexOfRank y) := by
                      apply (T.smaller_iff_lowerCut y _).mpr
                      change (law.outputRank x).val < T.skip.next y
                      rwa [hy]
                    have hout : T.indexOfRank (law.outputRank x) = TerminalOutput x :=
                        T.indexOfRank.apply_symm_apply _
                    have hcheck : checkedUpdate T.value (T.indexOfRank y) (TerminalOutput x) = TerminalOutput x := by
                      apply if_pos
                      rwa [hout] at hlow
                    rw [hcheck]
                    have hrem : b-law.duration x < (f:ℝ) := by
                      rw [hd]
                      have hi := source_init_ge_one N hN
                      have hcost := Nat.cast_nonneg (α := ℝ) (TerminalCost (ExponentialSizes N) x)
                      push_cast at hfb
                      linarith
                    have hrec := ih _ hnext (law.outputRank x) rfl f (b-law.duration x) hrem
                    rw [hout] at hrec
                    have hr : b-binaryLog N-(TerminalCost (ExponentialSizes N) x : ℝ) = b-law.duration x := by
                      rw [hd]
                      ring
                    rw [hr]
                    exact mul_le_mul_right hrec _
                  · rw [law.lower_support (t+1) (by omega) htN x hx]
                    simp
                · rw [if_neg (fun h => hc (hciff.mp h)),if_neg hc]
              have hdom : (∑' x : SearchTrace N, if TerminalCost (ExponentialSizes N) x < cap then
                  ENNReal.ofReal (TerminalMass A (ExponentialSizes N) x) *
                    S (TerminalOutput x,some (cap-TerminalCost (ExponentialSizes N) x)) else 0) ≤
                  sourceCallEval N hN A 0 cap S := by
                have h :=
                    sourceCall_completion_le N hN A 0 cap (by dsimp [cap,queryBoundary]; omega) S
                rw [shiftedSizes_zero N] at h
                exact h
              have houter : outerEval T.value hN (f+1) b (T.indexOfRank y) payoff = sourceCallEval N hN A 0 cap S := by
                rw [outerEval,if_neg hb]
                (try dsimp only)
                rw [if_neg hpaid]
              calc
                _ = ∑' x : SearchTrace N, if law.duration x ≤ b then ENNReal.ofReal (law.mass (t+1) x) *
                    Qatlib.Concepts.AmplitudeSearch.InterruptMin.completion law T.skip (T.skip.next (law.outputRank x)) (b-law.duration x) else 0 :=
                  Qatlib.Concepts.AmplitudeSearch.InterruptMin.completion_step law T.skip (t+1) (by omega) htN b
                _ ≤ _ := ENNReal.tsum_le_tsum hpoint
                _ ≤ sourceCallEval N hN A 0 cap S := hdom
                _ = _ := houter.symm
  exact hall _ initial rfl fuel budget hf

/-- The source rank-process completion mass is bounded by the global-minimum event under the
clocked minimum-search evaluator. -/
theorem source_completion_le_minimum {N : ℕ} {α : Type*} [LinearOrder α]
    (T : SortedRankedTable N α) (hN : 0 < N) (initial : Fin N) (budget : ℝ) :
    Qatlib.Concepts.AmplitudeSearch.InterruptMin.completion (sourceBBHTLaw T.indexOfRank hN) T.skip (T.skip.next initial) budget ≤
      sourceMinimumEval T.value hN budget (T.indexOfRank initial)
        (fun i => if ∀ j, T.value i ≤ T.value j then 1 else 0) := by
  by_cases h1 : N = 1
  · subst N
    have hmin : ∀ j, T.value (T.indexOfRank initial) ≤ T.value j := by
      intro j
      rw [show j = T.indexOfRank initial from Subsingleton.elim _ _]
    rw [sourceMinimumEval,dif_pos rfl,if_pos hmin]
    exact Qatlib.Concepts.AmplitudeSearch.InterruptMin.completion_le_one _ _ _
      (lt_of_le_of_lt (T.skip.le_rank initial) initial.isLt) budget
  · rw [sourceMinimumEval,dif_neg h1]
    exact source_completion_le_outer T (by omega) initial _ budget (by
      simpa only [Nat.cast_add,Nat.cast_one] using! Nat.lt_floor_add_one budget)

/-- The uniform initialization law assigns each index the mass `ENNReal.ofReal (1 / N)`. -/
theorem iterationPMF_eq_ofReal (N : ℕ) (hN : 0 < N) (i : Fin N) :
    iterationPMF N hN i = ENNReal.ofReal ((1:ℝ)/N) := by
  rw [← iterationPMF_toReal N hN i]
  exact (ENNReal.ofReal_toReal ((iterationPMF N hN).apply_ne_top i)).symm

/-- The source-clock attainment mass is bounded by the minimum-event evaluation under uniform
initialization. -/
theorem source_attainment_le_event {N : ℕ} {α : Type*} [LinearOrder α]
    (T : Fin N → α) (hN : 0 < N) (budget : ℝ) :
    ENNReal.ofReal (clause40AttainmentMass T hN budget) ≤
      sourceInitialEval T hN budget (fun i => if ∀ j, T i ≤ T j then 1 else 0) := by
  let ranked := SortedRankedTable.ofTable T
  let law := sourceBBHTLaw ranked.indexOfRank hN
  change ENNReal.ofReal (∑' x : Fin N × List (SearchTrace N),
    if law.runClock x.2 ≤ budget then law.initialMass ranked.skip x else 0) ≤ _
  rw [Qatlib.Concepts.AmplitudeSearch.InterruptMin.initial_completion law ranked.skip hN budget]
  calc
    _ ≤ ∑' i : Fin N, ENNReal.ofReal ((1:ℝ)/N) *
        sourceMinimumEval T hN budget (ranked.indexOfRank i)
          (fun j => if ∀ k, T j ≤ T k then 1 else 0) := by
      apply ENNReal.tsum_le_tsum
      intro i
      exact mul_le_mul_right (source_completion_le_minimum ranked hN i budget) _
    _ = _ := by
      unfold sourceInitialEval
      simp_rw [iterationPMF_eq_ofReal]
      exact ranked.indexOfRank.tsum_eq (fun i : Fin N => ENNReal.ofReal ((1:ℝ)/N) *
        sourceMinimumEval T hN budget i (fun j => if ∀ k, T j ≤ T k then 1 else 0))

/-- The source-clock attainment mass is nonnegative. -/
theorem source_attainment_nonneg {N : ℕ} {α : Type*} [LinearOrder α]
    (T : Fin N → α) (hN : 0 < N) (budget : ℝ) : 0 ≤ clause40AttainmentMass T hN budget := by
  let ranked := SortedRankedTable.ofTable T
  have hm := (sourceBBHTLaw ranked.indexOfRank hN).initialMass_normalized ranked.skip hN
  unfold clause40AttainmentMass clause40AttainmentMassOn
  apply tsum_nonneg
  intro x
  split_ifs
  · exact hm.2 x
  · exact le_rfl

/-- The source-clock attainment mass is bounded by the success probability of the clocked
minimum-search law. -/
theorem source_attainment_le_success {N : ℕ} {α : Type*} [LinearOrder α]
    (T : Fin N → α) (hN : 0 < N) (budget : ℝ) :
    clause40AttainmentMass T hN budget ≤ sourceSuccess T hN budget := by
  let payoff : Fin N → ℝ≥0∞ := fun i => if ∀ j, T i ≤ T j then 1 else 0
  have hb : sourceInitialEval T hN budget payoff ≤ 1 := by
    rw [sourceInitialEval_eq_expectation]
    exact expectation_le_one _ _ (fun i => by dsimp [payoff]; split_ifs <;> simp)
  have hfin : sourceInitialEval T hN budget payoff ≠ ∞ :=
    ne_of_lt (lt_of_le_of_lt hb ENNReal.one_lt_top)
  have h := ENNReal.toReal_mono hfin (source_attainment_le_event T hN budget)
  rw [ENNReal.toReal_ofReal (source_attainment_nonneg T hN budget)] at h
  exact h

/-- At `sourceTimeout N`, the clocked minimum-search law succeeds with probability at least one
half, as in the minimum-finding guarantee of [DurrHoyer1996]. -/
theorem source_timeout_half {N : ℕ} {α : Type*} [LinearOrder α]
    (T : Fin N → α) (hN : 0 < N) :
    (1/2:ℝ) ≤ sourceSuccess T hN (sourceTimeout N) :=
  (clause40_source_cutoff_attainment_half T hN).trans
    (source_attainment_le_success T hN (sourceTimeout N))

/-- Combines the one-half success bound at `sourceTimeout N` with the expectation representation
of the uniformly initialized evaluator. -/
theorem frontier1 {N : ℕ} {α : Type*} [LinearOrder α] (T : Fin N → α) (hN : 0 < N) :
    (1/2:ℝ) ≤ sourceSuccess T hN (sourceTimeout N) ∧
    (∀ payoff : Fin N → ℝ≥0∞,
      sourceInitialEval T hN (sourceTimeout N) payoff =
        expectation (sourceInitialPMF T hN (sourceTimeout N)) payoff) :=
  ⟨source_timeout_half T hN,fun payoff => sourceInitialEval_eq_expectation T hN _ payoff⟩

end Qatlib.Concepts.AmplitudeSearch.InterruptMin
