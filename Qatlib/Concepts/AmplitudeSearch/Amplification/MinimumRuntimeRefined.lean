/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.AmplitudeSearch.Amplification.MinimumRuntimeRefinedDefs
import Qatlib.Concepts.QueryComplexity.DegreeMethod.Stopping
import Qatlib.Concepts.StoppingCore.BranchCostCore.BranchCostExecution
import Qatlib.Concepts.FairRandomBits.GeometricRetry
import Qatlib.Concepts.AmplitudeSearch.Amplification.BBHTCall
import Qatlib.Concepts.AmplitudeSearch.Amplification.SortedTable
import Qatlib.Concepts.AmplitudeSearch.Amplification.ClockBounds
import Qatlib.Concepts.AmplitudeSearch.Amplification.ClockedPrefix
import Qatlib.Concepts.AmplitudeSearch.Amplification.Basic
import Qatlib.Concepts.AmplitudeSearch.Amplification.FinalRemarksAmplificationAqua
import Qatlib.Concepts.AmplitudeSearch.Amplification.ChargedBudgetSuccess
import Qatlib.Concepts.AmplitudeSearch.Amplification.MinimumBudgetProbability
import Qatlib.Concepts.AmplitudeSearch.Amplification.Lemma2
import Qatlib.Concepts.AmplitudeSearch.Amplification.TableRun
set_option backward.isDefEq.respectTransparency false
set_option warningAsError false
open Qatlib.Concepts.FairRandomBits.GeometricRetry
open Qatlib.Concepts.StoppingCore.BranchCostCore
open Qatlib.Concepts.AdversaryBounds.AdvDuality.CappedFeedback
open Qatlib.Concepts.AdversaryBounds.AdvDuality.FairFeedback
open Qatlib.Concepts.AdversaryBounds.AdvDuality.HybridCounts
open Qatlib.Concepts.AdversaryBounds.AdvDuality.HybridLeaf
open Qatlib.Concepts.LinearLearning.ConcisePipeline
open Qatlib.Concepts.AmplitudeSearch.Amplification
open Qatlib.Concepts.AmplitudeSearch.Amplification.Experiment
open Qatlib.Concepts.AmplitudeSearch.Amplification.RankedCallLaw
open Qatlib.Concepts.AmplitudeSearch.Amplification.SortedRankedTable
open Qatlib.Concepts.StoppingCore.BranchCostCore
open Qatlib.Concepts.QueryComplexity.DegreeMethod

set_option autoImplicit false

namespace Qatlib.Concepts.AmplitudeSearch.Amplification

open Matrix
open scoped BigOperators Classical ENNReal Classical
open Qatlib
open Qatlib.Concepts.AEMeanReadout.LocalAEBackend
open Qatlib.Concepts.AEMeanReadout.LocalAEBackend.RandomizedExecution

theorem clause6_retry_exact_receipt (coin : PMF Bool) (good bad n : ℕ) (hg : 0 < good)
    (hb : 0 < bad) :
    branchHaltJoint (branchRetryNext coin good bad) (.inr ()) true
      (RetryCostLedger good bad n) = (coin false) ^ n * coin true := by
  rw [RetryCostLedger]
  exact branch_cost_geometric_retry_exact_receipt coin good bad hg hb n

theorem clause6_retry_charge_is_the_ledger (coin : PMF Bool) (good bad n : ℕ) (hg : 0 < good)
    (hb : 0 < bad) :
    branchHaltJoint (branchRetryNext coin good bad) (.inr ()) true
      (n * bad + good) = (coin false) ^ n * coin true :=
  branch_cost_geometric_retry_exact_receipt coin good bad hg hb n

theorem clause7_same_path_cutoff (S O : Type) (next : S → PMF ((O ⊕ S) × ℕ))
    (hp : ∀ s cfg k, next s (cfg, k) ≠ 0 → 1 ≤ k) (cfg : O ⊕ S) (b : ℕ)
    (hfinite : generalUnboundedTime (branchClockNext next) (branchClockEmbed cfg) < ⊤) :
    generalPendingMass (branchClockNext next) (branchClockEmbed cfg) b ≤
      generalUnboundedTime (branchClockNext next) (branchClockEmbed cfg) / (b + 1 : ℝ≥0∞) := by
  exact (branch_cost_same_path_expectation_and_cutoff S O next hp cfg b hfinite).2.2

theorem clause8_pending_keeps_sampled_successor (S O : Type) (next : S → PMF ((O ⊕ S) × ℕ))
    (cfg : O ⊕ S) (k a b : ℕ) (hab : a + b ≤ k) :
    runFor (branchClockNext next) (a + b) (branchClockDelay cfg (k + 1)) =
      PMF.pure (branchClockDelay cfg (k + 1 - a - b), a + b) ∧
    runFor (branchClockNext next) (a + b) (branchClockDelay cfg (k + 1)) =
      CostedLaw.bind (runFor (branchClockNext next) a (branchClockDelay cfg (k + 1)))
        (runFor (branchClockNext next) b) :=
  branch_cost_budget_resume_keeps_sampled_successor S O next cfg k a b hab

theorem clause8_zero_price_is_outside_the_positive_support_model (O : Type) (s : Unit) :
    ¬ Qatlib.Concepts.StoppingCore.BranchCostCore.PositiveReceiptCost
        (O := O) (Qatlib.Concepts.StoppingCore.BranchCostCore.zeroCostLoop (O := O) s) :=
  Qatlib.Concepts.QueryComplexity.DegreeMethod.clause14_zero_cost_loop_violates_positive_cost
    O s

theorem clause7_source_timeout_is_the_printed_deadline (N : ℕ) :
    sourceTimeout N = sourcePrintedDeadline N ∧ sourceTimeout N = 2 * sourceMeanBudget N := by
  constructor
  · rfl
  · exact sourceTimeout_eq_twice N

theorem clause7_printed_deadline_is_twice_the_mean_budget (N : ℕ) :
    sourcePrintedDeadline N = 2 * sourceMeanBudget N := by
  have h1 := (clause7_source_timeout_is_the_printed_deadline N).1
  have h2 := (clause7_source_timeout_is_the_printed_deadline N).2
  rw [h1] at h2
  exact h2

theorem clause7_source_integer_deadline (N : ℕ) :
    sourcePrintedDeadline N ≤ (sourceIntegerDeadline N : ℝ) ∧
    (sourceIntegerDeadline N : ℝ) < sourcePrintedDeadline N + 1 := by
  have hpos : (0 : ℝ) ≤ sourcePrintedDeadline N := by
    unfold sourcePrintedDeadline
    have h1 : (0 : ℝ) ≤ (45 / 2 : ℝ) * Real.sqrt N := by positivity
    have h2 : (0 : ℝ) ≤ (7 / 5 : ℝ) * (binaryLog N) ^ 2 := by positivity
    linarith
  unfold sourceIntegerDeadline
  constructor
  · exact Nat.le_ceil _
  · exact Nat.ceil_lt_add_one hpos

theorem clause7_source_cutoff_fns_agree {N : ℕ} {α : Type} [LinearOrder α]
    (T : Fin N → α) (hN : 0 < N) (deadline : ℝ) :
    sourceCutoffMassFn T hN deadline = sourceCutoffSuccessFn T hN deadline := by
  funext x
  have hnn : 0 ≤ (sourceProgramLaw T hN).initialMass (sourceProgramSkip T) x := by
    exact ((sourceProgramLaw T hN).initialMass_normalized (sourceProgramSkip T) hN).2 x
  simp only [sourceCutoffMassFn, sourceCutoffSuccessFn]
  by_cases hc : (sourceProgramLaw T hN).runClock x.2 ≤ deadline
  · rw [if_pos hc]
    by_cases hm : 0 < (sourceProgramLaw T hN).initialMass (sourceProgramSkip T) x
    · rw [if_pos ⟨hc, hm⟩]
    · rw [if_neg (by simp [hc, hm])]
      rw [le_antisymm (le_of_not_gt hm) hnn]
  · rw [if_neg hc]
    rw [if_neg (by simp [hc])]

theorem clause7_source_cutoff_success_half {N : ℕ} {α : Type} [LinearOrder α]
    (T : Fin N → α) (hN : 0 < N) :
    ∃ p : ℝ, HasSum (sourceCutoffSuccessFn T hN (sourcePrintedDeadline N)) p ∧
      1 / 2 ≤ p ∧ p ≤ 1 := by
  have hlaw :
      sourceProgramLaw T hN = sourceBBHTLaw ((SortedRankedTable.ofTable T).indexOfRank) hN := rfl
  obtain ⟨q, hq, _, hqb⟩ := bbht_source_attainment_moment (SortedRankedTable.ofTable T) hN
  obtain ⟨p, hp, hhalf, hple⟩ := nonnegative_clock_half_mass
    ((sourceProgramLaw T hN).initialMass (sourceProgramSkip T))
    (fun x => (sourceProgramLaw T hN).runClock x.2)
    ((sourceProgramLaw T hN).initialMass_normalized (sourceProgramSkip T) hN).1
    ((sourceProgramLaw T hN).initialMass_normalized (sourceProgramSkip T) hN).2
    (fun x => (sourceProgramLaw T hN).runClock_nonneg x.2)
    q (sourceMeanBudget N) hq hqb (sourceMeanBudget_pos N hN)
  have hdead : 2 * sourceMeanBudget N = sourcePrintedDeadline N :=
    (clause7_printed_deadline_is_twice_the_mean_budget N).symm
  rw [hdead] at hp
  refine ⟨p, ?_, hhalf, hple⟩
  have hmass : (fun x : Fin N × List (SearchTrace N) =>
      if (sourceProgramLaw T hN).runClock x.2 ≤ sourcePrintedDeadline N then
        (sourceProgramLaw T hN).initialMass (sourceProgramSkip T) x else 0)
      = sourceCutoffMassFn T hN (sourcePrintedDeadline N) := by
    funext x
    simp only [sourceCutoffMassFn]
  rw [hmass] at hp
  have hagree := clause7_source_cutoff_fns_agree T hN (sourcePrintedDeadline N)
  rw [hagree] at hp
  exact hp

theorem clause7_source_cutoff_runs_attain_a_true_minimum {N : ℕ} {α : Type} [LinearOrder α]
    (T : Fin N → α) (hN : 0 < N)
    (x : Fin N × List (SearchTrace N))
    (hx : 0 < (sourceProgramLaw T hN).initialMass (sourceProgramSkip T) x) :
    ∀ i : Fin N,
      T (finalCheckedIndex T ((SortedRankedTable.ofTable T).indexOfRank x.1)
        (tableClockedTrace (SortedRankedTable.ofTable T) (sourceProgramLaw T hN) x.2)) ≤ T i := by
  have h := (lemma2 N hN α T).2.1
  exact h x hx

theorem clause7_source_cutoff_is_four_times_tighter_than_the_corrected_deadline (N : ℕ) :
    chargedBudget N = Nat.ceil (4 * sourcePrintedDeadline N) := by
  rw [← (clause7_source_timeout_is_the_printed_deadline N).1]
  exact chargedBudget_eq_four_sourceTimeout N

theorem clause7_independent_runs_failure_is_exact {N : ℕ} {α : Type} [LinearOrder α]
    (T : Fin N → α) (hN : 0 < N) (c : ℕ) (hc : 1 ≤ c) :
    CostedLaw.event (independentRunsPMF T hN c) (fun x => ¬∀ j, T x.1 ≤ T j)
      = (CostedLaw.event (chargedInitialPMF T hN (chargedBudget N))
        (fun x => ¬∀ j, T x.1 ≤ T j)) ^ c := by
  induction c using Nat.strong_induction_on with
  | h c ih =>
    cases c with
    | zero => omega
    | succ c =>
      cases c with
      | zero =>
        simp only [independentRunsPMF]
        rw [pow_one]
      | succ c =>
        simp only [independentRunsPMF]
        rw [amplifiedStep_failure]
        have hrec := ih (c + 1) (by omega) (by omega)
        rw [hrec, pow_succ]
        ring

theorem clause7_independent_runs_failure_value {N : ℕ} {α : Type} [LinearOrder α]
    (T : Fin N → α) (hN : 0 < N) (c : ℕ) (_hc : 1 ≤ c) :
    independentRunsFailure T hN c = (singleRunFailure T hN) ^ c := rfl

private theorem one_half_eq_one_over {c : ℕ} (hc : 0 < c) :
    (1 / 2 : ℝ) ^ c = 1 / ((2 * c : ℕ) : ℝ) ↔ (2 : ℝ) ^ c = (2 * c : ℕ) := by
  have hpos2 : (0 : ℝ) < 2 ^ c := by positivity
  have hden : ((2 * c : ℕ) : ℝ) ≠ 0 := by positivity
  rw [div_pow, one_pow]
  constructor
  · intro h
    have hA : (1 : ℝ) = (1 / ((2 * c : ℕ) : ℝ)) * 2 ^ c := by
      have hh := (div_eq_iff hpos2.ne').mp h
      exact hh
    have hB : (1 : ℝ) = (1 / ((2 * c : ℕ) : ℝ)) * ((2 * c : ℕ) : ℝ) := by
      have hh := (div_eq_iff hden).mp
        (show (1 : ℝ) / ((2 * c : ℕ) : ℝ) = 1 / ((2 * c : ℕ) : ℝ) from rfl)
      simpa using! hh
    have hne : (1 / ((2 * c : ℕ) : ℝ)) ≠ 0 := by positivity
    apply (mul_right_cancel₀ hne)
    calc 2 ^ c * (1 / ((2 * c : ℕ) : ℝ))
        = (1 / ((2 * c : ℕ) : ℝ)) * 2 ^ c := by ring
      _ = 1 := hA.symm
      _ = (1 / ((2 * c : ℕ) : ℝ)) * ((2 * c : ℕ) : ℝ) := hB
      _ = ((2 * c : ℕ) : ℝ) * (1 / ((2 * c : ℕ) : ℝ)) := by ring
  · intro h
    have hB : (1 : ℝ) = (1 / ((2 * c : ℕ) : ℝ)) * ((2 * c : ℕ) : ℝ) := by
      have hh := (div_eq_iff hden).mp
        (show (1 : ℝ) / ((2 * c : ℕ) : ℝ) = 1 / ((2 * c : ℕ) : ℝ) from rfl)
      simpa using! hh
    apply (div_eq_iff hpos2.ne').mpr
    calc 1 = (1 / ((2 * c : ℕ) : ℝ)) * ((2 * c : ℕ) : ℝ) := hB
      _ = (1 / ((2 * c : ℕ) : ℝ)) * 2 ^ c := by rw [h]

private theorem two_pow_gt {c : ℕ} (hc : 3 ≤ c) : (2 : ℝ) ^ (c - 1) > c := by
  induction c using Nat.strong_induction_on with
  | h c ih =>
    rcases Nat.eq_or_lt_of_le hc with h3 | hlt
    · subst h3
      norm_num
    · have hprev : (2 : ℝ) ^ (c - 2) > (c - 1 : ℕ) := by
        have h := ih (c - 1) (by omega) (by omega)
        rw [show (c - 1) - 1 = c - 2 by omega] at h
        exact h
      have hone : c - 1 = (c - 2) + 1 := by omega
      rw [hone, pow_succ]
      have hnonneg : (0 : ℝ) ≤ 2 ^ (c - 2) := by positivity
      have hmul : (2 : ℝ) ^ (c - 2) * 2 > ((c - 1 : ℕ) : ℝ) * 2 :=
        mul_lt_mul_of_pos_right hprev (by norm_num)
      have hc2 : ((c - 1 : ℕ) : ℝ) * 2 ≥ (c : ℝ) := by
        have hn : (c - 1) * 2 ≥ c := by omega
        exact_mod_cast hn
      linarith

theorem clause7_single_longer_run_comparison {N : ℕ} {α : Type} [LinearOrder α]
    (T : Fin N → α) (hN : 0 < N) (c : ℕ) (hc : 0 < c) :
    (c : ℝ) * (chargedBudget N : ℝ) = (c * chargedBudget N : ℕ) ∧
    singleRunFailure T hN ≤ 1 / 2 ∧
    1 - 1 / ((2 * c : ℕ) : ℝ) ≤ chargedInitialSuccess T (c * chargedBudget N) ∧
    (1 - 1 / ((2 * c : ℕ) : ℝ) = 1 - (1 / 2 : ℝ) ^ c ↔ c ≤ 2) := by
  have hcost : (c : ℝ) * (chargedBudget N : ℝ) = (c * chargedBudget N : ℕ) := by
    push_cast
    ring
  have hhalf : (1 / 2 : ℝ) ≤ chargedInitialSuccess T (chargedBudget N) :=
    charged_initial_success_half T hN
  have hfail : singleRunFailure T hN ≤ 1 / 2 := by
    unfold singleRunFailure
    linarith
  have hamp : 1 - 1 / ((2 * c : ℕ) : ℝ) ≤ chargedInitialSuccess T (c * chargedBudget N) :=
    charged_initial_success_amplified T hN c hc
  refine ⟨hcost, hfail, hamp, ?_⟩
  constructor
  · intro h
    have h1 : 1 / ((2 * c : ℕ) : ℝ) = (1 / 2 : ℝ) ^ c := by linarith
    have h2 : (2 : ℝ) ^ c = (2 * c : ℕ) := (one_half_eq_one_over hc).mp h1.symm
    have h3 : (2 : ℝ) ^ (c - 1) = (c : ℝ) := by
      have hstep : (2 : ℝ) ^ c = 2 ^ (c - 1) * 2 := by
        have hle : c - 1 + 1 = c := by omega
        calc (2 : ℝ) ^ c = 2 ^ (c - 1 + 1) := by rw [hle]
          _ = 2 ^ (c - 1) * 2 := by rw [pow_succ]
      have hcast : ((2 * c : ℕ) : ℝ) = 2 * (c : ℝ) := by push_cast; ring
      rw [hstep, hcast] at h2
      linarith
    by_cases hle : c ≤ 2
    · exact hle
    · have hgt : (2 : ℝ) ^ (c - 1) > (c : ℝ) := two_pow_gt (by omega)
      rw [h3] at hgt
      linarith
  · intro h
    rcases Nat.lt_or_ge c 2 with h1 | h2
    · have h1' : c = 1 := by omega
      subst h1'
      norm_num
    · rcases Nat.eq_or_lt_of_le h2 with h3 | h3
      · subst h3
        norm_num
      · have hgt : (2 : ℝ) ^ (c - 1) > (c : ℝ) := two_pow_gt (by omega)
        have hone : c = (c - 1) + 1 := by omega
        have hpos2 : (0 : ℝ) < 2 ^ c := by positivity
        have hstrict : (1 / 2 : ℝ) ^ c < 1 / ((2 * c : ℕ) : ℝ) := by
          have hL : (1 / 2 : ℝ) ^ c = 1 / 2 ^ c := by rw [div_pow, one_pow]
          rw [hL]
          rw [div_lt_div_iff₀ hpos2 (by positivity : (0 : ℝ) < ((2 * c : ℕ) : ℝ))]
          rw [hone, pow_succ]
          nlinarith [hgt]
        linarith

theorem clause7_actual_comparison_direction {N : ℕ} {α : Type} [LinearOrder α]
    (T : Fin N → α) (hN : 0 < N) (c : ℕ) (hc : 0 < c) :
    (1 - independentRunsFailure T hN c ≤ 1 - 1 / ((2 * c : ℕ) : ℝ)) ↔
      (1 / ((2 * c : ℕ) : ℝ) ≤ (singleRunFailure T hN) ^ c) := by
  rw [independentRunsFailure]
  generalize hB : 1 / ((2 * c : ℕ) : ℝ) = B
  generalize hF : (singleRunFailure T hN) ^ c = F
  clear hB hF
  constructor
  · intro h
    linarith
  · intro h
    linarith

theorem clause7_no_unconditional_direction_for_large_c {N : ℕ} {α : Type} [LinearOrder α]
    (T : Fin N → α) (hN : 0 < N) (c : ℕ) (hc : 3 ≤ c) :
    (1 / 2 : ℝ) ^ c < 1 / ((2 * c : ℕ) : ℝ) := by
  have hone : c = (c - 1) + 1 := by omega
  have hgt : (2 : ℝ) ^ (c - 1) > (c : ℝ) := two_pow_gt (by omega)
  have hpos2 : (0 : ℝ) < 2 ^ c := by positivity
  have hL : (1 / 2 : ℝ) ^ c = 1 / 2 ^ c := by rw [div_pow, one_pow]
  have hcast : ((2 * c : ℕ) : ℝ) = 2 * (c : ℝ) := by push_cast; ring
  have hstep : (2 : ℝ) ^ c = (2 : ℝ) ^ (c - 1) * 2 := by
    have hle : c - 1 + 1 = c := by omega
    calc (2 : ℝ) ^ c = (2 : ℝ) ^ (c - 1 + 1) := by rw [hle]
      _ = (2 : ℝ) ^ (c - 1) * 2 := by rw [pow_succ]
  rw [hL]
  rw [div_lt_div_iff₀ hpos2 (by positivity : (0 : ℝ) < ((2 * c : ℕ) : ℝ))]
  rw [hstep, hcast]
  nlinarith [hgt]

theorem clause7_comparison_decision_criterion {N : ℕ} {α : Type} [LinearOrder α]
    (T : Fin N → α) (hN : 0 < N) (c : ℕ) (hc : 0 < c) :
    (1 - 1 / ((2 * c : ℕ) : ℝ) = 1 - (1 / 2 : ℝ) ^ c ↔ c ≤ 2) ∧
      ((1 / 2 : ℝ) ^ c < 1 / ((2 * c : ℕ) : ℝ) ↔ 3 ≤ c) := by
  refine ⟨(clause7_single_longer_run_comparison T hN c hc).2.2.2, ?_⟩
  constructor
  · intro h
    by_contra hn
    have hle : c ≤ 2 := by omega
    rcases Nat.eq_or_lt_of_le hle with heq | hlt
    · subst heq
      norm_num at h
    · have h0 : c = 1 := by omega
      subst h0
      norm_num at h
  · intro h
    exact clause7_no_unconditional_direction_for_large_c T hN c h

end Qatlib.Concepts.AmplitudeSearch.Amplification
