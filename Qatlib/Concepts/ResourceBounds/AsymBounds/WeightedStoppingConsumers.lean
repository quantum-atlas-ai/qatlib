/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.FairRandomBits.FiniteCoinExecution
import Qatlib.Concepts.StoppingCore.InterruptBridge.WeightedStoppingBudget
import Mathlib.Probability.Distributions.Uniform
set_option warningAsError false
open Qatlib.Concepts.StoppingCore.BranchCostCore
open Qatlib.Concepts.AEMeanReadout.LocalAEBackend.CostedLaw
open Qatlib.Concepts.AEMeanReadout.LocalAEBackend.RandomizedExecution
open Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw
open Qatlib.Concepts.AEMeanReadout.LocalAEBackend
open Qatlib.Concepts.LinearLearning.ConcisePipeline
open Qatlib.Concepts.StoppingCore.InterruptBridge

namespace Qatlib.Concepts.ResourceBounds.AsymBounds

open scoped Classical BigOperators ENNReal

noncomputable def alternatingRetryKernel : Bool → PMF (Unit ⊕ Bool)
  | false => PMF.pure (.inr true)
  | true => (PMF.uniformOfFintype' Bool).map (fun b => if b then .inl () else .inr false)

def alternatingRetryCost (b : Bool) : ℕ := if b then 3 else 2

@[simp] theorem alternatingRetryCost_positive (b : Bool) : 1 ≤ alternatingRetryCost b := by
  cases b <;> decide

@[simp] theorem alternatingRetryKernel_true_halt : alternatingRetryKernel true (.inl ()) = 1/2 := by
  simp [alternatingRetryKernel, PMF.map_apply, tsum_fintype,
    PMF.uniformOfFintype'_apply]

@[simp] theorem alternatingRetryKernel_true_false : alternatingRetryKernel true (.inr false) = 1/2 := by
  simp [alternatingRetryKernel, PMF.map_apply, tsum_fintype,
    PMF.uniformOfFintype'_apply]

@[simp] theorem alternatingRetryKernel_true_true : alternatingRetryKernel true (.inr true) = 0 := by
  simp [alternatingRetryKernel, PMF.map_apply, tsum_fintype,
    PMF.uniformOfFintype'_apply]

noncomputable def alternatingRetryMarginal (n : ℕ) : PMF (Unit ⊕ Bool) :=
  (RandomizedExecution.runFor alternatingRetryKernel n (.inr false)).map Prod.fst

theorem alternatingRetryMarginal_succ (n : ℕ) :
    alternatingRetryMarginal (n+1) (.inr false) = (1/2 : ℝ≥0∞) * alternatingRetryMarginal n (.inr true) ∧
    alternatingRetryMarginal (n+1) (.inr true) = alternatingRetryMarginal n (.inr false) := by
  have hm : alternatingRetryMarginal (n+1) =
      (alternatingRetryMarginal n).bind (fun d => match d with
        | .inl o => PMF.pure (.inl o)
        | .inr s => alternatingRetryKernel s) := by
    unfold alternatingRetryMarginal
    rw [Qatlib.Concepts.AEMeanReadout.LocalAEBackend.RandomizedExecution.runFor_add,
        costedLaw_map_fst_bind]
    congr 1
    funext d
    have hone : RandomizedExecution.runFor alternatingRetryKernel 1 d =
        RandomizedExecution.tick alternatingRetryKernel d := CostedLaw.bind_ret _
    rw [hone]
    cases d with
    | inl o => exact PMF.pure_map _ _
    | inr s => simpa only [RandomizedExecution.tick, PMF.map_comp, Function.comp_def] using!
        (PMF.map_id (alternatingRetryKernel s))
  rw [hm]
  constructor <;>
    simp [PMF.bind_apply, tsum_fintype,
      alternatingRetryKernel, PMF.map_apply, PMF.uniformOfFintype'_apply, PMF.pure_apply, mul_comm]

theorem alternatingRetryMarginal_even (m : ℕ) :
    alternatingRetryMarginal (2*m) (.inr false) = (1/2 : ℝ≥0∞)^m ∧
    alternatingRetryMarginal (2*m) (.inr true) = 0 := by
  induction m with
  | zero => simp [alternatingRetryMarginal, Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.ret, PMF.pure_map, PMF.pure_apply]
  | succ m ih =>
    have h1 := alternatingRetryMarginal_succ (2*m)
    have h2 := alternatingRetryMarginal_succ (2*m+1)
    rw [show 2*(m+1) = (2*m+1)+1 by omega]
    rw [h2.1, h2.2, h1.1, h1.2, ih.1, ih.2]
    simp [pow_succ, mul_comm]

theorem alternatingRetryOccupation (m : ℕ) :
    Qatlib.Concepts.StoppingCore.InterruptBridge.weightedOccupation alternatingRetryKernel alternatingRetryCost (.inr false) (2*m) =
      2 * (1/2 : ℝ≥0∞)^m ∧
    Qatlib.Concepts.StoppingCore.InterruptBridge.weightedOccupation alternatingRetryKernel alternatingRetryCost (.inr false) (2*m+1) =
      3 * (1/2 : ℝ≥0∞)^m := by
  have he := alternatingRetryMarginal_even m
  have ho := alternatingRetryMarginal_succ (2*m)
  change _ = _ ∧ _ = _
  unfold Qatlib.Concepts.StoppingCore.InterruptBridge.weightedOccupation
  change (∑ s : Bool, alternatingRetryMarginal (2*m) (.inr s) * (alternatingRetryCost s : ℝ≥0∞)) = _ ∧
    (∑ s : Bool, alternatingRetryMarginal (2*m+1) (.inr s) * (alternatingRetryCost s : ℝ≥0∞)) = _
  simp only [Fintype.sum_bool]
  rw [ho.1, ho.2, he.1, he.2]
  simp [alternatingRetryCost, mul_comm]

theorem alternatingRetry_expectedCost :
    Qatlib.Concepts.StoppingCore.InterruptBridge.weightedExpectedCost alternatingRetryKernel alternatingRetryCost (.inr false) = 10 := by
  unfold Qatlib.Concepts.StoppingCore.InterruptBridge.weightedExpectedCost
  rw [← tsum_even_add_odd ENNReal.summable ENNReal.summable]
  simp_rw [(alternatingRetryOccupation _).1, (alternatingRetryOccupation _).2]
  rw [ENNReal.tsum_mul_left, ENNReal.tsum_mul_left, ENNReal.tsum_geometric]
  norm_num

theorem alternatingRetry_budget_four :
    Qatlib.Concepts.StoppingCore.InterruptBridge.weightedBudgetRun alternatingRetryKernel alternatingRetryCost 4 (.inr false) =
      PMF.pure (.inr true,2) := by
  rw [Qatlib.Concepts.StoppingCore.InterruptBridge.weightedBudgetRun_paid _ _ 4 false (by decide)]
  simp only [alternatingRetryKernel, PMF.pure_bind, alternatingRetryCost, Bool.false_eq_true,
    if_false]
  rw [weightedBudgetRun_pending _ _ 2 true (by decide),
      Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.charge_ret]

theorem alternatingRetry_budget_five :
    Qatlib.Concepts.StoppingCore.InterruptBridge.weightedBudgetRun alternatingRetryKernel alternatingRetryCost 5 (.inr false) =
      (alternatingRetryKernel true).map (fun d => (d,5)) := by
  rw [Qatlib.Concepts.StoppingCore.InterruptBridge.weightedBudgetRun_paid _ _ 5 false (by decide)]
  simp only [alternatingRetryKernel, PMF.pure_bind, alternatingRetryCost, Bool.false_eq_true,
    if_false]
  rw [Qatlib.Concepts.StoppingCore.InterruptBridge.weightedBudgetRun_paid _ _ 3 true (by decide)]
  simp only [alternatingRetryCost, if_true, Nat.sub_self, weightedBudgetRun_zero,
    Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.charge_ret]
  change CostedLaw.charge 2 ((alternatingRetryKernel true).map (fun d => (d,3))) = _
  simp only [CostedLaw.charge, alternatingRetryKernel, PMF.map_comp, Function.comp_def]

theorem alternatingRetry_halt_five :
    Qatlib.Concepts.StoppingCore.BranchCostCore.weightedHaltJoint alternatingRetryKernel alternatingRetryCost (.inr false) () 5 = 1/2 := by
  rw [← Qatlib.Concepts.StoppingCore.InterruptBridge.weightedBudgetRun_halt_point _ _ alternatingRetryCost_positive _ _ 5 5 le_rfl,
    alternatingRetry_budget_five]
  simp [PMF.map_apply, tsum_fintype]

theorem alternatingRetry_budget_ten_halt :
    Qatlib.Concepts.StoppingCore.InterruptBridge.weightedBudgetRun alternatingRetryKernel alternatingRetryCost 10 (.inr false) (.inl (),10) = 1/4 := by
  rw [Qatlib.Concepts.StoppingCore.InterruptBridge.weightedBudgetRun_paid _ _ 10 false (by decide)]
  simp only [alternatingRetryKernel, PMF.pure_bind, alternatingRetryCost, Bool.false_eq_true,
    if_false, Qatlib.Concepts.StoppingCore.BranchCostCore.charge_point_mass]
  norm_num
  rw [Qatlib.Concepts.StoppingCore.InterruptBridge.weightedBudgetRun_paid _ _ 8 true (by decide)]
  simp only [alternatingRetryCost, if_true]
  norm_num
  rw [Qatlib.Concepts.StoppingCore.BranchCostCore.charge_point_mass]
  norm_num
  rw [alternatingRetry_budget_five]
  simp [PMF.map_apply, tsum_fintype]
  rw [← ENNReal.mul_inv (by simp) (by simp)]
  norm_num

theorem weighted_alternating_retry_exact_consumer :
    let c : Bool → ℕ := fun b => if b then 3 else 2
    Qatlib.Concepts.StoppingCore.InterruptBridge.weightedExpectedCost alternatingRetryKernel c (.inr false) = 10 ∧
    Qatlib.Concepts.StoppingCore.BranchCostCore.nonterminationMass alternatingRetryKernel (.inr false) = 0 ∧
    Qatlib.Concepts.StoppingCore.BranchCostCore.weightedHaltJoint alternatingRetryKernel c (.inr false) () 5 = 1/2 ∧
    Qatlib.Concepts.StoppingCore.BranchCostCore.weightedHaltJoint alternatingRetryKernel c (.inr false) () 10 = 1/4 ∧
    CostedLaw.event (Qatlib.Concepts.StoppingCore.InterruptBridge.weightedBudgetRun alternatingRetryKernel c 4 (.inr false))
      (fun z => ∃ s, z.1 = Sum.inr s) = 1 ∧
    CostedLaw.event (Qatlib.Concepts.StoppingCore.InterruptBridge.weightedBudgetRun alternatingRetryKernel c 5 (.inr false))
      (fun z => ∃ s, z.1 = Sum.inr s) = 1/2 := by
  change Qatlib.Concepts.StoppingCore.InterruptBridge.weightedExpectedCost alternatingRetryKernel alternatingRetryCost (.inr false) = 10 ∧
    Qatlib.Concepts.StoppingCore.BranchCostCore.nonterminationMass alternatingRetryKernel (.inr false) = 0 ∧
    Qatlib.Concepts.StoppingCore.BranchCostCore.weightedHaltJoint alternatingRetryKernel alternatingRetryCost (.inr false) () 5 = 1/2 ∧
    Qatlib.Concepts.StoppingCore.BranchCostCore.weightedHaltJoint alternatingRetryKernel alternatingRetryCost (.inr false) () 10 = 1/4 ∧
    CostedLaw.event (Qatlib.Concepts.StoppingCore.InterruptBridge.weightedBudgetRun alternatingRetryKernel alternatingRetryCost 4 (.inr false))
      (fun z => ∃ s, z.1 = Sum.inr s) = 1 ∧
    CostedLaw.event (Qatlib.Concepts.StoppingCore.InterruptBridge.weightedBudgetRun alternatingRetryKernel alternatingRetryCost 5 (.inr false))
      (fun z => ∃ s, z.1 = Sum.inr s) = 1/2
  refine ⟨alternatingRetry_expectedCost, ?_, alternatingRetry_halt_five, ?_, ?_, ?_⟩
  · exact Qatlib.Concepts.StoppingCore.InterruptBridge.weightedExpectedCost_finite_nontermination _ _ _ alternatingRetryCost_positive
      (by rw [alternatingRetry_expectedCost]; norm_num)
  · rw [← Qatlib.Concepts.StoppingCore.InterruptBridge.weightedBudgetRun_halt_point _ _ alternatingRetryCost_positive _ _ 10 10 le_rfl]
    exact alternatingRetry_budget_ten_halt
  · rw [Qatlib.Concepts.ResourceBounds.AsymBounds.alternatingRetry_budget_four]
    simp [CostedLaw.event, CostedLaw.expectation_pure]
  · rw [alternatingRetry_budget_five, CostedLaw.event_map]
    simp [alternatingRetryKernel, CostedLaw.event, CostedLaw.expectation,
      tsum_fintype, PMF.uniformOfFintype'_apply]

end Qatlib.Concepts.ResourceBounds.AsymBounds
