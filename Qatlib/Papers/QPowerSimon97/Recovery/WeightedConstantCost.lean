/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.StoppingCore.BranchCostCore.WeightedUnboundedExecution

/-!
# Constant charges for randomized retry executions

This module relates constant-charge weighted executions to ordinary randomized executions. It
supplies the expected-cost scaling identity used to price each verified Simon retry uniformly in
the analysis of [Simon1997].

## Main statements

* `weightedRunFor_const_charge_expected_cost`: Charging a fixed natural number `C` per execution
  step multiplies the ordinary expected execution cost by `C`.

## References

* [Simon, 1997][Simon1997]
-/

set_option warningAsError false

open Qatlib.Concepts.AEMeanReadout.LocalAEBackend.RandomizedExecution

open Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw

open Qatlib.Concepts.AEMeanReadout.LocalAEBackend

open Qatlib.Concepts.StoppingCore.BranchCostCore
open Qatlib.Concepts.LinearLearning.ConcisePipeline

set_option autoImplicit false
noncomputable section
namespace Qatlib.Papers.QPowerSimon97.Recovery
open scoped Classical ENNReal

/-- A weighted execution with constant charge `C` is the ordinary execution law with its step
count multiplied by `C`. -/
private theorem weightedRunFor_const_map
    (S O : Type) [Fintype S] [DecidableEq S] [Fintype O] [DecidableEq O]
    (next : S → PMF (O ⊕ S)) (C fuel : ℕ) (cfg : O ⊕ S) :
    weightedRunFor next (fun _ => C) fuel cfg =
      (RandomizedExecution.runFor next fuel cfg).map (fun z => (z.1, C * z.2)) := by
  induction fuel generalizing cfg with
  | zero => simp [Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.ret, PMF.pure_map]
  | succ fuel ih =>
    cases cfg with
    | inl o => simp [Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.ret, PMF.pure_map]
    | inr s =>
      rw [weightedRunFor_succ_running]
      simp only [RandomizedExecution.runFor, RandomizedExecution.tick,
        CostedLaw.bind, PMF.bind_map, PMF.map_bind, Function.comp_def]
      congr 1
      funext d
      rw [ih]
      simp only [CostedLaw.charge, PMF.map_comp, Function.comp_def]
      congr 1
      funext z
      simp only [Prod.mk.injEq, true_and]
      ring

/-- Charging a fixed natural number `C` per execution step multiplies the ordinary expected
execution cost by `C`. -/
theorem weightedRunFor_const_charge_expected_cost :
    ∀ (S O : Type) [Fintype S] [DecidableEq S] [Fintype O] [DecidableEq O]
      (next : S → PMF (O ⊕ S)) (C : ℕ) (fuel : ℕ) (cfg : O ⊕ S),
      Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectedCost (weightedRunFor next (fun _ => C) fuel cfg) =
        ((C : ℝ≥0∞) * Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectedCost (RandomizedExecution.runFor next fuel cfg)) := by
  intro S O _ _ _ _ next C fuel cfg
  rw [weightedRunFor_const_map, Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectedCost, Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectation_map,
    Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectedCost, Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectation, Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectation,
    ← ENNReal.tsum_mul_left]
  apply tsum_congr
  intro z
  simp only [Nat.cast_mul]
  ring

end Qatlib.Papers.QPowerSimon97.Recovery
