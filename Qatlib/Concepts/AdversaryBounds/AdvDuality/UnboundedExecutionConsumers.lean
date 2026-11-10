/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.StoppingCore.BranchCostCore.UnboundedExecutionBudget
set_option warningAsError false

set_option linter.unusedSectionVars false

open Qatlib.Concepts.StoppingCore.BranchCostCore
open Qatlib.Concepts.LinearLearning.ConcisePipeline

namespace Qatlib.Concepts.AdversaryBounds.AdvDuality

open Qatlib.Concepts.AEMeanReadout.LocalAEBackend.RandomizedExecution
open scoped ENNReal Classical

theorem pendingMass_eq_sum_point {S O : Type} [Fintype S] [DecidableEq S] [Fintype O]
    [DecidableEq O] (next : S → PMF (Configuration S O)) (s0 : S) (n : ℕ) :
    pendingMass next (Sum.inr s0) n
      = ∑ s : S, runFor next n (Sum.inr s0) ((Sum.inr s : Configuration S O), n) := by
  show (∑ s : S, ∑ k ∈ Finset.range (n + 1),
      runFor next n (Sum.inr s0) ((Sum.inr s : Configuration S O), k)) = _
  refine Finset.sum_congr rfl fun s _ => ?_
  rw [Finset.sum_eq_single n
    (fun k _ hkn => runFor_point_running_off_fuel next n s0 s k hkn)
    (fun hcon => absurd (Finset.mem_range.mpr (Nat.lt_succ_self n)) hcon)]

noncomputable def twoStepKernel : Bool → PMF (Bool ⊕ Bool)
  | false => PMF.pure (Sum.inr true)
  | true => PMF.pure (Sum.inl false)

theorem tick_twoStepKernel_false : tick twoStepKernel (Sum.inr false)
    = PMF.pure ((Sum.inr true : Bool ⊕ Bool), 1) := by
  show (twoStepKernel false).map (fun cfg => (cfg, 1)) = _
  rw [show twoStepKernel false = PMF.pure (Sum.inr true : Bool ⊕ Bool) from rfl, PMF.pure_map]

theorem tick_twoStepKernel_true : tick twoStepKernel (Sum.inr true)
    = PMF.pure ((Sum.inl false : Bool ⊕ Bool), 1) := by
  show (twoStepKernel true).map (fun cfg => (cfg, 1)) = _
  rw [show twoStepKernel true = PMF.pure (Sum.inl false : Bool ⊕ Bool) from rfl, PMF.pure_map]

theorem runFor_twoStepKernel_one_true :
    runFor twoStepKernel 1 (Sum.inr true)
      = PMF.pure ((Sum.inl false : Bool ⊕ Bool), 1) := by
  rw [show runFor twoStepKernel 1 (Sum.inr true)
      = Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.bind (tick twoStepKernel (Sum.inr true)) (runFor twoStepKernel 0) from rfl,
    tick_twoStepKernel_true]
  show Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.bind
      (PMF.pure ((Sum.inl false : Bool ⊕ Bool), 1)) (runFor twoStepKernel 0) = _
  rw [show Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.bind (PMF.pure ((Sum.inl false : Bool ⊕ Bool), 1)) (runFor twoStepKernel 0)
      = PMF.bind (PMF.pure ((Sum.inl false : Bool ⊕ Bool), 1))
        (fun x => Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.charge x.2 (runFor twoStepKernel 0 x.1)) from rfl,
    PMF.pure_bind]
  show Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.charge 1
      (runFor twoStepKernel 0 (Sum.inl false)) = _
  rw [runFor_zero, Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.charge_ret]

theorem runFor_twoStepKernel_one_false :
    runFor twoStepKernel 1 (Sum.inr false)
      = PMF.pure ((Sum.inr true : Bool ⊕ Bool), 1) := by
  rw [show runFor twoStepKernel 1 (Sum.inr false)
      = Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.bind (tick twoStepKernel (Sum.inr false)) (runFor twoStepKernel 0) from rfl,
    tick_twoStepKernel_false]
  show Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.bind
      (PMF.pure ((Sum.inr true : Bool ⊕ Bool), 1)) (runFor twoStepKernel 0) = _
  rw [show Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.bind (PMF.pure ((Sum.inr true : Bool ⊕ Bool), 1)) (runFor twoStepKernel 0)
      = PMF.bind (PMF.pure ((Sum.inr true : Bool ⊕ Bool), 1))
        (fun x => Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.charge x.2 (runFor twoStepKernel 0 x.1)) from rfl,
    PMF.pure_bind]
  show Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.charge 1
      (runFor twoStepKernel 0 (Sum.inr true)) = _
  rw [runFor_zero, Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.charge_ret]

theorem runFor_twoStepKernel_two :
    runFor twoStepKernel 2 (Sum.inr false)
      = PMF.pure ((Sum.inl false : Bool ⊕ Bool), 2) := by
  rw [show runFor twoStepKernel 2 (Sum.inr false)
      = Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.bind (tick twoStepKernel (Sum.inr false)) (runFor twoStepKernel 1) from rfl,
    tick_twoStepKernel_false]
  show Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.bind
      (PMF.pure ((Sum.inr true : Bool ⊕ Bool), 1)) (runFor twoStepKernel 1) = _
  rw [show Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.bind (PMF.pure ((Sum.inr true : Bool ⊕ Bool), 1)) (runFor twoStepKernel 1)
      = PMF.bind (PMF.pure ((Sum.inr true : Bool ⊕ Bool), 1))
        (fun x => Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.charge x.2 (runFor twoStepKernel 1 x.1)) from rfl,
    PMF.pure_bind]
  show Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.charge 1
      (runFor twoStepKernel 1 (Sum.inr true)) = _
  rw [runFor_twoStepKernel_one_true, ← Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.charge_ret, Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.charge_charge,
    Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.charge_ret]

theorem runFor_twoStepKernel_ge_two (n : ℕ) (hn : 2 ≤ n) :
    runFor twoStepKernel n (Sum.inr false)
      = PMF.pure ((Sum.inl false : Bool ⊕ Bool), 2) := by
  rw [show n = 2 + (n - 2) from by omega, runFor_add, runFor_twoStepKernel_two]
  show Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.bind (PMF.pure ((Sum.inl false : Bool ⊕ Bool), 2))
      (runFor twoStepKernel (n - 2)) = _
  rw [show Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.bind (PMF.pure ((Sum.inl false : Bool ⊕ Bool), 2))
        (runFor twoStepKernel (n - 2))
      = PMF.bind (PMF.pure ((Sum.inl false : Bool ⊕ Bool), 2))
        (fun x => Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.charge x.2 (runFor twoStepKernel (n - 2) x.1)) from rfl,
    PMF.pure_bind]
  show Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.charge 2
      (runFor twoStepKernel (n - 2) (Sum.inl false)) = _
  rw [runFor_halted, Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.charge_ret]

theorem pendingMass_twoStepKernel (n : ℕ) :
    pendingMass twoStepKernel (Sum.inr false) n = if n < 2 then (1 : ℝ≥0∞) else 0 := by
  rw [pendingMass_eq_sum_point, Fintype.sum_bool]
  rcases Nat.lt_or_ge n 2 with hn | hn
  · rw [if_pos hn]
    rcases n with _ | _ | n
    · rw [runFor_zero]
      show (Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.ret (Sum.inr false)) ((Sum.inr true : Bool ⊕ Bool), 0)
          + (Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.ret (Sum.inr false)) ((Sum.inr false : Bool ⊕ Bool), 0) = 1
      show (PMF.pure ((Sum.inr false : Bool ⊕ Bool), 0)) ((Sum.inr true : Bool ⊕ Bool), 0)
          + (PMF.pure ((Sum.inr false : Bool ⊕ Bool), 0)) ((Sum.inr false : Bool ⊕ Bool), 0) = 1
      rw [PMF.pure_apply, PMF.pure_apply, if_neg (fun h => by simp at h), if_pos rfl, zero_add]
    · rw [runFor_twoStepKernel_one_false]
      show (PMF.pure ((Sum.inr true : Bool ⊕ Bool), 1)) ((Sum.inr true : Bool ⊕ Bool), 1)
          + (PMF.pure ((Sum.inr true : Bool ⊕ Bool), 1)) ((Sum.inr false : Bool ⊕ Bool), 1) = 1
      rw [PMF.pure_apply, PMF.pure_apply, if_pos rfl, if_neg (fun h => by simp at h), add_zero]
    · exact absurd hn (by omega)
  · rw [if_neg (Nat.not_lt_of_ge hn)]
    show (runFor twoStepKernel n (Sum.inr false) ((Sum.inr true : Bool ⊕ Bool), n))
        + (runFor twoStepKernel n (Sum.inr false) ((Sum.inr false : Bool ⊕ Bool), n)) = 0
    rw [runFor_twoStepKernel_ge_two n hn]
    show (PMF.pure ((Sum.inl false : Bool ⊕ Bool), 2)) ((Sum.inr true : Bool ⊕ Bool), n)
        + (PMF.pure ((Sum.inl false : Bool ⊕ Bool), 2)) ((Sum.inr false : Bool ⊕ Bool), n) = 0
    rw [PMF.pure_apply, PMF.pure_apply, if_neg (fun h => by simp at h),
      if_neg (fun h => by simp at h), add_zero]

noncomputable def selfLoopKernel : Bool → PMF (Bool ⊕ Bool) :=
  fun b => PMF.pure (Sum.inr b)

theorem tick_selfLoopKernel : tick selfLoopKernel (Sum.inr false)
    = PMF.pure ((Sum.inr false : Bool ⊕ Bool), 1) := by
  show (selfLoopKernel false).map (fun cfg => (cfg, 1)) = _
  rw [show selfLoopKernel false = PMF.pure (Sum.inr false : Bool ⊕ Bool) from rfl, PMF.pure_map]

theorem runFor_selfLoopKernel (n : ℕ) :
    runFor selfLoopKernel n (Sum.inr false)
      = PMF.pure ((Sum.inr false : Bool ⊕ Bool), n) := by
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [show runFor selfLoopKernel (n + 1) (Sum.inr false)
          = Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.bind (tick selfLoopKernel (Sum.inr false)) (runFor selfLoopKernel n)
          from rfl, tick_selfLoopKernel]
      show Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.bind (PMF.pure ((Sum.inr false : Bool ⊕ Bool), 1))
          (runFor selfLoopKernel n) = _
      rw [show Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.bind (PMF.pure ((Sum.inr false : Bool ⊕ Bool), 1))
            (runFor selfLoopKernel n)
          = PMF.bind (PMF.pure ((Sum.inr false : Bool ⊕ Bool), 1))
            (fun x => Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.charge x.2 (runFor selfLoopKernel n x.1)) from rfl,
        PMF.pure_bind]
      show Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.charge 1 (runFor selfLoopKernel n (Sum.inr false))
          = PMF.pure ((Sum.inr false : Bool ⊕ Bool), n + 1)
      rw [ih, ← Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.charge_ret, Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.charge_charge, Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.charge_ret,
        Nat.add_comm 1 n]

theorem pendingMass_selfLoopKernel (n : ℕ) :
    pendingMass selfLoopKernel (Sum.inr false) n = 1 := by
  rw [pendingMass_eq_sum_point, runFor_selfLoopKernel, Fintype.sum_bool]
  show (PMF.pure ((Sum.inr false : Bool ⊕ Bool), n)) ((Sum.inr true : Bool ⊕ Bool), n)
      + (PMF.pure ((Sum.inr false : Bool ⊕ Bool), n)) ((Sum.inr false : Bool ⊕ Bool), n) = 1
  rw [PMF.pure_apply, PMF.pure_apply, if_neg (fun h => by simp at h), if_pos rfl, zero_add]

theorem nonterminationMass_selfLoopKernel :
    nonterminationMass selfLoopKernel (Sum.inr false) = 1 := by
  show (⨅ n : ℕ, pendingMass selfLoopKernel (Sum.inr false) n) = 1
  rw [iInf_congr pendingMass_selfLoopKernel]
  exact iInf_const

theorem unboundedTime_selfLoopKernel :
    unboundedTime selfLoopKernel (Sum.inr false) = ⊤ := by
  show ∑' n : ℕ, pendingMass selfLoopKernel (Sum.inr false) n = ⊤
  rw [tsum_congr pendingMass_selfLoopKernel]
  show ∑' _n : ℕ, (1 : ℝ≥0∞) = ⊤
  rw [tsum_const_nat_ennreal]
  simp

theorem unbounded_two_step_and_infinite_loop_consumers :
    twoStepKernel false = PMF.pure (Sum.inr true) ∧
      twoStepKernel true = PMF.pure (Sum.inl false) ∧
      (unboundedLaw twoStepKernel (Sum.inr false)) (some (false, 2)) = 1 ∧
      unboundedTime twoStepKernel (Sum.inr false) = 2 ∧
      nonterminationMass (fun b : Bool => PMF.pure (Sum.inr b : Bool ⊕ Bool)) (Sum.inr false) = 1 ∧
      unboundedTime (fun b : Bool => PMF.pure (Sum.inr b : Bool ⊕ Bool)) (Sum.inr false) = ⊤ := by
  have hlaw : (unboundedLaw twoStepKernel (Sum.inr false)) (some (false, 2)) = 1 := by
    rw [(unbounded_nontermination_limit_and_joint_law twoStepKernel (Sum.inr false)).2.2.2 false 2]
    show runFor twoStepKernel 2 (Sum.inr false) ((Sum.inl false : Bool ⊕ Bool), 2) = 1
    rw [runFor_twoStepKernel_two]
    exact PMF.pure_apply_self _
  have htime : unboundedTime twoStepKernel (Sum.inr false) = 2 := by
    show ∑' n : ℕ, pendingMass twoStepKernel (Sum.inr false) n = 2
    rw [tsum_congr pendingMass_twoStepKernel]
    show ∑' n : ℕ, (if n < 2 then (1 : ℝ≥0∞) else 0) = 2
    rw [tsum_indicator_lt_ennreal]
    simp
  have hloopNT : nonterminationMass (fun b : Bool => PMF.pure (Sum.inr b : Bool ⊕ Bool))
      (Sum.inr false) = 1 :=
    nonterminationMass_selfLoopKernel
  have hloopT : unboundedTime (fun b : Bool => PMF.pure (Sum.inr b : Bool ⊕ Bool))
      (Sum.inr false) = ⊤ :=
    unboundedTime_selfLoopKernel
  exact ⟨rfl, rfl, hlaw, htime, hloopNT, hloopT⟩

end Qatlib.Concepts.AdversaryBounds.AdvDuality
