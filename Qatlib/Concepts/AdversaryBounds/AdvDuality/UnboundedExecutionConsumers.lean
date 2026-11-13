/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.StoppingCore.BranchCostCore.UnboundedExecutionBudget

/-!
# Terminating and nonterminating execution examples

This module evaluates the unbounded execution constructions on two deterministic Boolean
kernels. The kernel `twoStepKernel` terminates with output `false` after two transitions from
running `false`, whereas `selfLoopKernel` remains in its running state forever. These examples
illustrate termination probabilities and expected running time in the classical computation
setting of [KitaevShenVyalyi2002].

Finite-budget laws and pending masses are computed explicitly. They yield terminal mass one at
cost two for the first example, and nontermination mass one with infinite expected time for the
self-loop.

## Main statements

* `pendingMass_eq_sum_point`: pending mass as running-state point masses at the current budget.
* `pendingMass_twoStepKernel`: pending mass vanishes exactly from time two onward.
* `unboundedTime_selfLoopKernel`: the self-loop has infinite unbounded expected time.
* `unbounded_two_step_and_infinite_loop_consumers`: the combined terminal-law and expected-time
  calculations.

## References

* [Kitaev, Shen, and Vyalyi, 2002][KitaevShenVyalyi2002]
-/

open Qatlib.Concepts.StoppingCore.BranchCostCore
open Qatlib.Concepts.LinearLearning.ConcisePipeline

namespace Qatlib.Concepts.AdversaryBounds.AdvDuality

open Qatlib.Concepts.AEMeanReadout.LocalAEBackend.RandomizedExecution
open scoped ENNReal Classical

/-- The pending mass after `n` ticks from a running state is the sum of running-state point
masses at cost exactly `n`. -/
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

/-- A deterministic kernel that moves from running `false` to running `true`, then terminates
with output `false`. -/
noncomputable def twoStepKernel : Bool → PMF (Bool ⊕ Bool)
  | false => PMF.pure (Sum.inr true)
  | true => PMF.pure (Sum.inl false)

/-- One tick from running `false` under `twoStepKernel` reaches running `true` at cost one. -/
theorem tick_twoStepKernel_false : tick twoStepKernel (Sum.inr false)
    = PMF.pure ((Sum.inr true : Bool ⊕ Bool), 1) := by
  show (twoStepKernel false).map (fun cfg => (cfg, 1)) = _
  rw [show twoStepKernel false = PMF.pure (Sum.inr true : Bool ⊕ Bool) from rfl, PMF.pure_map]

/-- One tick from running `true` under `twoStepKernel` terminates with output `false` at cost
one. -/
theorem tick_twoStepKernel_true : tick twoStepKernel (Sum.inr true)
    = PMF.pure ((Sum.inl false : Bool ⊕ Bool), 1) := by
  show (twoStepKernel true).map (fun cfg => (cfg, 1)) = _
  rw [show twoStepKernel true = PMF.pure (Sum.inl false : Bool ⊕ Bool) from rfl, PMF.pure_map]

/-- One tick of `twoStepKernel` from running `true` has the pure terminated law with output
`false` and cost one. -/
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

/-- One tick of `twoStepKernel` from running `false` has the pure running law at state `true`
and cost one. -/
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

/-- Two ticks of `twoStepKernel` from running `false` terminate with output `false` and cost two
with probability one. -/
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

/-- Every execution budget of at least two gives the same terminated law of `twoStepKernel` from
running `false`, with cost two. -/
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

/-- The pending mass of `twoStepKernel` from running `false` is one before time two and zero
thereafter. -/
theorem pendingMass_twoStepKernel (n : ℕ) :
    pendingMass twoStepKernel (Sum.inr false) n = if n < 2 then (1 : ℝ≥0∞) else 0 := by
  rw [pendingMass_eq_sum_point, Fintype.sum_bool]
  rcases Nat.lt_or_ge n 2 with hn | hn
  · rw [ite_eq_left hn]
    rcases n with _ | _ | n
    · rw [runFor_zero]
      show (Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.ret (Sum.inr false)) ((Sum.inr true : Bool ⊕ Bool), 0)
          + (Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.ret (Sum.inr false)) ((Sum.inr false : Bool ⊕ Bool), 0) = 1
      show (PMF.pure ((Sum.inr false : Bool ⊕ Bool), 0)) ((Sum.inr true : Bool ⊕ Bool), 0)
          + (PMF.pure ((Sum.inr false : Bool ⊕ Bool), 0)) ((Sum.inr false : Bool ⊕ Bool), 0) = 1
      rw [PMF.pure_apply, PMF.pure_apply, ite_eq_right (fun h => by simp at h), ite_eq_left rfl, zero_add]
    · rw [runFor_twoStepKernel_one_false]
      show (PMF.pure ((Sum.inr true : Bool ⊕ Bool), 1)) ((Sum.inr true : Bool ⊕ Bool), 1)
          + (PMF.pure ((Sum.inr true : Bool ⊕ Bool), 1)) ((Sum.inr false : Bool ⊕ Bool), 1) = 1
      rw [PMF.pure_apply, PMF.pure_apply, ite_eq_left rfl, ite_eq_right (fun h => by simp at h), add_zero]
    · exact absurd hn (by omega)
  · rw [ite_eq_right (Nat.not_lt_of_ge hn)]
    show (runFor twoStepKernel n (Sum.inr false) ((Sum.inr true : Bool ⊕ Bool), n))
        + (runFor twoStepKernel n (Sum.inr false) ((Sum.inr false : Bool ⊕ Bool), n)) = 0
    rw [runFor_twoStepKernel_ge_two n hn]
    show (PMF.pure ((Sum.inl false : Bool ⊕ Bool), 2)) ((Sum.inr true : Bool ⊕ Bool), n)
        + (PMF.pure ((Sum.inl false : Bool ⊕ Bool), 2)) ((Sum.inr false : Bool ⊕ Bool), n) = 0
    rw [PMF.pure_apply, PMF.pure_apply, ite_eq_right (fun h => by simp at h),
      ite_eq_right (fun h => by simp at h), add_zero]

/-- A deterministic kernel that returns its Boolean state as a running state forever. -/
noncomputable def selfLoopKernel : Bool → PMF (Bool ⊕ Bool) :=
  fun b => PMF.pure (Sum.inr b)

/-- One tick of `selfLoopKernel` from running `false` returns to that state at cost one. -/
theorem tick_selfLoopKernel : tick selfLoopKernel (Sum.inr false)
    = PMF.pure ((Sum.inr false : Bool ⊕ Bool), 1) := by
  show (selfLoopKernel false).map (fun cfg => (cfg, 1)) = _
  rw [show selfLoopKernel false = PMF.pure (Sum.inr false : Bool ⊕ Bool) from rfl, PMF.pure_map]

/-- After `n` ticks, `selfLoopKernel` from running `false` remains in that state with cost `n`
with probability one. -/
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

/-- The self-loop kernel has pending mass one at every finite time from running `false`. -/
theorem pendingMass_selfLoopKernel (n : ℕ) :
    pendingMass selfLoopKernel (Sum.inr false) n = 1 := by
  rw [pendingMass_eq_sum_point, runFor_selfLoopKernel, Fintype.sum_bool]
  show (PMF.pure ((Sum.inr false : Bool ⊕ Bool), n)) ((Sum.inr true : Bool ⊕ Bool), n)
      + (PMF.pure ((Sum.inr false : Bool ⊕ Bool), n)) ((Sum.inr false : Bool ⊕ Bool), n) = 1
  rw [PMF.pure_apply, PMF.pure_apply, ite_eq_right (fun h => by simp at h), ite_eq_left rfl, zero_add]

/-- The self-loop kernel from running `false` has nontermination mass one. -/
theorem nonterminationMass_selfLoopKernel :
    nonterminationMass selfLoopKernel (Sum.inr false) = 1 := by
  show (⨅ n : ℕ, pendingMass selfLoopKernel (Sum.inr false) n) = 1
  rw [iInf_congr pendingMass_selfLoopKernel]
  exact iInf_const

/-- The self-loop kernel from running `false` has infinite unbounded expected time. -/
theorem unboundedTime_selfLoopKernel :
    unboundedTime selfLoopKernel (Sum.inr false) = ⊤ := by
  show ∑' n : ℕ, pendingMass selfLoopKernel (Sum.inr false) n = ⊤
  rw [tsum_congr pendingMass_selfLoopKernel]
  show ∑' _n : ℕ, (1 : ℝ≥0∞) = ⊤
  rw [tsum_const_nat_ennreal]
  simp

/-- The two-step kernel terminates at cost two with probability one and has unbounded expected
time two, while the self-loop kernel has nontermination mass one and infinite expected time. -/
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
