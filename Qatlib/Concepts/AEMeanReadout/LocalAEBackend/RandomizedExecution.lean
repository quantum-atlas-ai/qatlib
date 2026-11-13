/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.LinearLearning.ConcisePipeline.RandomizedCost

/-!
# Bounded execution of randomized stopping processes

This module models a randomized process by configurations that are either terminal outputs or
pending states. `tick` charges one unit for a transition from a pending state, and `runFor`
executes a bounded number of transitions while leaving terminal outputs fixed. This supplies
finite execution semantics for randomized quantum-search schedules such as those in
[BrassardEtAl2002].

## Main statements

* `runFor_add`: compose two bounded executions by adding their horizons.
* `runFor_bounded`: bound every supported execution cost by its horizon.
* `runFor_expectedCost_le`: bound expected execution cost by the horizon.

## References

* [Brassard et al., 2002][BrassardEtAl2002]
-/

set_option backward.isDefEq.respectTransparency false
open Qatlib.Concepts.LinearLearning.ConcisePipeline
open Qatlib

namespace Qatlib.Concepts.AEMeanReadout.LocalAEBackend
namespace RandomizedExecution

section
open scoped ENNReal
variable {State Output : Type*}

/-- A terminal output or a pending process state, represented by `Output ⊕ State`. -/
abbrev Configuration (State Output : Type*) := Output ⊕ State

/-- One costed process step: retain a terminal output at zero cost or sample a pending state's
next configuration at unit cost. -/
noncomputable def tick (next : State → PMF (Configuration State Output)) :
    Configuration State Output → CostedLaw (Configuration State Output)
  | .inl result => Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.ret (.inl result)
  | .inr state => (next state).map (fun cfg => (cfg, 1))

/-- Execute at most the specified number of randomized transitions, accumulating unit costs only
while the configuration is pending. -/
noncomputable def runFor (next : State → PMF (Configuration State Output)) :
    ℕ → Configuration State Output → CostedLaw (Configuration State Output)
  | 0, cfg => Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.ret cfg
  | fuel + 1, cfg => Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.bind (tick next cfg) (runFor next fuel)

/-- Executing with zero fuel returns the initial configuration at zero cost. -/
@[simp] theorem runFor_zero (next : State → PMF (Configuration State Output))
    (cfg : Configuration State Output) : runFor next 0 cfg = Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.ret cfg := rfl

/-- Executing from a terminal output returns that same output at zero cost for every horizon. -/
@[simp] theorem runFor_halted (next : State → PMF (Configuration State Output))
    (fuel : ℕ) (out : Output) : runFor next fuel (.inl out) = Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.ret (.inl out) := by
  induction fuel with
  | zero => rfl
  | succ fuel ih => simpa [runFor, tick] using ih

/-- Execution for horizon `m + n` equals execution for `m` followed by execution for `n`, with
costs accumulated by binding. -/
theorem runFor_add (next : State → PMF (Configuration State Output))
    (m n : ℕ) (cfg : Configuration State Output) :
    runFor next (m + n) cfg = Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.bind (runFor next m cfg) (runFor next n) := by
  induction m generalizing cfg with
  | zero => simp
  | succ m ih =>
    rw [Nat.succ_add, runFor, runFor, Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.bind_assoc]
    congr 1
    funext x
    exact ih x

/-- Every outcome of a single process step has cost at most one. -/
theorem tick_bounded (next : State → PMF (Configuration State Output))
    (cfg : Configuration State Output) : Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.BoundedBy (tick next cfg) 1 := by
  cases cfg with
  | inl out => exact Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.boundedBy_ret _ _
  | inr state =>
    intro x hx
    obtain ⟨y, _, rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp hx
    exact le_rfl

/-- Every outcome of bounded process execution has cost at most the supplied fuel. -/
theorem runFor_bounded (next : State → PMF (Configuration State Output))
    (fuel : ℕ) (cfg : Configuration State Output) :
    Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.BoundedBy (runFor next fuel cfg) fuel := by
  induction fuel generalizing cfg with
  | zero => exact Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.boundedBy_ret _ _
  | succ fuel ih =>
    simpa only [runFor, Nat.add_comm 1 fuel] using
      (Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.BoundedBy.bind (tick_bounded next cfg) ih)

/-- The expected cost of bounded process execution is at most its fuel. -/
theorem runFor_expectedCost_le (next : State → PMF (Configuration State Output))
    (fuel : ℕ) (cfg : Configuration State Output) :
    Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectedCost (runFor next fuel cfg) ≤ (fuel : ℝ≥0∞) :=
  (runFor_bounded next fuel cfg).expectedCost_le

end
end RandomizedExecution
end Qatlib.Concepts.AEMeanReadout.LocalAEBackend
