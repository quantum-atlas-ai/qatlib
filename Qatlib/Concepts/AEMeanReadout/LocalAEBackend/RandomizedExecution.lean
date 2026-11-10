/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.LinearLearning.ConcisePipeline.RandomizedCost
set_option backward.isDefEq.respectTransparency false
set_option warningAsError false
open Qatlib.Concepts.LinearLearning.ConcisePipeline
open Qatlib

namespace Qatlib.Concepts.AEMeanReadout.LocalAEBackend
namespace RandomizedExecution

section
open scoped ENNReal
variable {State Output : Type*}

abbrev Configuration (State Output : Type*) := Output ⊕ State

noncomputable def tick (next : State → PMF (Configuration State Output)) :
    Configuration State Output → CostedLaw (Configuration State Output)
  | .inl result => Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.ret (.inl result)
  | .inr state => (next state).map (fun cfg => (cfg, 1))

noncomputable def runFor (next : State → PMF (Configuration State Output)) :
    ℕ → Configuration State Output → CostedLaw (Configuration State Output)
  | 0, cfg => Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.ret cfg
  | fuel + 1, cfg => Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.bind (tick next cfg) (runFor next fuel)

@[simp] theorem runFor_zero (next : State → PMF (Configuration State Output))
    (cfg : Configuration State Output) : runFor next 0 cfg = Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.ret cfg := rfl

@[simp] theorem runFor_halted (next : State → PMF (Configuration State Output))
    (fuel : ℕ) (out : Output) : runFor next fuel (.inl out) = Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.ret (.inl out) := by
  induction fuel with
  | zero => rfl
  | succ fuel ih => simpa [runFor, tick] using ih

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

theorem tick_bounded (next : State → PMF (Configuration State Output))
    (cfg : Configuration State Output) : Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.BoundedBy (tick next cfg) 1 := by
  cases cfg with
  | inl out => exact Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.boundedBy_ret _ _
  | inr state =>
    intro x hx
    obtain ⟨y, _, rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp hx
    exact le_rfl

theorem runFor_bounded (next : State → PMF (Configuration State Output))
    (fuel : ℕ) (cfg : Configuration State Output) :
    Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.BoundedBy (runFor next fuel cfg) fuel := by
  induction fuel generalizing cfg with
  | zero => exact Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.boundedBy_ret _ _
  | succ fuel ih =>
    simpa only [runFor, Nat.add_comm 1 fuel] using
      (Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.BoundedBy.bind (tick_bounded next cfg) ih)

theorem runFor_expectedCost_le (next : State → PMF (Configuration State Output))
    (fuel : ℕ) (cfg : Configuration State Output) :
    Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectedCost (runFor next fuel cfg) ≤ (fuel : ℝ≥0∞) :=
  (runFor_bounded next fuel cfg).expectedCost_le

end
end RandomizedExecution
end Qatlib.Concepts.AEMeanReadout.LocalAEBackend
