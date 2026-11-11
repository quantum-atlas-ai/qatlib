/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.StoppingCore.BranchCostCore.GeneralCostClock
import Qatlib.Concepts.StoppingCore.BranchCostCore.UnboundedExecutionBudget

/-!
# Branch-dependent cost execution and clocks

`branchCostRun` iterates a joint successor-and-cost PMF while accumulating the costs of the
sampled branches. `branchClockNext` compiles each sampled receipt into unit-time countdown
states that retain its successor.

For positive supported receipt costs, the branch run and compiled clock have the same joint
halting-output and cost law. The module derives conservation, expected-cost, and cutoff
formulas, and proves that splitting a countdown budget preserves the previously sampled
successor. For background, see [Montanaro2015].

## Main statements

* `branch_cost_actual_joint_recursion`: gives the joint output-cost recurrence and absorption of
  halted configurations.
* `branch_cost_compiled_clock_halt_joint`: identifies branch-cost and compiled-clock joint
  halting masses.
* `branch_cost_same_path_expectation_and_cutoff`: relates finite expected clock time to branch
  costs and pending-mass bounds.

## References

* [Montanaro, 2015][Montanaro2015]
-/

set_option warningAsError false
open Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw

open Qatlib.Concepts.LinearLearning.ConcisePipeline
open Qatlib.Concepts.StoppingCore.BranchCostCore.GeneralExecution

set_option autoImplicit false
set_option maxRecDepth 4096

namespace Qatlib.Concepts.StoppingCore.BranchCostCore
open Matrix
open scoped Classical BigOperators ENNReal

open Qatlib.Concepts.AEMeanReadout.LocalAEBackend.RandomizedExecution

/-- One joint successor-and-cost step, leaving halted outputs fixed with zero additional cost. -/
noncomputable def branchCostTick {S O : Type} (next : S  →  PMF ((O ⊕ S) × ℕ)) :
    O ⊕ S  →  PMF ((O ⊕ S) × ℕ)
  | .inl o => PMF.pure (.inl o,0)
  | .inr s => next s

/-- Run at most the specified number of branch transitions, accumulating the costs sampled
jointly with their successor configurations. -/
noncomputable def branchCostRun {S O : Type} (next : S  →  PMF ((O ⊕ S) × ℕ)) :
    ℕ  →  O ⊕ S  →  PMF ((O ⊕ S) × ℕ)
  | 0,cfg => CostedLaw.ret cfg
  | n+1,cfg => CostedLaw.bind (branchCostTick next cfg) (branchCostRun next n)

/-- The compiled clock state type, consisting of a state ready for a branch draw or a stored
successor configuration with a remaining delay. -/
abbrev BranchClock (S O : Type) := S ⊕ ((O ⊕ S) × ℕ)

/-- Embed an original configuration into the compiled clock, preserving a halted output and
making a running state ready for a branch draw. -/
def branchClockEmbed {S O : Type} : O ⊕ S  →  O ⊕ BranchClock S O
  | .inl o => .inl o
  | .inr s => .inr (.inl s)

/-- Represent a configuration after a remaining delay of `k` unit steps, embedding it
immediately when `k` is zero. -/
def branchClockDelay {S O : Type} (cfg : O ⊕ S) (k : ℕ) : O ⊕ BranchClock S O :=
  if k=0 then branchClockEmbed cfg else .inr (.inr (cfg,k))

/-- A unit-time clock step that either samples a successor and cost once and stores the
remaining delay, or decrements the delay of an already sampled successor. -/
noncomputable def branchClockNext {S O : Type} (next : S  →  PMF ((O ⊕ S) × ℕ)) :
    BranchClock S O  →  PMF (O ⊕ BranchClock S O)
  | .inl s => (next s).map (fun z => branchClockDelay z.1 (z.2-1))
  | .inr z => PMF.pure (branchClockDelay z.1 (z.2-1))

/-- The mass of output `o` with accumulated cost `k` in the branch run with transition fuel `k`. -/
noncomputable def branchHaltJoint {S O : Type} (next : S  →  PMF ((O ⊕ S) × ℕ))
    (cfg : O ⊕ S) (o : O) (k : ℕ) : ℝ≥0∞ :=
  branchCostRun next k cfg (.inl o,k)

/-- A retry transition that halts with output `true` and cost `good` on a true coin outcome, and
continues with cost `bad` on a false outcome. -/
noncomputable def branchRetryNext (coin : PMF Bool) (good bad : ℕ) : Unit  →  PMF ((Bool ⊕ Unit) × ℕ) :=
  fun _ => coin.map (fun b => (if b then .inl true else .inr (),if b then good else bad))

variable {S O : Type}

/-- Starting from a halted output, every branch run returns that output with zero cost. -/
@[simp] theorem branchCostRun_halted (next : S → PMF ((O ⊕ S) × ℕ)) (n : ℕ) (o : O) :
    branchCostRun next n (.inl o) = PMF.pure (.inl o,0) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    change CostedLaw.bind (CostedLaw.ret (.inl o)) (branchCostRun next n) = _
    rw [CostedLaw.ret_bind, ih]

/-- A joint point mass after one additional transition is the sum over sampled
successor-and-cost receipts, subtracting the receipt cost from the requested total when
affordable. -/
theorem branchCostRun_point (next : S → PMF ((O ⊕ S) × ℕ)) (n k : ℕ) (s : S) (cfg : O ⊕ S) :
    branchCostRun next (n+1) (.inr s) (cfg,k) =
      ∑' z : (O ⊕ S) × ℕ, next s z *
        (if z.2 ≤ k then branchCostRun next n z.1 (cfg,k-z.2) else 0) := by
  rw [branchCostRun, branchCostTick, CostedLaw.bind, PMF.bind_apply]
  simp only [charge_point_mass]

/-- The branch run satisfies the receipt-weighted joint output-cost recurrence, and a halted
initial configuration remains fixed at zero cost. -/
theorem branch_cost_actual_joint_recursion :
    ∀ (S O : Type) (next : S → PMF ((O ⊕ S) × ℕ)) (n k : ℕ) (s : S) (cfg : O ⊕ S),
      branchCostRun next (n+1) (.inr s) (cfg,k) =
        ∑' z : (O ⊕ S) × ℕ, next s z *
          (if z.2 ≤ k then branchCostRun next n z.1 (cfg,k-z.2) else 0) ∧
      ∀ o : O, branchCostRun next n (.inl o)=PMF.pure (.inl o,0) := by
  intro S O next n k s cfg
  exact ⟨branchCostRun_point next n k s cfg, branchCostRun_halted next n⟩

/-- If every supported receipt costs at least one, the mass of output `o` at total cost `k`
stabilizes to `branchHaltJoint` once transition fuel is at least `k`. -/
theorem branchCostRun_stable (next : S → PMF ((O ⊕ S) × ℕ))
    (hp : ∀ s cfg k, next s (cfg,k) ≠ 0 → 1 ≤ k)
    (cfg : O ⊕ S) (o : O) (k fuel : ℕ) (h : k ≤ fuel) :
    branchCostRun next fuel cfg (.inl o,k)=branchHaltJoint next cfg o k := by
  unfold branchHaltJoint
  induction k using Nat.strong_induction_on generalizing fuel cfg with
  | h k ih =>
    cases cfg with
    | inl a => simp
    | inr s =>
      cases k with
      | zero =>
        cases fuel with
        | zero => rfl
        | succ n =>
          rw [branchCostRun_point]
          have hz : ∀ z : (O ⊕ S) × ℕ, next s z *
              (if z.2 ≤ 0 then branchCostRun next n z.1 (.inl o,0-z.2) else 0)=0 := by
            intro z
            by_cases hmass : next s z=0
            · simp [hmass]
            · have hc := hp s z.1 z.2 hmass
              simp [show ¬ z.2 ≤ 0 by omega]
          simp only [hz, tsum_zero]
          simp [branchCostRun, CostedLaw.ret, PMF.pure_apply]
      | succ k =>
        obtain ⟨n,rfl⟩ : ∃ n, fuel=n+1 := ⟨fuel-1, by omega⟩
        rw [branchCostRun_point, branchCostRun_point]
        apply tsum_congr
        intro z
        by_cases hmass : next s z=0
        · simp [hmass]
        · have hc := hp s z.1 z.2 hmass
          split_ifs with hfit
          · rw [ih (k+1-z.2) (by omega) z.1 n (by omega),
              ih (k+1-z.2) (by omega) z.1 k (by omega)]
          · rfl

/-- A prefix of at most `k` steps of a delay `k + 1` deterministically decrements that delay and
records exactly the elapsed unit cost. -/
theorem branchClock_prefix (next : S → PMF ((O ⊕ S) × ℕ))
    (cfg : O ⊕ S) (n k : ℕ) (hn : n ≤ k) :
    runFor (branchClockNext next) n (branchClockDelay cfg (k+1)) =
      PMF.pure (branchClockDelay cfg (k+1-n),n) := by
  induction n generalizing k with
  | zero => simp [runFor, CostedLaw.ret]
  | succ n ih =>
    rw [show branchClockDelay cfg (k+1) = .inr (.inr (cfg,k+1)) by simp [branchClockDelay]]
    rw [costClock_unit_succ]
    simp only [branchClockNext, Nat.add_sub_cancel, PMF.pure_bind]
    have hk : k ≠ 0 := by omega
    have he : branchClockDelay cfg k = branchClockDelay cfg ((k-1)+1) := by
      congr 1; omega
    rw [he, ih (k-1) (by omega)]
    simp only [CostedLaw.charge, PMF.pure_map]
    congr 1
    apply Prod.ext
    · exact congrArg (branchClockDelay cfg) (by omega)
    · omega

/-- Splitting a countdown prefix into budgets `a` and `b` preserves its stored successor and
gives the same costed law as running their sum, provided `a + b ≤ k` for initial delay `k +
1`. -/
theorem branch_cost_budget_resume_keeps_sampled_successor :
    ∀ (S O : Type) (next : S → PMF ((O ⊕ S) × ℕ)) (cfg : O ⊕ S) (k a b : ℕ), a+b ≤ k →
      runFor (branchClockNext next) (a+b) (branchClockDelay cfg (k+1)) =
        PMF.pure (branchClockDelay cfg (k+1-a-b),a+b) ∧
      runFor (branchClockNext next) (a+b) (branchClockDelay cfg (k+1)) =
        CostedLaw.bind (runFor (branchClockNext next) a (branchClockDelay cfg (k+1)))
          (runFor (branchClockNext next) b) := by
  intro S O next cfg k a b h
  refine ⟨?_, runFor_add _ _ _ _⟩
  simpa only [Nat.sub_sub] using branchClock_prefix next cfg (a+b) k h

/-- Running exactly the stored delay deterministically reaches the embedded successor
configuration with that delay as the recorded cost. -/
theorem branchClock_countdown (next : S → PMF ((O ⊕ S) × ℕ)) (cfg : O ⊕ S) (d : ℕ) :
    runFor (branchClockNext next) d (branchClockDelay cfg d) =
      PMF.pure (branchClockEmbed cfg,d) := by
  induction d with
  | zero => simp [branchClockDelay, runFor, CostedLaw.ret]
  | succ d ih =>
    rw [show branchClockDelay cfg (d+1) = .inr (.inr (cfg,d+1)) by simp [branchClockDelay]]
    rw [costClock_unit_succ]
    simp only [branchClockNext, Nat.add_sub_cancel, PMF.pure_bind, ih,
      CostedLaw.charge, PMF.pure_map]
    simp [add_comm]

/-- A delayed configuration has zero halting mass before the delay expires, and afterward its
joint halting mass is that of the embedded configuration at the shifted time. -/
theorem branchClock_delay_halt (next : S → PMF ((O ⊕ S) × ℕ))
    (cfg : O ⊕ S) (o : O) (d k : ℕ) :
    haltJoint (branchClockNext next) (branchClockDelay cfg d) o k =
      if d ≤ k then haltJoint (branchClockNext next) (branchClockEmbed cfg) o (k-d) else 0 := by
  by_cases hfit : d ≤ k
  · rw [if_pos hfit]
    unfold haltJoint
    rw [show k=d+(k-d) by omega, runFor_add, branchClock_countdown]
    simp only [CostedLaw.bind, PMF.pure_bind, charge_point_mass]
    simp [hfit]
  · rw [if_neg hfit]
    unfold haltJoint
    have hd : d=(d-1)+1 := by omega
    rw [hd, branchClock_prefix next cfg k (d-1) (by omega)]
    have hpos : d-1+1-k ≠ 0 := by omega
    simp [branchClockDelay, hpos, PMF.pure_apply]

/-- With positive supported receipt costs, compiled-clock halting mass from a running state
obeys the joint receipt recurrence with the receipt cost subtracted from the halting time. -/
theorem branchClock_halt_running (next : S → PMF ((O ⊕ S) × ℕ))
    (hp : ∀ s cfg k, next s (cfg,k) ≠ 0 → 1 ≤ k) (s : S) (o : O) (k : ℕ) :
    haltJoint (branchClockNext next) (branchClockEmbed (.inr s)) o k =
      ∑' z : (O ⊕ S) × ℕ, next s z *
        (if z.2 ≤ k then haltJoint (branchClockNext next) (branchClockEmbed z.1) o (k-z.2) else 0) := by
  cases k with
  | zero =>
    have hz : ∀ z : (O ⊕ S) × ℕ, next s z *
        (if z.2 ≤ 0 then haltJoint (branchClockNext next) (branchClockEmbed z.1) o (0-z.2) else 0)=0 := by
      intro z
      by_cases hm : next s z=0
      · simp [hm]
      · have hc := hp s z.1 z.2 hm
        simp [show ¬ z.2 ≤ 0 by omega]
    simp only [hz, tsum_zero]
    simp [haltJoint, runFor, CostedLaw.ret, branchClockEmbed, PMF.pure_apply]
  | succ k =>
    unfold haltJoint
    rw [branchClockEmbed, costClock_unit_succ]
    simp only [branchClockNext, PMF.bind_map, PMF.bind_apply, Function.comp_def,
      charge_point_mass, show 1 ≤ k+1 by omega, if_true, Nat.add_sub_cancel]
    change (∑' z : (O ⊕ S) × ℕ, next s z *
      haltJoint (branchClockNext next) (branchClockDelay z.1 (z.2-1)) o k) = _
    apply tsum_congr
    intro z
    by_cases hm : next s z=0
    · simp [hm]
    · have hc := hp s z.1 z.2 hm
      rw [branchClock_delay_halt]
      have he : z.2-1 ≤ k ↔ z.2 ≤ k+1 := by omega
      by_cases hfit : z.2 ≤ k+1
      · rw [if_pos (he.mpr hfit), if_pos hfit]
        have hk : k-(z.2-1)=k+1-z.2 := by omega
        rw [hk]; rfl
      · rw [if_neg (fun h => hfit (he.mp h)), if_neg hfit]

/-- With positive supported receipt costs, compiled-clock joint halting mass equals the original
branch-cost joint halting mass. -/
theorem branchClock_bridge (next : S → PMF ((O ⊕ S) × ℕ))
    (hp : ∀ s cfg k, next s (cfg,k) ≠ 0 → 1 ≤ k)
    (cfg : O ⊕ S) (o : O) (k : ℕ) :
    haltJoint (branchClockNext next) (branchClockEmbed cfg) o k = branchHaltJoint next cfg o k := by
  induction k using Nat.strong_induction_on generalizing cfg with
  | h k ih =>
    cases cfg with
    | inl a => simp [branchClockEmbed, haltJoint, runFor_halted, branchHaltJoint, CostedLaw.ret, PMF.pure_apply]
    | inr s =>
      rw [branchClock_halt_running next hp]
      cases k with
      | zero =>
        unfold branchHaltJoint
        have hz : ∀ z : (O ⊕ S) × ℕ, next s z *
            (if z.2 ≤ 0 then haltJoint (branchClockNext next) (branchClockEmbed z.1) o (0-z.2) else 0)=0 := by
          intro z
          by_cases hm : next s z=0
          · simp [hm]
          · have hc := hp s z.1 z.2 hm
            simp [show ¬ z.2 ≤ 0 by omega]
        simp only [hz, tsum_zero]
        simp [branchCostRun, CostedLaw.ret, PMF.pure_apply]
      | succ k =>
        unfold branchHaltJoint
        rw [branchCostRun_point]
        apply tsum_congr
        intro z
        by_cases hm : next s z=0
        · simp [hm]
        · have hc := hp s z.1 z.2 hm
          split_ifs with hfit
          · rw [ih (k+1-z.2) (by omega) z.1,
              branchCostRun_stable next hp z.1 o (k+1-z.2) k (by omega)]
          · rfl

/-- Under positive supported receipt costs and fuel at least the requested total cost, the
branch run point mass and compiled-clock halting mass both equal `branchHaltJoint`. -/
theorem branch_cost_compiled_clock_halt_joint :
    ∀ (S O : Type) (next : S → PMF ((O ⊕ S) × ℕ)),
      (∀ s cfg k, next s (cfg,k) ≠ 0 → 1 ≤ k) →
      ∀ (cfg : O ⊕ S) (o : O) (k n : ℕ), k ≤ n →
      branchCostRun next n cfg (.inl o,k)=branchHaltJoint next cfg o k ∧
      haltJoint (branchClockNext next) (branchClockEmbed cfg) o k=branchHaltJoint next cfg o k := by
  intro S O next hp cfg o k n h
  exact ⟨branchCostRun_stable next hp cfg o k n h, branchClock_bridge next hp cfg o k⟩

/-- With positive supported receipt costs, total branch halting mass plus compiled-clock
nontermination mass is one. At every finite clock budget, branch halting mass up to that
cost plus pending mass is also one. -/
theorem branch_cost_output_pending_never_conservation :
    ∀ (S O : Type) (next : S → PMF ((O ⊕ S) × ℕ)),
      (∀ s cfg k, next s (cfg,k) ≠ 0 → 1 ≤ k) → ∀ cfg : O ⊕ S,
      (∑' o : O, ∑' k : ℕ, branchHaltJoint next cfg o k)+
        generalNeverMass (branchClockNext next) (branchClockEmbed cfg)=1 ∧
      (∀ n : ℕ, (∑' o : O, ∑' k : ℕ, if k ≤ n then branchHaltJoint next cfg o k else 0)+
        generalPendingMass (branchClockNext next) (branchClockEmbed cfg) n=1) := by
  intro S O next hp cfg
  have h := general_haltJoint_tsum_add_never (branchClockNext next) (branchClockEmbed cfg)
  simp_rw [branchClock_bridge next hp] at h
  refine ⟨h, ?_⟩
  intro n
  have hf := (general_unbounded_finite_partition_and_pending (BranchClock S O) O
    (branchClockNext next) (branchClockEmbed cfg)).2 n
  convert hf using 2
  apply tsum_congr
  intro o
  refine (tsum_eq_sum (s := Finset.range (n+1)) (fun k hk => ?_)).trans ?_
  · rw [if_neg (by have := Finset.mem_range.not.mp hk; omega)]
  · apply Finset.sum_congr rfl
    intro k hk
    rw [if_pos (by have := Finset.mem_range.mp hk; omega), branchClock_bridge next hp]

/-- With positive supported receipt costs and finite expected compiled-clock time,
nontermination mass is zero and expected time equals the cost-weighted branch halting sum.
Pending mass after budget `b` is bounded by that expected time divided by `b + 1`. -/
theorem branch_cost_same_path_expectation_and_cutoff :
    ∀ (S O : Type) (next : S → PMF ((O ⊕ S) × ℕ)),
      (∀ s cfg k, next s (cfg,k) ≠ 0 → 1 ≤ k) → ∀ (cfg : O ⊕ S) (b : ℕ),
      generalUnboundedTime (branchClockNext next) (branchClockEmbed cfg) < ⊤ →
      generalNeverMass (branchClockNext next) (branchClockEmbed cfg)=0 ∧
      generalUnboundedTime (branchClockNext next) (branchClockEmbed cfg)=
        ∑' o : O, ∑' k : ℕ, (k:ℝ≥0∞)*branchHaltJoint next cfg o k ∧
      generalPendingMass (branchClockNext next) (branchClockEmbed cfg) b ≤
        generalUnboundedTime (branchClockNext next) (branchClockEmbed cfg)/(b+1:ℝ≥0∞) := by
  intro S O next hp cfg b hfinite
  have h := general_unbounded_actual_expected_time (BranchClock S O) O
    (branchClockNext next) (branchClockEmbed cfg)
  have hn := h.2.1 hfinite
  have he := h.1
  simp_rw [branchClock_bridge next hp] at he
  rw [hn, mul_zero, add_zero] at he
  exact ⟨hn, he, (general_online_cutoff _ _ b).2⟩
end Qatlib.Concepts.StoppingCore.BranchCostCore
