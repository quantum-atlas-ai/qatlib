/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.StoppingCore.BranchCostCore.WeightedUnboundedExecution
import Qatlib.Concepts.StoppingCore.BranchCostCore.UnboundedExecutionBudget

/-!
# Expected weighted costs and online budgets

`weightedExpectedCost` sums state-charge occupation over time, while `weightedBudgetRun`
executes only positive-cost steps fitting the available budget. The module relates finite and
unbounded expected costs, proves positive-cost halting decompositions, and bounds the
probability of remaining pending after budget exhaustion.

This abstract accounting supports expected-resource analyses of randomized quantum algorithms,
such as the Monte Carlo algorithms in [Montanaro2015].

## Main statements

* `weightedExpectedCost_eq_iSup`: expected cost as a supremum of finite expectations
* `weighted_expected_cost_occupation_and_halt`: cost-weighted halting and nontermination
  decomposition
* `weighted_online_budget_joint_prefix_and_cutoff`: budget boundedness, exact halted masses, and
  a cutoff estimate

## References

* [Montanaro, 2015][Montanaro2015]
-/

set_option warningAsError false
open Qatlib.Concepts.AEMeanReadout.LocalAEBackend.CostedLaw
open Qatlib.Concepts.AEMeanReadout.LocalAEBackend.RandomizedExecution
open Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw

open Qatlib.Concepts.StoppingCore.BranchCostCore
open Qatlib.Concepts.AEMeanReadout.LocalAEBackend
open Qatlib.Concepts.LinearLearning.ConcisePipeline

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace Qatlib.Concepts.StoppingCore.InterruptBridge

open scoped Classical BigOperators ENNReal

variable {S O : Type} [Fintype S] [DecidableEq S] [Fintype O] [DecidableEq O]

/-- The expected state charge at time `n`, computed from the running-state marginal of unit-cost
execution. -/
noncomputable def weightedOccupation (next : S → PMF (O ⊕ S)) (c : S → ℕ)
    (cfg : O ⊕ S) (n : ℕ) : ℝ≥0∞ :=
  ∑ s, (RandomizedExecution.runFor next n cfg).map Prod.fst (.inr s) * (c s : ℝ≥0∞)

/-- The extended expected accumulated charge, defined as the sum of weighted occupations over
all times. -/
noncomputable def weightedExpectedCost (next : S → PMF (O ⊕ S)) (c : S → ℕ)
    (cfg : O ⊕ S) : ℝ≥0∞ := ∑' n, weightedOccupation next c cfg n

/-- The expected weighted cost from an already halted output is zero. -/
@[simp] theorem weightedExpectedCost_halted (next : S → PMF (O ⊕ S)) (c : S → ℕ)
    (o : O) : weightedExpectedCost next c (.inl o) = 0 := by
  simp [weightedExpectedCost, weightedOccupation, RandomizedExecution.runFor_halted,
    CostedLaw.ret, PMF.pure_map, PMF.pure_apply]

/-- Execute a transition only when its state cost is positive and fits the remaining budget,
subtracting that cost and accumulating the resulting charge. -/
noncomputable def weightedBudgetRun (next : S → PMF (O ⊕ S)) (c : S → ℕ)
    (budget : ℕ) (cfg : O ⊕ S) : CostedLaw (O ⊕ S) :=
  match cfg with
  | .inl o => CostedLaw.ret (.inl o)
  | .inr s => if h : 0 < c s ∧ c s ≤ budget then
      (next s).bind (fun d => CostedLaw.charge (c s) (weightedBudgetRun next c (budget-c s) d))
    else CostedLaw.ret (.inr s)
termination_by budget

/-- Budgeted execution preserves an already halted output with zero additional cost. -/
@[simp] theorem weightedBudgetRun_halted (next : S → PMF (O ⊕ S)) (c : S → ℕ)
    (B : ℕ) (o : O) : weightedBudgetRun next c B (.inl o) = CostedLaw.ret (.inl o) := by
  rw [weightedBudgetRun]

/-- A zero budget returns the initial configuration without additional cost. -/
@[simp] theorem weightedBudgetRun_zero (next : S → PMF (O ⊕ S)) (c : S → ℕ)
    (cfg : O ⊕ S) : weightedBudgetRun next c 0 cfg = CostedLaw.ret cfg := by
  cases cfg with
  | inl o => simp
  | inr s =>
    rw [weightedBudgetRun]
    exact dif_neg (by omega)

/-- Budgeted execution stays at the current running state when its cost is zero or exceeds the
remaining budget. -/
theorem weightedBudgetRun_pending (next : S → PMF (O ⊕ S)) (c : S → ℕ)
    (B : ℕ) (s : S) (h : ¬ (0 < c s ∧ c s ≤ B)) :
    weightedBudgetRun next c B (.inr s) = CostedLaw.ret (.inr s) := by
  rw [weightedBudgetRun, dif_neg h]

/-- When the positive state cost fits the budget, execution samples the next configuration and
recurses on the reduced budget while charging that cost. -/
theorem weightedBudgetRun_paid (next : S → PMF (O ⊕ S)) (c : S → ℕ)
    (B : ℕ) (s : S) (h : 0 < c s ∧ c s ≤ B) :
    weightedBudgetRun next c B (.inr s) =
      (next s).bind (fun d => CostedLaw.charge (c s) (weightedBudgetRun next c (B-c s) d)) := by
  rw [weightedBudgetRun, dif_pos h]

/-- Every supported accumulated cost of budgeted execution is at most its initial budget. -/
theorem weightedBudgetRun_bounded (next : S → PMF (O ⊕ S)) (c : S → ℕ)
    (B : ℕ) (cfg : O ⊕ S) : CostedLaw.BoundedBy (weightedBudgetRun next c B cfg) B := by
  induction B using Nat.strong_induction_on generalizing cfg with
  | h B ih =>
    cases cfg with
    | inl o => simp
    | inr s =>
      by_cases h : 0 < c s ∧ c s ≤ B
      · rw [weightedBudgetRun_paid next c B s h]
        intro z hz
        obtain ⟨d, _, hd⟩ := (PMF.mem_support_bind_iff _ _ _).mp hz
        have hb := (ih (B-c s) (by omega) d).charge (c s) z hd
        exact hb.trans (by omega)
      · rw [weightedBudgetRun_pending next c B s h]
        exact CostedLaw.boundedBy_ret _ _

/-- The extended nonnegative state charge, equal to zero for halted configurations and `c s` for
running states. -/
noncomputable def weightedStateCharge (c : S → ℕ) : O ⊕ S → ℝ≥0∞
  | .inl _ => 0
  | .inr s => c s

/-- The expected cost of a weighted tick equals the charge of its starting configuration. -/
theorem weightedTick_expectedCost (next : S → PMF (O ⊕ S)) (c : S → ℕ)
    (cfg : O ⊕ S) : CostedLaw.expectedCost (weightedTick next c cfg) = weightedStateCharge c cfg := by
  cases cfg with
  | inl o => exact CostedLaw.expectedCost_ret _
  | inr s => simp [weightedTick, weightedStateCharge, CostedLaw.expectedCost]

/-- Weighted occupation is the expectation of `weightedStateCharge` under the finite-run
configuration marginal. -/
theorem weightedOccupation_eq_expectation (next : S → PMF (O ⊕ S)) (c : S → ℕ)
    (cfg : O ⊕ S) (n : ℕ) :
    weightedOccupation next c cfg n = CostedLaw.expectation
      ((RandomizedExecution.runFor next n cfg).map Prod.fst) (weightedStateCharge c) := by
  unfold weightedOccupation CostedLaw.expectation
  rw [tsum_sum_type']
  simp [weightedStateCharge, tsum_fintype]

/-- The expected cost of one additional weighted step equals the previous expected cost plus the
weighted occupation at that time. -/
theorem weightedRunFor_expectedCost_succ (next : S → PMF (O ⊕ S)) (c : S → ℕ)
    (cfg : O ⊕ S) (n : ℕ) :
    CostedLaw.expectedCost (weightedRunFor next c (n+1) cfg) =
      CostedLaw.expectedCost (weightedRunFor next c n cfg) + weightedOccupation next c cfg n := by
  rw [weightedRunFor_add, CostedLaw.expectedCost_bind]
  congr 1
  simp only [weightedRunFor, CostedLaw.bind_ret, weightedTick_expectedCost]
  rw [← CostedLaw.expectation_map _ Prod.fst, weightedRunFor_marginal,
    weightedOccupation_eq_expectation]

/-- The expected cost of a finite weighted run is the sum of its weighted occupations before the
fuel cutoff. -/
theorem weightedRunFor_expectedCost (next : S → PMF (O ⊕ S)) (c : S → ℕ)
    (cfg : O ⊕ S) (n : ℕ) :
    CostedLaw.expectedCost (weightedRunFor next c n cfg) =
      ∑ i ∈ Finset.range n, weightedOccupation next c cfg i := by
  induction n with
  | zero => simp
  | succ n ih => rw [weightedRunFor_expectedCost_succ, ih, Finset.sum_range_succ]

/-- The unbounded expected weighted cost is the supremum of the finite weighted-run expected
costs. -/
theorem weightedExpectedCost_eq_iSup (next : S → PMF (O ⊕ S)) (c : S → ℕ)
    (cfg : O ⊕ S) :
    weightedExpectedCost next c cfg = ⨆ n, CostedLaw.expectedCost (weightedRunFor next c n cfg) := by
  simp_rw [weightedRunFor_expectedCost]
  exact ENNReal.tsum_eq_iSup_nat

/-- The pending mass is the sum of the running-state marginal probabilities. -/
theorem pendingMass_eq_marginal_sum (next : S → PMF (O ⊕ S)) (cfg : O ⊕ S) (n : ℕ) :
    pendingMass next cfg n = ∑ s, (RandomizedExecution.runFor next n cfg).map Prod.fst (.inr s) := by
  rw [pendingMass_eq_finiteSurvival]
  change CostedLaw.event (RandomizedExecution.runFor next n cfg)
    (fun z => ∃ s, z.1 = Sum.inr s) = _
  rw [← CostedLaw.event_map _ Prod.fst (fun d => ∃ s, d = Sum.inr s)]
  unfold CostedLaw.event CostedLaw.expectation
  rw [tsum_sum_type']
  simp [tsum_fintype]

/-- With constant unit costs, expected weighted cost equals the unbounded expected running time. -/
theorem weightedExpectedCost_unit_cost (next : S → PMF (O ⊕ S)) (cfg : O ⊕ S) :
    weightedExpectedCost next (fun _ => 1) cfg = unboundedTime next cfg := by
  apply tsum_congr
  intro n
  unfold weightedOccupation
  simp only [Nat.cast_one, mul_one]
  exact (pendingMass_eq_marginal_sum next cfg n).symm

/-- When state costs lie between one and `C`, weighted occupation lies between pending mass and
`C` times pending mass. -/
theorem weightedOccupation_bounds (next : S → PMF (O ⊕ S)) (c : S → ℕ)
    (cfg : O ⊕ S) (n C : ℕ) (hc : ∀ s, 1 ≤ c s ∧ c s ≤ C) :
    pendingMass next cfg n ≤ weightedOccupation next c cfg n ∧
      weightedOccupation next c cfg n ≤ (C : ℝ≥0∞) * pendingMass next cfg n := by
  rw [pendingMass_eq_marginal_sum]
  unfold weightedOccupation
  constructor
  · apply Finset.sum_le_sum
    intro s _
    calc
      _ = (RandomizedExecution.runFor next n cfg).map Prod.fst (.inr s) * 1 := (mul_one _).symm
      _ ≤ _ := mul_le_mul_right (by exact_mod_cast (hc s).1) _
  · rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro s _
    rw [mul_comm (C : ℝ≥0∞)]
    exact mul_le_mul_right (by exact_mod_cast (hc s).2) _

/-- If every state costs at least one, expected running time is at most expected weighted cost. -/
theorem unboundedTime_le_weightedExpectedCost (next : S → PMF (O ⊕ S)) (c : S → ℕ)
    (cfg : O ⊕ S) (hc : ∀ s, 1 ≤ c s) :
    unboundedTime next cfg ≤ weightedExpectedCost next c cfg := by
  apply ENNReal.tsum_le_tsum
  intro n
  rw [pendingMass_eq_marginal_sum]
  unfold weightedOccupation
  apply Finset.sum_le_sum
  intro s _
  calc
    _ = (RandomizedExecution.runFor next n cfg).map Prod.fst (.inr s) * 1 := (mul_one _).symm
    _ ≤ _ := mul_le_mul_right (by exact_mod_cast hc s) _

/-- Under costs at least one, finite expected weighted cost implies zero nontermination mass. -/
theorem weightedExpectedCost_finite_nontermination (next : S → PMF (O ⊕ S)) (c : S → ℕ)
    (cfg : O ⊕ S) (hc : ∀ s, 1 ≤ c s) (h : weightedExpectedCost next c cfg < ⊤) :
    nonterminationMass next cfg = 0 :=
  (unbounded_expected_time_tail_sum next cfg).2.2
    (lt_of_le_of_lt (unboundedTime_le_weightedExpectedCost next c cfg hc) h)

/-- If state costs lie between one and `C`, expected weighted cost is at most `C` times expected
running time. -/
theorem weightedExpectedCost_le_charge_time (next : S → PMF (O ⊕ S)) (c : S → ℕ)
    (cfg : O ⊕ S) (C : ℕ) (hc : ∀ s, 1 ≤ c s ∧ c s ≤ C) :
    weightedExpectedCost next c cfg ≤ (C : ℝ≥0∞) * unboundedTime next cfg := by
  change (∑' n, weightedOccupation next c cfg n) ≤ (C : ℝ≥0∞) * ∑' n, pendingMass next cfg n
  rw [← ENNReal.tsum_mul_left]
  exact ENNReal.tsum_le_tsum fun n => (weightedOccupation_bounds next c cfg n C hc).2

/-- Costs between one and `C` and a uniform continuation bound `q < 1` give zero nontermination
mass and expected cost at most `C / (1 - q)`. -/
theorem weighted_bounded_charge_geometric_consumer :
    ∀ (S O : Type) [Fintype S] [DecidableEq S] [Fintype O] [DecidableEq O]
      (next : S → PMF (O ⊕ S)) (c : S → ℕ) (s : S) (C : ℕ) (q : ℝ≥0∞),
      (∀ s, 1 ≤ c s ∧ c s ≤ C) → q < 1 →
      (∀ x, ∑ y : S, next x (.inr y) ≤ q) →
      nonterminationMass next (.inr s) = 0 ∧
        weightedExpectedCost next c (.inr s) ≤ (C : ℝ≥0∞) / (1-q) := by
  intro S O _ _ _ _ next c s C q hc hq hstep
  have hg := unbounded_geometric_kernel_runtime next s q hq hstep
  refine ⟨hg.2.1, ?_⟩
  calc
    weightedExpectedCost next c (.inr s) ≤ (C : ℝ≥0∞) * unboundedTime next (.inr s) :=
      weightedExpectedCost_le_charge_time next c (.inr s) C hc
    _ ≤ (C : ℝ≥0∞) * (1-q)⁻¹ := mul_le_mul_right hg.2.2 _
    _ = _ := rfl

/-- Under positive state costs, the budgeted mass of a halted pair with cost at most the budget
equals its weighted halting joint mass. -/
theorem weightedBudgetRun_halt_point (next : S → PMF (O ⊕ S)) (c : S → ℕ)
    (hc : ∀ s, 1 ≤ c s) (cfg : O ⊕ S) (o : O) (k B : ℕ) (hk : k ≤ B) :
    weightedBudgetRun next c B cfg (.inl o,k) = weightedHaltJoint next c cfg o k := by
  induction k using Nat.strong_induction_on generalizing B cfg with
  | h k ih =>
    cases cfg with
    | inl a => simp [weightedHaltJoint, CostedLaw.ret]
    | inr s =>
      by_cases hb : 0 < c s ∧ c s ≤ B
      · rw [weightedBudgetRun_paid next c B s hb, PMF.bind_apply]
        simp only [charge_point_mass]
        by_cases hcs : c s ≤ k
        · simp only [if_pos hcs]
          have hsmall : k-c s < k := by have := hc s; omega
          have hB : k-c s ≤ B-c s := by omega
          simp_rw [ih (k-c s) hsmall _ _ hB]
          obtain ⟨n, rfl⟩ : ∃ n, k = n+1 := ⟨k-1, by have := hc s; omega⟩
          unfold weightedHaltJoint
          rw [weightedRunFor_succ_running_point, if_pos hcs]
          apply tsum_congr
          intro d
          rw [weightedRunFor_halt_stable next c hc d o _ n (by have := hc s; omega)]
          rfl
        · simp only [if_neg hcs, mul_zero, tsum_zero]
          unfold weightedHaltJoint
          cases k with
          | zero => simp [CostedLaw.ret, PMF.pure_apply]
          | succ n => rw [weightedRunFor_succ_running_point, if_neg hcs]
      · rw [weightedBudgetRun_pending next c B s hb]
        have hcs : ¬ c s ≤ k := by have := hc s; omega
        unfold weightedHaltJoint
        cases k with
        | zero => rfl
        | succ n =>
          rw [weightedRunFor_succ_running_point, if_neg hcs]
          simp [CostedLaw.ret, PMF.pure_apply]

/-- The accumulated cost on halted outcomes, extended by zero on running outcomes. -/
noncomputable def weightedHaltedCharge : (O ⊕ S) × ℕ → ℝ≥0∞
  | (.inl _, k) => k
  | (.inr _, _) => 0

/-- The extended nonnegative indicator of a running configuration in a costed outcome. -/
noncomputable def weightedPendingIndicator : (O ⊕ S) × ℕ → ℝ≥0∞
  | (.inl _, _) => 0
  | (.inr _, _) => 1

/-- The expectation of the pending indicator equals the running-event probability. -/
theorem weightedPendingIndicator_expectation (p : CostedLaw (O ⊕ S)) :
    CostedLaw.expectation p weightedPendingIndicator =
      CostedLaw.event p (fun z => ∃ s, z.1 = Sum.inr s) := by
  apply CostedLaw.expectation_congr
  intro z
  rcases z with ⟨d,k⟩
  cases d <;> simp [weightedPendingIndicator]

/-- The expected halted charge is the sum of halted point masses weighted by their cost
coordinates. -/
theorem weightedHaltedCharge_expectation (p : CostedLaw (O ⊕ S)) :
    CostedLaw.expectation p weightedHaltedCharge = ∑' o, ∑' k : ℕ, (k : ℝ≥0∞) * p (.inl o,k) := by
  unfold CostedLaw.expectation
  rw [tsum_prod_type', tsum_sum_type']
  simp [weightedHaltedCharge, mul_comm]

/-- For a prefix bounded by `D`, its expected cost is at most the continuation's expected halted
charge plus `D` times its pending probability. -/
theorem weighted_prefix_expense_le (p : CostedLaw (O ⊕ S)) (f : O ⊕ S → CostedLaw (O ⊕ S))
    (D : ℕ) (hp : CostedLaw.BoundedBy p D) :
    CostedLaw.expectedCost p ≤ CostedLaw.expectation (CostedLaw.bind p f) weightedHaltedCharge +
      (D : ℝ≥0∞) * CostedLaw.event (CostedLaw.bind p f) (fun z => ∃ s, z.1 = Sum.inr s) := by
  have hm : CostedLaw.expectation (CostedLaw.bind p f)
      (fun z => (D : ℝ≥0∞) * weightedPendingIndicator z) =
      (D : ℝ≥0∞) * CostedLaw.expectation (CostedLaw.bind p f) weightedPendingIndicator := by
    unfold CostedLaw.expectation
    rw [← ENNReal.tsum_mul_left]
    apply tsum_congr
    intro z
    dsimp
    ac_rfl
  rw [← weightedPendingIndicator_expectation, ← hm, ← CostedLaw.expectation_add,
    CostedLaw.bind, CostedLaw.expectation_bind]
  change (∑' x, p x * (x.2 : ℝ≥0∞)) ≤ ∑' x, p x * CostedLaw.expectation
    (CostedLaw.charge x.2 (f x.1)) (fun z => weightedHaltedCharge z + (D : ℝ≥0∞) * weightedPendingIndicator z)
  apply ENNReal.tsum_le_tsum
  intro x
  by_cases hx : p x = 0
  · simp [hx]
  · apply mul_le_mul_right
    rw [CostedLaw.charge, CostedLaw.expectation_map]
    have hd : x.2 ≤ D := hp x ((PMF.mem_support_iff _ _).mpr hx)
    rw [← CostedLaw.expectation_const (f x.1) (x.2 : ℝ≥0∞)]
    apply CostedLaw.expectation_le_of_forall
    intro y
    rcases y with ⟨d,k⟩
    cases d with
    | inl o => simp [weightedHaltedCharge, weightedPendingIndicator, Nat.cast_add]
    | inr s => simpa [weightedHaltedCharge, weightedPendingIndicator] using
        (show (x.2 : ℝ≥0∞) ≤ (D : ℝ≥0∞) by exact_mod_cast hd)

/-- If every state cost is at most `C`, an `n`-step weighted run has accumulated cost at most `n
* C`. -/
theorem weightedRunFor_bounded (next : S → PMF (O ⊕ S)) (c : S → ℕ)
    (C : ℕ) (hc : ∀ s, c s ≤ C) (n : ℕ) (cfg : O ⊕ S) :
    CostedLaw.BoundedBy (weightedRunFor next c n cfg) (n*C) := by
  induction n generalizing cfg with
  | zero => simp
  | succ n ih =>
    have ht : CostedLaw.BoundedBy (weightedTick next c cfg) C := by
      cases cfg with
      | inl o => exact CostedLaw.boundedBy_ret _ _
      | inr s =>
        intro z hz
        obtain ⟨d, _, rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp hz
        exact hc s
    simpa [weightedRunFor, Nat.add_mul, Nat.add_comm] using ht.bind ih

/-- With positive state costs, the supremum of finite expected halted charges equals the
cost-weighted eventual halting joint mass. -/
theorem weightedHaltedCharge_iSup (next : S → PMF (O ⊕ S)) (c : S → ℕ)
    (hc : ∀ s, 1 ≤ c s) (cfg : O ⊕ S) :
    (⨆ n, CostedLaw.expectation (weightedRunFor next c n cfg) weightedHaltedCharge) =
      ∑' o, ∑' k : ℕ, (k : ℝ≥0∞) * weightedHaltJoint next c cfg o k := by
  simp_rw [weightedHaltedCharge_expectation]
  have hm : ∀ o, Monotone (fun n => ∑' k : ℕ, (k : ℝ≥0∞) * weightedRunFor next c n cfg (.inl o,k)) := by
    intro o n m h
    exact ENNReal.tsum_le_tsum fun k =>
      mul_le_mul_right (weightedRunFor_halt_monotone next c cfg o k h) _
  rw [← weighted_tsum_iSup _ hm]
  apply tsum_congr
  intro o
  rw [← weighted_tsum_iSup _ (fun k => by
    intro n m h
    exact mul_le_mul_right (weightedRunFor_halt_monotone next c cfg o k h) _)]
  apply tsum_congr
  intro k
  rw [← ENNReal.mul_iSup, weightedRunFor_halt_iSup next c hc cfg o k]

set_option maxHeartbeats 800000 in

/-- With positive state costs and zero nontermination mass, expected weighted cost equals the
cost-weighted halting joint mass. -/
theorem weightedExpectedCost_eq_halt_of_nontermination_zero (next : S → PMF (O ⊕ S))
    (c : S → ℕ) (hc : ∀ s, 1 ≤ c s) (cfg : O ⊕ S)
    (hzero : nonterminationMass next cfg = 0) :
    weightedExpectedCost next c cfg = ∑' o, ∑' k : ℕ, (k : ℝ≥0∞) * weightedHaltJoint next c cfg o k := by
  let H : ℝ≥0∞ := ∑' o, ∑' k : ℕ, (k : ℝ≥0∞) * weightedHaltJoint next c cfg o k
  have hsup := weightedHaltedCharge_iSup next c hc cfg
  apply le_antisymm
  · rw [weightedExpectedCost_eq_iSup]
    apply iSup_le
    intro n
    let C : ℕ := ∑ s, c s
    have hcC : ∀ s, c s ≤ C :=
        fun s => Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ s)
    have hpre (m : ℕ) : CostedLaw.expectedCost (weightedRunFor next c n cfg) ≤
        H + ((n*C : ℕ) : ℝ≥0∞) * pendingMass next cfg (n+m) := by
      have h := weighted_prefix_expense_le (weightedRunFor next c n cfg)
        (weightedRunFor next c m) (n*C) (weightedRunFor_bounded next c C hcC n cfg)
      rw [← weightedRunFor_add, weightedRunFor_pending] at h
      have hle : CostedLaw.expectation (weightedRunFor next c (n+m) cfg) weightedHaltedCharge ≤ H := by
        change _ ≤ ∑' o, ∑' k : ℕ, (k : ℝ≥0∞) * weightedHaltJoint next c cfg o k
        rw [← hsup]
        exact le_iSup
            (fun j : ℕ => CostedLaw.expectation (weightedRunFor next c j cfg) weightedHaltedCharge)
            (n+m)
      exact h.trans (add_le_add hle le_rfl)
    have ht := (pendingMass_tendsto_iInf next cfg).comp
      (show Filter.Tendsto (fun m : ℕ => n+m) Filter.atTop Filter.atTop from
        by simpa [Nat.add_comm] using (Filter.tendsto_add_atTop_nat n))
    rw [hzero] at ht
    have ht' :=
        (tendsto_const_nhds (x := H) (f := (Filter.atTop : Filter ℕ))).add
        (ENNReal.Tendsto.const_mul ht (Or.inr (ENNReal.natCast_ne_top (n*C))))
    have htH : Filter.Tendsto (fun m => H + ((n*C : ℕ) : ℝ≥0∞) * pendingMass next cfg (n+m))
        Filter.atTop (nhds H) := by simpa using ht'
    exact ge_of_tendsto' htH hpre
  · rw [← hsup, weightedExpectedCost_eq_iSup]
    apply iSup_mono
    intro n
    apply CostedLaw.expectation_le_of_forall
    intro z
    rcases z with ⟨d,k⟩
    cases d <;> simp [weightedHaltedCharge]

/-- With positive state costs, expected weighted cost equals the cost-weighted halting mass plus
`⊤` times nontermination mass; finite expectation forces zero nontermination mass. -/
theorem weighted_expected_cost_occupation_and_halt :
    ∀ (S O : Type) [Fintype S] [DecidableEq S] [Fintype O] [DecidableEq O]
      (next : S → PMF (O ⊕ S)) (c : S → ℕ) (cfg : O ⊕ S), (∀ s, 1 ≤ c s) →
      weightedExpectedCost next c cfg =
        (∑' o, ∑' k : ℕ, (k : ℝ≥0∞) * weightedHaltJoint next c cfg o k) +
          (⊤ : ℝ≥0∞) * nonterminationMass next cfg ∧
      (weightedExpectedCost next c cfg < ⊤ → nonterminationMass next cfg = 0) := by
  intro S O _ _ _ _ next c cfg hc
  refine ⟨?_, weightedExpectedCost_finite_nontermination next c cfg hc⟩
  by_cases hz : nonterminationMass next cfg = 0
  · simpa [hz] using weightedExpectedCost_eq_halt_of_nontermination_zero next c hc cfg hz
  · have ht : weightedExpectedCost next c cfg = ⊤ := by
      by_contra h
      exact hz (weightedExpectedCost_finite_nontermination next c cfg hc (lt_top_iff_ne_top.mpr h))
    simp [ht, ENNReal.top_mul hz]

/-- For any costed law, total halted mass plus running-event probability equals one. -/
theorem weighted_law_halt_pending_partition (p : CostedLaw (O ⊕ S)) :
    (∑' o, ∑' k : ℕ, p (.inl o,k)) +
      CostedLaw.event p (fun z => ∃ s, z.1 = Sum.inr s) = 1 := by
  have he : CostedLaw.event p (fun z => ∃ s, z.1 = Sum.inr s) =
      ∑' s, ∑' k : ℕ, p (.inr s,k) := by
    unfold CostedLaw.event CostedLaw.expectation
    rw [tsum_prod_type', tsum_sum_type']
    simp
  rw [he, ← tsum_sum_type' (F := fun d : O ⊕ S => ∑' k : ℕ, p (d,k)),
    ← tsum_prod_type' (F := fun z : (O ⊕ S) × ℕ => p z), PMF.tsum_coe]

/-- With positive state costs, halted joint masses through the budget plus the budgeted pending
probability sum to one. -/
theorem weightedBudgetRun_partition (next : S → PMF (O ⊕ S)) (c : S → ℕ)
    (hc : ∀ s, 1 ≤ c s) (cfg : O ⊕ S) (B : ℕ) :
    (∑ o, ∑ k ∈ Finset.range (B+1), weightedHaltJoint next c cfg o k) +
      CostedLaw.event (weightedBudgetRun next c B cfg) (fun z => ∃ s, z.1 = Sum.inr s) = 1 := by
  have hp := weighted_law_halt_pending_partition (weightedBudgetRun next c B cfg)
  have hh (o : O) : (∑' k : ℕ, weightedBudgetRun next c B cfg (.inl o,k)) =
      ∑ k ∈ Finset.range (B+1), weightedHaltJoint next c cfg o k := by
    rw [tsum_eq_sum (s := Finset.range (B+1)) (fun k hk => ?_)]
    · apply Finset.sum_congr rfl
      intro k hk
      exact weightedBudgetRun_halt_point next c hc cfg o k B (by simpa using Finset.mem_range.mp hk)
    · have hkB : B < k := by have := Finset.mem_range.not.mp hk; omega
      by_contra hz
      have hb :=
          weightedBudgetRun_bounded next c B cfg (.inl o,k) ((PMF.mem_support_iff _ _).mpr hz)
      omega
  simp_rw [hh, tsum_fintype] at hp
  exact hp

/-- Total weighted halting mass splits into cost coordinates at most `B` and those greater than
`B`. -/
theorem weightedHaltJoint_tsum_split (next : S → PMF (O ⊕ S)) (c : S → ℕ)
    (cfg : O ⊕ S) (B : ℕ) :
    (∑' o, ∑' k : ℕ, weightedHaltJoint next c cfg o k) =
      (∑ o, ∑ k ∈ Finset.range (B+1), weightedHaltJoint next c cfg o k) +
      ∑' o, ∑' k : ℕ, weightedHaltJoint next c cfg o k * (if B < k then 1 else 0) := by
  have hk (o : O) : (∑' k : ℕ, weightedHaltJoint next c cfg o k) =
      (∑ k ∈ Finset.range (B+1), weightedHaltJoint next c cfg o k) +
      ∑' k : ℕ, weightedHaltJoint next c cfg o k * (if B < k then 1 else 0) := by
    have hpoint (k : ℕ) : weightedHaltJoint next c cfg o k =
        (if k < B+1 then weightedHaltJoint next c cfg o k else 0) +
        weightedHaltJoint next c cfg o k * (if B < k then 1 else 0) := by
      by_cases h : B < k <;> simp [h, show (k < B+1) ↔ ¬ B < k by omega]
    rw [tsum_congr hpoint, ENNReal.tsum_add]
    congr 1
    rw [tsum_eq_sum (s := Finset.range (B+1)) (fun k hk => if_neg (Finset.mem_range.not.mp hk))]
    apply Finset.sum_congr rfl
    intro k hk
    exact if_pos (Finset.mem_range.mp hk)
  simp_rw [hk]
  rw [ENNReal.tsum_add, tsum_fintype]

/-- With positive state costs, budgeted pending probability equals the halting-cost tail beyond
the budget plus nontermination mass. -/
theorem weightedBudgetRun_pending_tail (next : S → PMF (O ⊕ S)) (c : S → ℕ)
    (hc : ∀ s, 1 ≤ c s) (cfg : O ⊕ S) (B : ℕ) :
    CostedLaw.event (weightedBudgetRun next c B cfg) (fun z => ∃ s, z.1 = Sum.inr s) =
      (∑' o, ∑' k : ℕ, weightedHaltJoint next c cfg o k * (if B < k then 1 else 0)) +
      nonterminationMass next cfg := by
  have hpart := weightedBudgetRun_partition next c hc cfg B
  have htotal := (weighted_first_halt_stable_and_total_partition S O next c cfg hc).2
  rw [weightedHaltJoint_tsum_split, add_assoc] at htotal
  have hfinite : (∑ o, ∑ k ∈ Finset.range (B+1), weightedHaltJoint next c cfg o k) ≠ ⊤ := by
    apply ne_top_of_le_ne_top (by simp : (1 : ℝ≥0∞) ≠ ⊤)
    calc
      _ ≤ _ + CostedLaw.event (weightedBudgetRun next c B cfg) (fun z => ∃ s, z.1 = Sum.inr s) := le_self_add
      _ = 1 := hpart
  exact WithTop.add_left_cancel hfinite (hpart.trans htotal.symm)

/-- With positive state costs, the budgeted pending probability is at most expected weighted
cost divided by `B + 1`. -/
theorem weightedBudgetRun_cutoff (next : S → PMF (O ⊕ S)) (c : S → ℕ)
    (hc : ∀ s, 1 ≤ c s) (cfg : O ⊕ S) (B : ℕ) :
    CostedLaw.event (weightedBudgetRun next c B cfg) (fun z => ∃ s, z.1 = Sum.inr s) ≤
      weightedExpectedCost next c cfg / (B+1 : ℝ≥0∞) := by
  have hmul : (B+1 : ℝ≥0∞) *
      CostedLaw.event (weightedBudgetRun next c B cfg) (fun z => ∃ s, z.1 = Sum.inr s) ≤
      weightedExpectedCost next c cfg := by
    rw [weightedBudgetRun_pending_tail next c hc,
      (weighted_expected_cost_occupation_and_halt S O next c cfg hc).1, mul_add]
    apply add_le_add
    · simp_rw [← ENNReal.tsum_mul_left]
      apply ENNReal.tsum_le_tsum
      intro o
      apply ENNReal.tsum_le_tsum
      intro k
      by_cases hk : B < k
      · simp only [if_pos hk, mul_one]
        exact mul_le_mul_left (by exact_mod_cast Nat.succ_le_of_lt hk) _
      · simp [hk]
    · exact mul_le_mul_left le_top _
  exact (ENNReal.le_div_iff_mul_le (by simp) (by simp)).mpr (by simpa [mul_comm] using hmul)

/-- With positive state costs, online budget execution respects the budget, preserves every
halted joint mass within it, and satisfies the expected-cost cutoff bound. -/
theorem weighted_online_budget_joint_prefix_and_cutoff :
    ∀ (S O : Type) [Fintype S] [DecidableEq S] [Fintype O] [DecidableEq O]
      (next : S → PMF (O ⊕ S)) (c : S → ℕ) (cfg : O ⊕ S) (B : ℕ),
      (∀ s, 1 ≤ c s) → CostedLaw.BoundedBy (weightedBudgetRun next c B cfg) B ∧
      (∀ o k, k ≤ B → weightedBudgetRun next c B cfg (.inl o,k) = weightedHaltJoint next c cfg o k) ∧
      CostedLaw.event (weightedBudgetRun next c B cfg) (fun z => ∃ s, z.1 = Sum.inr s) ≤
        weightedExpectedCost next c cfg / (B+1 : ℝ≥0∞) := by
  intro S O _ _ _ _ next c cfg B hc
  exact ⟨weightedBudgetRun_bounded next c B cfg,
    fun o k hk => weightedBudgetRun_halt_point next c hc cfg o k B hk,
    weightedBudgetRun_cutoff next c hc cfg B⟩

end Qatlib.Concepts.StoppingCore.InterruptBridge
