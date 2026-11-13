/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.StoppingCore.BranchCostCore.WeightedUnboundedExecution
import Qatlib.Concepts.StoppingCore.BranchCostCore.GeneralUnboundedExecution

/-!
# Unit-time clocks for state-dependent costs

`costClockEmbed` and `costClockNext` compile a state-dependent natural cost into a unit-time
countdown. For positive costs, one macro step takes exactly the prescribed charge and the
compiled joint halting law agrees with `weightedRunFor`.

The module relates weighted and unweighted configuration marginals, proves preservation of
nontermination mass, and gives expected-charge and arbitrary-output-event cutoff formulas for
the compiled clock. For background, see [Ambainis2012].

## Main statements

* `cost_clock_macro_step_exact_charge`: identifies one weighted transition with its exact-length
  clock execution.
* `cost_clock_nontermination_and_weighted_partition`: preserves nontermination mass and
  normalizes the weighted halting law.
* `cost_clock_arbitrary_output_event_cutoff`: bounds eventual event mass by finite-budget event
  mass and an expected-time remainder.

## References

* [Ambainis, 2012][Ambainis2012]
-/

open Qatlib.Concepts.AEMeanReadout.LocalAEBackend.CostedLaw
open Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw

open Qatlib.Concepts.AEMeanReadout.LocalAEBackend
open Qatlib.Concepts.LinearLearning.ConcisePipeline
open Qatlib.Concepts.StoppingCore.BranchCostCore.GeneralExecution

set_option autoImplicit false
namespace Qatlib.Concepts.StoppingCore.BranchCostCore
open Qatlib.Concepts.AEMeanReadout.LocalAEBackend.RandomizedExecution
open scoped Classical BigOperators ENNReal

/-- Embed a configuration into a countdown clock, assigning a running state the remaining
counter `c s - 1` and preserving halted outputs. -/
def costClockEmbed {S O : Type} (c : S → ℕ) : O ⊕ S → O ⊕ (S × ℕ)
  | .inl o => .inl o
  | .inr s => .inr (s, c s - 1)

/-- Decrement a positive countdown; at zero, sample an original transition and embed its
successor with its next state-dependent counter. -/
noncomputable def costClockNext {S O : Type} (next : S → PMF (O ⊕ S))
    (c : S → ℕ) (sd : S × ℕ) : PMF (O ⊕ (S × ℕ)) :=
  if sd.2 = 0 then (next sd.1).map (costClockEmbed c)
  else PMF.pure (.inr (sd.1, sd.2-1))

variable {S O : Type}

/-- A weighted run from a halted output remains at that output with zero cost. -/
@[simp] theorem costClock_weighted_halted (next : S → PMF (O ⊕ S)) (c : S → ℕ)
    (fuel : ℕ) (o : O) :
    weightedRunFor next c fuel (.inl o) = CostedLaw.ret (.inl o) := by
  induction fuel with
  | zero => rfl
  | succ fuel ih => simpa [weightedRunFor, weightedTick] using ih

/-- A weighted run with combined transition fuel equals the cost-accumulating composition of the
two successive runs. -/
theorem costClock_weighted_add (next : S → PMF (O ⊕ S)) (c : S → ℕ)
    (m n : ℕ) (cfg : O ⊕ S) :
    weightedRunFor next c (m + n) cfg =
      CostedLaw.bind (weightedRunFor next c m cfg) (weightedRunFor next c n) := by
  induction m generalizing cfg with
  | zero => simp
  | succ m ih =>
    rw [Nat.succ_add, weightedRunFor, weightedRunFor, CostedLaw.bind_assoc]
    congr 1
    funext x
    exact ih x

/-- Forgetting recorded costs gives the same configuration marginal for weighted and unit-cost
runs with the same transition fuel. -/
theorem costClock_weighted_marginal (next : S → PMF (O ⊕ S)) (c : S → ℕ)
    (n : ℕ) (cfg : O ⊕ S) :
    (weightedRunFor next c n cfg).map Prod.fst =
      (RandomizedExecution.runFor next n cfg).map Prod.fst := by
  induction n generalizing cfg with
  | zero => rfl
  | succ n ih =>
    simp only [weightedRunFor, RandomizedExecution.runFor, costedLaw_map_fst_bind, ih]
    congr 1
    cases cfg <;>
      simp [weightedTick, RandomizedExecution.tick, PMF.map_comp, Function.comp_def]

/-- A weighted run from a running state samples one successor, charges the current state cost,
and continues for the remaining transition fuel. -/
theorem costClock_weighted_succ (next : S → PMF (O ⊕ S)) (c : S → ℕ)
    (n : ℕ) (s : S) :
    weightedRunFor next c (n+1) (.inr s) =
      (next s).bind (fun d => CostedLaw.charge (c s) (weightedRunFor next c n d)) := by
  simp [weightedRunFor, weightedTick, CostedLaw.bind, PMF.bind_map, Function.comp_def]

/-- A weighted joint point mass is zero when the requested cost is below the current charge;
otherwise it is the successor-weighted sum at the residual cost. -/
theorem costClock_weighted_point (next : S → PMF (O ⊕ S)) (c : S → ℕ)
    (n : ℕ) (s : S) (d : O ⊕ S) (k : ℕ) :
    weightedRunFor next c (n+1) (.inr s) (d,k) =
      if c s ≤ k then ∑' x, next s x * weightedRunFor next c n x (d,k-c s) else 0 := by
  rw [costClock_weighted_succ, PMF.bind_apply]
  simp only [GeneralExecution.charge_point_mass]
  split_ifs with h
  · rfl
  · simp

/-- If every state cost is at least one, a weighted halting point mass at cost `k` stabilizes to
`weightedHaltJoint` once transition fuel is at least `k`. -/
theorem costClock_weighted_stable (next : S → PMF (O ⊕ S)) (c : S → ℕ)
    (hc : ∀ s, 1 ≤ c s) (cfg : O ⊕ S) (o : O) (k fuel : ℕ) (h : k ≤ fuel) :
    weightedRunFor next c fuel cfg (.inl o,k) = weightedHaltJoint next c cfg o k := by
  unfold weightedHaltJoint
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
          rw [costClock_weighted_point, ite_eq_right (by have := hc s; omega)]
          simp [CostedLaw.ret, PMF.pure_apply]
      | succ k =>
        obtain ⟨n, rfl⟩ : ∃ n, fuel = n+1 := ⟨fuel-1, by omega⟩
        rw [costClock_weighted_point, costClock_weighted_point]
        split_ifs with hcs
        · apply tsum_congr
          intro x
          rw [ih (k+1-c s) (by have := hc s; omega) x n (by have := hc s; omega),
            ih (k+1-c s) (by have := hc s; omega) x k (by have := hc s; omega)]
        · rfl

/-- At a fixed output and cost, weighted halting mass is monotone in transition fuel. -/
theorem costClock_weighted_monotone (next : S → PMF (O ⊕ S)) (c : S → ℕ)
    (cfg : O ⊕ S) (o : O) (k : ℕ) :
    Monotone (fun n => weightedRunFor next c n cfg (.inl o,k)) := by
  apply monotone_nat_of_le_succ
  intro n
  rw [show n+1 = n+1 from rfl, costClock_weighted_add, CostedLaw.bind, PMF.bind_apply]
  have h := ENNReal.le_tsum (f := fun x => weightedRunFor next c n cfg x *
    CostedLaw.charge x.2 (weightedRunFor next c 1 x.1) (.inl o,k)) (.inl o,k)
  simpa [costClock_weighted_halted, CostedLaw.charge_ret, PMF.pure_apply] using h

/-- For positive state costs, the supremum over transition fuel of a weighted halting point mass
is `weightedHaltJoint`. -/
theorem costClock_weighted_iSup (next : S → PMF (O ⊕ S)) (c : S → ℕ)
    (hc : ∀ s, 1 ≤ c s) (cfg : O ⊕ S) (o : O) (k : ℕ) :
    (⨆ n, weightedRunFor next c n cfg (.inl o,k)) = weightedHaltJoint next c cfg o k := by
  apply le_antisymm
  · apply iSup_le
    intro n
    calc
      weightedRunFor next c n cfg (.inl o,k) ≤
          weightedRunFor next c (max n k) cfg (.inl o,k) :=
        costClock_weighted_monotone next c cfg o k (le_max_left _ _)
      _ = _ := costClock_weighted_stable next c hc cfg o k _ (le_max_right _ _)
  · exact le_iSup (fun n => weightedRunFor next c n cfg (.inl o,k)) k

/-- The probability that a weighted run is still running equals the pending mass of the original
unit-cost execution with the same transition fuel. -/
theorem costClock_weighted_pending (next : S → PMF (O ⊕ S)) (c : S → ℕ)
    (cfg : O ⊕ S) (n : ℕ) :
    CostedLaw.event (weightedRunFor next c n cfg) (fun z => ∃ s, z.1 = Sum.inr s) =
      generalPendingMass next cfg n := by
  change _ = CostedLaw.event (RandomizedExecution.runFor next n cfg)
    (fun z => ∃ s, z.1 = Sum.inr s)
  rw [← CostedLaw.event_map _ Prod.fst (fun d => ∃ s, d = Sum.inr s),
    costClock_weighted_marginal, CostedLaw.event_map]

/-- The total weighted halted mass plus the original pending mass after the same transition fuel
is one. -/
theorem costClock_weighted_partition (next : S → PMF (O ⊕ S)) (c : S → ℕ)
    (cfg : O ⊕ S) (n : ℕ) :
    (∑' o, ∑' k, weightedRunFor next c n cfg (.inl o,k)) + generalPendingMass next cfg n = 1 := by
  rw [← costClock_weighted_pending next c cfg n]
  have he : CostedLaw.event (weightedRunFor next c n cfg)
      (fun z => ∃ s, z.1 = Sum.inr s) =
      ∑' s, ∑' k, weightedRunFor next c n cfg (.inr s,k) := by
    unfold CostedLaw.event CostedLaw.expectation
    rw [tsum_prod_type', tsum_sum_type']
    simp
  rw [he, ← tsum_sum_type' (F := fun d : O ⊕ S => ∑' k, weightedRunFor next c n cfg (d,k)),
    ← tsum_prod_type' (F := fun z : (O ⊕ S) × ℕ => weightedRunFor next c n cfg z), PMF.tsum_coe]

/-- A unit-cost run from a running state samples one successor, charges one, and executes the
remaining fuel. -/
theorem costClock_unit_succ (next : S → PMF (O ⊕ S)) (n : ℕ) (s : S) :
    runFor next (n+1) (.inr s) =
      (next s).bind (fun d => CostedLaw.charge 1 (runFor next n d)) := by
  simp [runFor, tick, CostedLaw.bind, PMF.bind_map, Function.comp_def]

/-- Starting at counter `d`, exactly `d + 1` clock steps sample one original successor, embed
it, and record cost `d + 1`. -/
theorem costClock_countdown (next : S → PMF (O ⊕ S)) (c : S → ℕ)
    (s : S) (d : ℕ) :
    runFor (costClockNext next c) (d+1) (.inr (s,d)) =
      (next s).map (fun x => (costClockEmbed c x,d+1)) := by
  induction d with
  | zero =>
    simp [runFor, tick, costClockNext, CostedLaw.bind, CostedLaw.ret,
      CostedLaw.charge, PMF.map, Function.comp_def]
  | succ d ih =>
    rw [costClock_unit_succ]
    simp only [costClockNext, Nat.succ_ne_zero, ite_false,
      Nat.add_sub_cancel, PMF.pure_bind, ih, CostedLaw.charge, PMF.map_comp, Function.comp_def]
    congr 1
    funext x
    simp
    omega

/-- For positive state costs, running the compiled clock for `c s` steps from embedded state `s`
exactly samples one original successor and records charge `c s`. -/
theorem cost_clock_macro_step_exact_charge :
    ∀ (S O : Type) (next : S → PMF (O ⊕ S)) (c : S → ℕ),
      (∀ s, 1 ≤ c s) → ∀ s : S,
      runFor (costClockNext next c) (c s) (costClockEmbed c (.inr s)) =
        (next s).map (fun d => (costClockEmbed c d,c s)) := by
  intro S O next c hc s
  have h := costClock_countdown next c s (c s-1)
  have he : c s-1+1 = c s := by have := hc s; omega
  simpa only [he, costClockEmbed] using h

/-- A prefix of at most `d` clock steps from counter `d` deterministically retains the current
state, subtracts the elapsed counter, and records that elapsed cost. -/
theorem costClock_countdown_prefix (next : S → PMF (O ⊕ S)) (c : S → ℕ)
    (s : S) (n d : ℕ) (hn : n ≤ d) :
    runFor (costClockNext next c) n (.inr (s,d)) = PMF.pure (.inr (s,d-n),n) := by
  induction n generalizing d with
  | zero => simp [runFor, CostedLaw.ret]
  | succ n ih =>
    rw [costClock_unit_succ]
    have hd : d ≠ 0 := by omega
    simp only [costClockNext, ite_eq_right hd, PMF.pure_bind]
    rw [ih (d-1) (by omega)]
    simp only [CostedLaw.charge, PMF.pure_map]
    congr 1
    apply Prod.ext
    · exact congrArg Sum.inr (Prod.ext rfl (by omega))
    · omega

/-- A clock run extending beyond the current countdown samples one successor, charges the
elapsed `d + 1` steps, and continues from its embedded configuration. -/
theorem costClock_countdown_resume (next : S → PMF (O ⊕ S)) (c : S → ℕ)
    (s : S) (d n : ℕ) :
    runFor (costClockNext next c) (d+1+n) (.inr (s,d)) =
      (next s).bind (fun x => CostedLaw.charge (d+1)
        (runFor (costClockNext next c) n (costClockEmbed c x))) := by
  rw [runFor_add, costClock_countdown]
  simp [CostedLaw.bind, PMF.bind_map, Function.comp_def]

/-- For positive cost at the starting state, compiled halting mass is zero below that cost and
otherwise satisfies the original successor recurrence with the cost subtracted from time. -/
theorem costClock_halt_running (next : S → PMF (O ⊕ S)) (c : S → ℕ)
    (s : S) (hc : 1 ≤ c s) (o : O) (k : ℕ) :
    haltJoint (costClockNext next c) (costClockEmbed c (.inr s)) o k =
      if c s ≤ k then ∑' x, next s x *
        haltJoint (costClockNext next c) (costClockEmbed c x) o (k-c s) else 0 := by
  by_cases hfit : c s ≤ k
  · rw [ite_eq_left hfit]
    unfold haltJoint
    have he := costClock_countdown_resume next c s (c s-1) (k-c s)
    have hp : c s-1+1 = c s := by omega
    have hk : c s-1+1+(k-c s) = k := by omega
    rw [hk] at he
    change runFor (costClockNext next c) k (.inr (s,c s-1)) (.inl o,k) = _
    rw [he, PMF.bind_apply]
    simp only [GeneralExecution.charge_point_mass, hp, ite_eq_left hfit]
  · rw [ite_eq_right hfit]
    unfold haltJoint
    change runFor (costClockNext next c) k (.inr (s,c s-1)) (.inl o,k) = 0
    rw [costClock_countdown_prefix next c s k (c s-1) (by omega)]
    simp [PMF.pure_apply]

/-- For positive state costs and transition fuel at least `k`, compiled-clock halting mass at
output `o` and time `k` equals the corresponding weighted-run point mass from any initial
configuration. -/
theorem cost_clock_arbitrary_configuration_halt_joint :
    ∀ (S O : Type) (next : S → PMF (O ⊕ S)) (c : S → ℕ),
      (∀ s, 1 ≤ c s) → ∀ (cfg : O ⊕ S) (o : O) (k fuel : ℕ), k ≤ fuel →
      haltJoint (costClockNext next c) (costClockEmbed c cfg) o k =
        weightedRunFor next c fuel cfg (.inl o,k) := by
  intro S O next c hc cfg o k fuel hf
  have bridge : ∀ k : ℕ, ∀ cfg : O ⊕ S,
      haltJoint (costClockNext next c) (costClockEmbed c cfg) o k =
        weightedRunFor next c k cfg (.inl o,k) := by
    intro k
    induction k using Nat.strong_induction_on with
    | h k ih =>
      intro cfg
      cases cfg with
      | inl a => simp only [costClockEmbed, haltJoint, runFor_halted, costClock_weighted_halted,
          CostedLaw.ret, PMF.pure_apply, Prod.mk.injEq, Sum.inl.injEq]
      | inr s =>
        cases k with
        | zero =>
          rw [costClock_halt_running next c s (hc s), ite_eq_right (by have := hc s; omega)]
          simp [weightedRunFor, CostedLaw.ret, PMF.pure_apply]
        | succ k =>
          rw [costClock_halt_running next c s (hc s), costClock_weighted_point]
          split_ifs with hfit
          · apply tsum_congr
            intro x
            rw [ih (k+1-c s) (by have := hc s; omega) x]
            rw [costClock_weighted_stable next c hc x o (k+1-c s) k (by have := hc s; omega)]
            rfl
          · rfl
  rw [bridge]
  exact (costClock_weighted_stable next c hc cfg o k fuel hf).symm

/-- For positive state costs, the sum of all weighted joint halting masses plus the original
nontermination mass is one. -/
theorem costClock_weighted_total (next : S → PMF (O ⊕ S)) (c : S → ℕ)
    (cfg : O ⊕ S) (hc : ∀ s, 1 ≤ c s) :
    (∑' o, ∑' k, weightedHaltJoint next c cfg o k) + generalNeverMass next cfg = 1 := by
  have hm : Monotone (fun n => ∑' o, ∑' k, weightedRunFor next c n cfg (.inl o,k)) := by
    intro n m h
    exact ENNReal.tsum_le_tsum fun o => ENNReal.tsum_le_tsum fun k =>
      costClock_weighted_monotone next c cfg o k h
  have hs : (⨆ n, ∑' o, ∑' k, weightedRunFor next c n cfg (.inl o,k)) =
      ∑' o, ∑' k, weightedHaltJoint next c cfg o k := by
    rw [← weighted_tsum_iSup _ (fun o => by
      intro n m h
      exact ENNReal.tsum_le_tsum fun k => costClock_weighted_monotone next c cfg o k h)]
    apply tsum_congr
    intro o
    rw [← weighted_tsum_iSup _ (fun k => costClock_weighted_monotone next c cfg o k)]
    exact tsum_congr fun k => costClock_weighted_iSup next c hc cfg o k
  have ht :=
      (tendsto_atTop_iSup hm).add
      (tendsto_atTop_iInf (general_unbounded_finite_partition_and_pending S O next cfg).1)
  rw [hs] at ht
  have hconst : Filter.Tendsto (fun _ : ℕ => (1 : ℝ≥0∞)) Filter.atTop
      (nhds ((∑' o, ∑' k, weightedHaltJoint next c cfg o k) + generalNeverMass next cfg)) :=
    ht.congr' (Filter.Eventually.of_forall fun n => costClock_weighted_partition next c cfg n)
  exact tendsto_nhds_unique hconst tendsto_const_nhds

/-- Positive state costs preserve nontermination mass under clock compilation, and the diagonal
weighted-run halting masses together with that mass sum to one. -/
theorem cost_clock_nontermination_and_weighted_partition :
    ∀ (S O : Type) (next : S → PMF (O ⊕ S)) (c : S → ℕ),
      (∀ s, 1 ≤ c s) → ∀ cfg : O ⊕ S,
      generalNeverMass (costClockNext next c) (costClockEmbed c cfg) = generalNeverMass next cfg ∧
      ((∑' o : O, ∑' k : ℕ, weightedRunFor next c k cfg (.inl o,k)) +
        generalNeverMass next cfg = 1) := by
  intro S O next c hc cfg
  have hw := costClock_weighted_total next c cfg hc
  have hclock := general_haltJoint_tsum_add_never (costClockNext next c) (costClockEmbed c cfg)
  simp_rw [cost_clock_arbitrary_configuration_halt_joint S O next c hc cfg _ _ _ le_rfl] at hclock
  change (∑' o, ∑' k, weightedRunFor next c k cfg (.inl o,k)) + generalNeverMass next cfg = 1 at hw
  have hfinite : (∑' o, ∑' k, weightedRunFor next c k cfg (.inl o,k)) ≠ ⊤ :=
    ne_top_of_le_ne_top ENNReal.one_ne_top ((le_self_add).trans hw.le)
  exact ⟨WithTop.add_left_cancel hfinite (hclock.trans hw.symm), hw⟩

/-- For positive state costs, expected compiled-clock time is the cost-weighted diagonal halting
sum plus infinite cost times the original nontermination mass. Pending mass after budget `B`
is at most expected clock time divided by `B + 1`. -/
theorem cost_clock_expected_charge_and_online_cutoff :
    ∀ (S O : Type) (next : S → PMF (O ⊕ S)) (c : S → ℕ),
      (∀ s, 1 ≤ c s) → ∀ (cfg : O ⊕ S) (B : ℕ),
      generalUnboundedTime (costClockNext next c) (costClockEmbed c cfg) =
        (∑' o : O, ∑' k : ℕ, (k : ℝ≥0∞)*weightedRunFor next c k cfg (.inl o,k)) +
          ⊤ * generalNeverMass next cfg ∧
      generalPendingMass (costClockNext next c) (costClockEmbed c cfg) B ≤
        generalUnboundedTime (costClockNext next c) (costClockEmbed c cfg)/(B+1 : ℝ≥0∞) := by
  intro S O next c hc cfg B
  have he := (general_unbounded_actual_expected_time (S × ℕ) O
    (costClockNext next c) (costClockEmbed c cfg)).1
  simp_rw [cost_clock_arbitrary_configuration_halt_joint S O next c hc cfg _ _ _ le_rfl,
    (cost_clock_nontermination_and_weighted_partition S O next c hc cfg).1] at he
  exact ⟨he, (general_online_cutoff (costClockNext next c) (costClockEmbed c cfg) B).2⟩

/-- The event probability of a halted output satisfying `E` is the sum of joint masses over all
such outputs and all recorded costs. -/
theorem costClock_event_outputs (p : CostedLaw (O ⊕ S)) (E : O → Prop) :
    CostedLaw.event p (fun z => ∃ o, z.1 = .inl o ∧ E o) =
      ∑' o, if E o then ∑' k, p (.inl o,k) else 0 := by
  unfold CostedLaw.event CostedLaw.expectation
  rw [tsum_prod_type', tsum_sum_type']
  simp only [Sum.inl.injEq, exists_eq_left', Sum.inr_ne_inl, false_and,
    exists_false, ite_false, mul_zero, tsum_zero, add_zero]
  apply tsum_congr
  intro o
  by_cases h : E o <;> simp [h]

/-- The probability of an output event within budget `B` equals the sum of its joint halting
masses over times at most `B`. -/
theorem costClock_finite_event (next : S → PMF (O ⊕ S)) (cfg : O ⊕ S)
    (B : ℕ) (E : O → Prop) :
    CostedLaw.event (runFor next B cfg) (fun z => ∃ o, z.1 = .inl o ∧ E o) =
      ∑' o, if E o then ∑ k ∈ Finset.range (B+1), haltJoint next cfg o k else 0 := by
  rw [costClock_event_outputs]
  apply tsum_congr
  intro o
  by_cases h : E o
  · rw [ite_eq_left h, ite_eq_left h]
    refine (tsum_eq_sum (s := Finset.range (B+1)) (fun k hk => ?_)).trans ?_
    · exact GeneralExecution.runFor_point_cost_gt_fuel next B cfg (.inl o) k
        (by have := Finset.mem_range.not.mp hk; omega)
    · exact Finset.sum_congr rfl fun k hk =>
        GeneralExecution.runFor_point_halt_ge next cfg o B k
          (by have := Finset.mem_range.mp hk; omega)
  · simp only [ite_eq_right h]

/-- For any output predicate, its eventual halting mass is bounded by the finite-budget event
probability plus expected unbounded time divided by `B + 1`. -/
theorem costClock_general_event_cutoff (next : S → PMF (O ⊕ S)) (cfg : O ⊕ S)
    (B : ℕ) (E : O → Prop) :
    (∑' o, if E o then ∑' k, haltJoint next cfg o k else 0) ≤
      CostedLaw.event (runFor next B cfg) (fun z => ∃ o, z.1 = .inl o ∧ E o) +
        generalUnboundedTime next cfg/(B+1 : ℝ≥0∞) := by
  have hsplit : (∑' o, if E o then ∑' k, haltJoint next cfg o k else 0) =
      (∑' o, if E o then ∑ k ∈ Finset.range (B+1), haltJoint next cfg o k else 0) +
      ∑' o, if E o then ∑' k, haltJoint next cfg o k *
        (if B < k then (1:ℝ≥0∞) else 0) else 0 := by
    rw [← ENNReal.tsum_add]
    apply tsum_congr
    intro o
    by_cases h : E o
    · simp only [ite_eq_left h]
      exact general_haltJoint_tsum_split next cfg o B
    · simp [h]
  rw [hsplit, ← costClock_finite_event]
  apply add_le_add le_rfl
  calc
    _ ≤ ∑' o, ∑' k, haltJoint next cfg o k *
        (if B < k then (1:ℝ≥0∞) else 0) :=
      ENNReal.tsum_le_tsum (fun o => by by_cases h : E o <;> simp [h])
    _ ≤ generalPendingMass next cfg B := by
      rw [generalPendingMass_eq_tail_add_never]
      exact le_self_add
    _ ≤ _ := (general_online_cutoff next cfg B).2

/-- For positive state costs and any output predicate, eventual weighted event mass is bounded
by the compiled finite-budget event probability plus expected clock time divided by `B + 1`. -/
theorem cost_clock_arbitrary_output_event_cutoff :
    ∀ (S O : Type) (next : S → PMF (O ⊕ S)) (c : S → ℕ),
      (∀ s, 1 ≤ c s) → ∀ (cfg : O ⊕ S) (B : ℕ) (E : O → Prop),
      (∑' o : O, if E o then ∑' k : ℕ, weightedRunFor next c k cfg (.inl o,k) else 0) ≤
        CostedLaw.event (runFor (costClockNext next c) B (costClockEmbed c cfg))
          (fun z => ∃ o, z.1 = .inl o ∧ E o) +
        generalUnboundedTime (costClockNext next c) (costClockEmbed c cfg)/(B+1 : ℝ≥0∞) := by
  intro S O next c hc cfg B E
  have h := costClock_general_event_cutoff (costClockNext next c) (costClockEmbed c cfg) B E
  simp_rw [cost_clock_arbitrary_configuration_halt_joint S O next c hc cfg _ _ _ le_rfl] at h
  exact h

end Qatlib.Concepts.StoppingCore.BranchCostCore
