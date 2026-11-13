/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.StoppingCore.BranchCostCore.UnboundedFiniteExecution
import Qatlib.Concepts.AEMeanReadout.LocalAEBackend.RandomizedExecution
import Qatlib.Concepts.LinearLearning.ConcisePipeline.RandomizedCost

/-!
# State-dependent costs in randomized execution

The operations `weightedTick` and `weightedRunFor` attach natural state-dependent charges to a
randomized execution while preserving its configuration marginal. The module proves resume
identities and stability of `weightedHaltJoint` when every running step has positive cost.

Such explicit cost accounting is useful in randomized quantum algorithm analyses, including the
Monte Carlo setting of [Montanaro2015].

## Main statements

* `weighted_finite_run_resume_and_marginal`: composition across fuel splits and preservation of
  marginals
* `weightedRunFor_unit_cost`: recovery of unit-cost execution
* `weighted_first_halt_stable_and_total_partition`: positive-cost stability and eventual mass
  partition

## References

* [Montanaro, 2015][Montanaro2015]
-/

open Qatlib.Concepts.AEMeanReadout.LocalAEBackend.RandomizedExecution
open Qatlib.Concepts.AEMeanReadout.LocalAEBackend.CostedLaw
open Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw
open Qatlib.Concepts.AEMeanReadout.LocalAEBackend
open Qatlib.Concepts.LinearLearning.ConcisePipeline

namespace Qatlib.Concepts.StoppingCore.BranchCostCore

open scoped Classical BigOperators ENNReal

variable {S O : Type} [Fintype S] [DecidableEq S] [Fintype O] [DecidableEq O]

/-- One execution step charging `cost s` in a running state and preserving a halted output at
zero additional cost. -/
noncomputable def weightedTick (next : S → PMF (O ⊕ S)) (cost : S → ℕ) :
    O ⊕ S → CostedLaw (O ⊕ S)
  | .inl o => CostedLaw.ret (.inl o)
  | .inr s => (next s).map (fun d => (d, cost s))

/-- Finite execution with state-dependent natural costs, accumulated by binding successive
weighted ticks. -/
noncomputable def weightedRunFor (next : S → PMF (O ⊕ S)) (cost : S → ℕ) :
    ℕ → O ⊕ S → CostedLaw (O ⊕ S)
  | 0, cfg => CostedLaw.ret cfg
  | fuel + 1, cfg => CostedLaw.bind (weightedTick next cost cfg)
      (weightedRunFor next cost fuel)

omit [Fintype S] [DecidableEq S] [Fintype O] [DecidableEq O] in

/-- Zero fuel returns the initial configuration with zero cost. -/
@[simp] theorem weightedRunFor_zero (next : S → PMF (O ⊕ S)) (c : S → ℕ)
    (cfg : O ⊕ S) : weightedRunFor next c 0 cfg = CostedLaw.ret cfg := rfl

omit [Fintype S] [DecidableEq S] [Fintype O] [DecidableEq O] in

/-- A weighted execution starting from a halted output returns that output with zero cost for
every fuel. -/
@[simp] theorem weightedRunFor_halted (next : S → PMF (O ⊕ S)) (c : S → ℕ)
    (fuel : ℕ) (o : O) :
    weightedRunFor next c fuel (.inl o) = CostedLaw.ret (.inl o) := by
  induction fuel with
  | zero => rfl
  | succ fuel ih => simpa [weightedRunFor, weightedTick] using ih

omit [Fintype S] [DecidableEq S] [Fintype O] [DecidableEq O] in

/-- A weighted run with fuel `m + n` equals an `m`-step run followed by an `n`-step
continuation, adding their costs. -/
theorem weightedRunFor_add (next : S → PMF (O ⊕ S)) (c : S → ℕ)
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

/-- Forgetting the cost after a costed bind agrees with binding the configuration marginals. -/
theorem costedLaw_map_fst_bind {α β : Type*} (p : CostedLaw α)
    (f : α → CostedLaw β) :
    (CostedLaw.bind p f).map Prod.fst =
      (p.map Prod.fst).bind (fun a => (f a).map Prod.fst) := by
  simp only [CostedLaw.bind, CostedLaw.charge, PMF.map_bind, PMF.map_comp,
    PMF.bind_map, Function.comp_def]

omit [Fintype S] [DecidableEq S] [Fintype O] [DecidableEq O] in

/-- State-dependent costs leave the configuration marginal of finite execution unchanged. -/
theorem weightedRunFor_marginal (next : S → PMF (O ⊕ S)) (c : S → ℕ)
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

/-- Weighted finite execution composes across fuel splits and has the same configuration
marginal as unit-cost execution. -/
theorem weighted_finite_run_resume_and_marginal :
    ∀ (S O : Type) [Fintype S] [DecidableEq S] [Fintype O] [DecidableEq O]
      (next : S → PMF (O ⊕ S)) (c : S → ℕ) (m n : ℕ) (cfg : O ⊕ S),
      weightedRunFor next c (m+n) cfg =
        CostedLaw.bind (weightedRunFor next c m cfg) (weightedRunFor next c n) ∧
      PMF.map Prod.fst (weightedRunFor next c n cfg) =
        PMF.map Prod.fst (RandomizedExecution.runFor next n cfg) := by
  intro S O _ _ _ _ next c m n cfg
  exact ⟨weightedRunFor_add next c m n cfg, weightedRunFor_marginal next c n cfg⟩

omit [Fintype S] [DecidableEq S] [Fintype O] [DecidableEq O] in

/-- Constant unit costs recover the original randomized finite execution law. -/
theorem weightedRunFor_unit_cost (next : S → PMF (O ⊕ S)) (n : ℕ) (cfg : O ⊕ S) :
    weightedRunFor next (fun _ => 1) n cfg = RandomizedExecution.runFor next n cfg := by
  induction n generalizing cfg with
  | zero => rfl
  | succ n ih =>
    have ht : weightedTick next (fun _ => 1) cfg = RandomizedExecution.tick next cfg := by
      cases cfg <;> rfl
    rw [weightedRunFor, RandomizedExecution.runFor, ht]
    congr 1
    funext d
    exact ih d

/-- The mass of halting with output `o` and total cost `k` in the weighted run with fuel `k`. -/
noncomputable def weightedHaltJoint (next : S → PMF (O ⊕ S)) (cost : S → ℕ)
    (cfg : O ⊕ S) (o : O) (k : ℕ) : ℝ≥0∞ :=
  weightedRunFor next cost k cfg (.inl o, k)

omit [Fintype S] [DecidableEq S] [Fintype O] [DecidableEq O] in

/-- A weighted run from `s` first samples `next s`, then continues with one less fuel and
charges `c s`. -/
theorem weightedRunFor_succ_running (next : S → PMF (O ⊕ S)) (c : S → ℕ)
    (n : ℕ) (s : S) :
    weightedRunFor next c (n+1) (.inr s) =
      (next s).bind (fun d => CostedLaw.charge (c s) (weightedRunFor next c n d)) := by
  simp [weightedRunFor, weightedTick, CostedLaw.bind, PMF.bind_map, Function.comp_def]

/-- The point mass of a weighted successor run is a sum over the first transition with cost
shifted by `c s`, or zero if the cost is too small. -/
theorem weightedRunFor_succ_running_point (next : S → PMF (O ⊕ S)) (c : S → ℕ)
    (n : ℕ) (s : S) (d : O ⊕ S) (k : ℕ) :
    weightedRunFor next c (n+1) (.inr s) (d,k) =
      if c s ≤ k then ∑' x, next s x * weightedRunFor next c n x (d,k-c s) else 0 := by
  rw [weightedRunFor_succ_running, PMF.bind_apply]
  simp only [charge_point_mass]
  split_ifs with h
  · rfl
  · simp

/-- If every running step costs at least one, halted mass at cost `k` stabilizes once fuel
reaches `k`. -/
theorem weightedRunFor_halt_stable (next : S → PMF (O ⊕ S)) (c : S → ℕ)
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
          rw [weightedRunFor_succ_running_point, ite_eq_right (by have := hc s; omega)]
          simp [CostedLaw.ret, PMF.pure_apply]
      | succ k =>
        obtain ⟨n, rfl⟩ : ∃ n, fuel = n+1 := ⟨fuel-1, by omega⟩
        rw [weightedRunFor_succ_running_point, weightedRunFor_succ_running_point]
        split_ifs with hcs
        · apply tsum_congr
          intro x
          rw [ih (k+1-c s) (by have := hc s; omega) x n (by have := hc s; omega),
            ih (k+1-c s) (by have := hc s; omega) x k (by have := hc s; omega)]
        · rfl

/-- For a fixed halted output and cost, its weighted finite-run mass is monotone in the fuel. -/
theorem weightedRunFor_halt_monotone (next : S → PMF (O ⊕ S)) (c : S → ℕ)
    (cfg : O ⊕ S) (o : O) (k : ℕ) :
    Monotone (fun n => weightedRunFor next c n cfg (.inl o,k)) := by
  apply monotone_nat_of_le_succ
  intro n
  rw [show n+1 = n+1 from rfl, weightedRunFor_add, CostedLaw.bind, PMF.bind_apply]
  have h := ENNReal.le_tsum (f := fun x => weightedRunFor next c n cfg x *
    CostedLaw.charge x.2 (weightedRunFor next c 1 x.1) (.inl o,k)) (.inl o,k)
  simpa [weightedRunFor_halted, CostedLaw.charge_ret, PMF.pure_apply] using h

/-- Under positive step costs, the supremum of the finite halted masses equals
`weightedHaltJoint`. -/
theorem weightedRunFor_halt_iSup (next : S → PMF (O ⊕ S)) (c : S → ℕ)
    (hc : ∀ s, 1 ≤ c s) (cfg : O ⊕ S) (o : O) (k : ℕ) :
    (⨆ n, weightedRunFor next c n cfg (.inl o,k)) = weightedHaltJoint next c cfg o k := by
  apply le_antisymm
  · apply iSup_le
    intro n
    calc
      weightedRunFor next c n cfg (.inl o,k) ≤
          weightedRunFor next c (max n k) cfg (.inl o,k) :=
        weightedRunFor_halt_monotone next c cfg o k (le_max_left _ _)
      _ = _ := weightedRunFor_halt_stable next c hc cfg o k _ (le_max_right _ _)
  · exact le_iSup (fun n => weightedRunFor next c n cfg (.inl o,k)) k

/-- A countable sum commutes with the supremum of a pointwise monotone sequence of extended
nonnegative real functions. -/
theorem weighted_tsum_iSup {α : Type*} (f : α → ℕ → ℝ≥0∞)
    (hf : ∀ a, Monotone (f a)) :
    (∑' a, ⨆ n, f a n) = ⨆ n, ∑' a, f a n := by
  simp_rw [ENNReal.tsum_eq_iSup_sum]
  simp_rw [ENNReal.finsetSum_iSup_of_monotone hf]
  exact iSup_comm

/-- The pending event of weighted execution has the same mass as unit-cost execution at the same
fuel. -/
theorem weightedRunFor_pending (next : S → PMF (O ⊕ S)) (c : S → ℕ)
    (cfg : O ⊕ S) (n : ℕ) :
    CostedLaw.event (weightedRunFor next c n cfg) (fun z => ∃ s, z.1 = Sum.inr s) =
      pendingMass next cfg n := by
  rw [pendingMass_eq_finiteSurvival]
  change _ = CostedLaw.event (RandomizedExecution.runFor next n cfg)
    (fun z => ∃ s, z.1 = Sum.inr s)
  rw [← CostedLaw.event_map _ Prod.fst (fun d => ∃ s, d = Sum.inr s),
    weightedRunFor_marginal, CostedLaw.event_map]

/-- The total halted mass of a finite weighted run plus its pending mass equals one. -/
theorem weightedRunFor_partition (next : S → PMF (O ⊕ S)) (c : S → ℕ)
    (cfg : O ⊕ S) (n : ℕ) :
    (∑' o, ∑' k, weightedRunFor next c n cfg (.inl o,k)) + pendingMass next cfg n = 1 := by
  rw [← weightedRunFor_pending next c cfg n]
  have he : CostedLaw.event (weightedRunFor next c n cfg)
      (fun z => ∃ s, z.1 = Sum.inr s) =
      ∑' s, ∑' k, weightedRunFor next c n cfg (.inr s,k) := by
    unfold CostedLaw.event CostedLaw.expectation
    rw [tsum_prod_type', tsum_sum_type']
    simp
  rw [he, ← tsum_sum_type' (F := fun d : O ⊕ S => ∑' k, weightedRunFor next c n cfg (d,k)),
    ← tsum_prod_type' (F := fun z : (O ⊕ S) × ℕ => weightedRunFor next c n cfg z), PMF.tsum_coe]

/-- Positive step costs give stability of the weighted halting joint masses and a partition of
unit mass into eventual halting and nontermination. -/
theorem weighted_first_halt_stable_and_total_partition :
    ∀ (S O : Type) [Fintype S] [DecidableEq S] [Fintype O] [DecidableEq O]
      (next : S → PMF (O ⊕ S)) (c : S → ℕ) (cfg : O ⊕ S),
      (∀ s, 1 ≤ c s) →
      (∀ o k fuel, k ≤ fuel → weightedRunFor next c fuel cfg (.inl o,k) =
        weightedHaltJoint next c cfg o k) ∧
      (∑' o, ∑' k, weightedHaltJoint next c cfg o k) + nonterminationMass next cfg = 1 := by
  intro S O _ _ _ _ next c cfg hc
  refine ⟨fun o k fuel h => weightedRunFor_halt_stable next c hc cfg o k fuel h, ?_⟩
  have hm : Monotone (fun n => ∑' o, ∑' k, weightedRunFor next c n cfg (.inl o,k)) := by
    intro n m h
    exact ENNReal.tsum_le_tsum fun o => ENNReal.tsum_le_tsum fun k =>
      weightedRunFor_halt_monotone next c cfg o k h
  have hs : (⨆ n, ∑' o, ∑' k, weightedRunFor next c n cfg (.inl o,k)) =
      ∑' o, ∑' k, weightedHaltJoint next c cfg o k := by
    rw [← weighted_tsum_iSup _ (fun o => by
      intro n m h
      exact ENNReal.tsum_le_tsum fun k => weightedRunFor_halt_monotone next c cfg o k h)]
    apply tsum_congr
    intro o
    rw [← weighted_tsum_iSup _ (fun k => weightedRunFor_halt_monotone next c cfg o k)]
    exact tsum_congr fun k => weightedRunFor_halt_iSup next c hc cfg o k
  have ht := (tendsto_atTop_iSup hm).add (pendingMass_tendsto_iInf next cfg)
  rw [hs] at ht
  have hconst : Filter.Tendsto (fun _ : ℕ => (1 : ℝ≥0∞)) Filter.atTop
      (nhds ((∑' o, ∑' k, weightedHaltJoint next c cfg o k) + nonterminationMass next cfg)) :=
    ht.congr' (Filter.Eventually.of_forall fun n => weightedRunFor_partition next c cfg n)
  exact tendsto_nhds_unique hconst tendsto_const_nhds

end Qatlib.Concepts.StoppingCore.BranchCostCore
