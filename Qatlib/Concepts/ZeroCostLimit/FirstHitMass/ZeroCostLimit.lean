/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.ZeroCostLimit.FirstHitMass.ZeroCostLimitDefs

/-!
# Halting mass with zero-cost transitions

This module compares accumulated-cost and first-hit descriptions of a finite probabilistic
process. Marginalization and monotone partial sums show that summing over all costs recovers
output halting mass, and that total halting mass plus nontermination mass equals one; these
process estimates support probabilistic algorithm analysis such as [DeckerDraismaWocjan2009].

## Main statements

* `g1`: Establish cost marginalization and total probability conservation.

## References

* [Decker et al., 2009][DeckerDraismaWocjan2009]
-/

set_option warningAsError false
open Qatlib.Concepts.LinearLearning.ConcisePipeline

open Qatlib.Concepts.StoppingCore.BranchCostCore
open Qatlib.Concepts.AEMeanReadout.LocalAEBackend

open Qatlib.Concepts.AEMeanReadout.LocalAEBackend.CostedLaw

set_option autoImplicit false

namespace Qatlib.Concepts.ZeroCostLimit.FirstHitMass
open Qatlib.Concepts.AEMeanReadout.LocalAEBackend.RandomizedExecution
open scoped BigOperators ENNReal Classical

/-- Summing a joint probability mass function over its natural-number charge coordinate gives
its first marginal. -/
lemma charge_marginal {α : Type} (μ : PMF (α × ℕ)) (a : α) :
    (∑' k, μ (a, k)) = μ.map Prod.fst a := by
  rw [PMF.map_apply, tsum_prod_type']
  have hzero : ∀ b : α, b ≠ a → (∑' k, if a = b then μ (b, k) else 0) = 0 := by
    intro b hb
    have hk : ∀ k, (if a = b then μ (b, k) else 0) = 0 := fun k => by
      rw [if_neg (Ne.symm hb)]
    exact (tsum_congr hk).trans tsum_zero
  rw [tsum_eq_single a hzero]
  simp

/-- At finite fuel, summing weighted halted mass over total cost equals summing unweighted
halted mass over step count. -/
lemma weighted_halted_eq_runFor {S O : Type} [Fintype S] [DecidableEq S]
    [Fintype O] [DecidableEq O] (next : S → PMF (O ⊕ S)) (cost : S → ℕ)
    (n : ℕ) (cfg : O ⊕ S) (o : O) :
    (∑' k, weightedRunFor next cost n cfg (.inl o, k)) =
      ∑' j, runFor next n cfg (.inl o, j) := by
  rw [charge_marginal, charge_marginal, weightedRunFor_marginal]

/-- The halted mass after finite fuel is the sum of first-hit masses through that fuel. -/
lemma runFor_halted_partial {S O : Type} [Fintype S] [DecidableEq S]
    [Fintype O] [DecidableEq O] (next : S → PMF (O ⊕ S))
    (fuel : ℕ) (cfg : O ⊕ S) (o : O) :
    (∑' j, runFor next fuel cfg (.inl o, j)) =
      ∑ j ∈ Finset.range (fuel + 1), haltJoint next cfg o j := by
  classical
  refine (tsum_eq_sum (L := SummationFilter.unconditional ℕ)
      (s := Finset.range (fuel + 1))
      (f := fun j : ℕ => runFor next fuel cfg (.inl o, j)) ?_).trans ?_
  · intro j hj
    exact runFor_point_cost_gt_fuel next fuel cfg (.inl o) j <| by
      have hlt : ¬ j < fuel + 1 := Finset.mem_range.not.mp hj
      omega
  · refine Finset.sum_congr rfl fun j hj => ?_
    have hle : j ≤ fuel := by
      have hlt : j < fuel + 1 := Finset.mem_range.mp hj
      omega
    exact haltJoint_eq_runFor_of_le hle

/-- The supremum of finite partial sums of first-hit masses equals their infinite sum. -/
lemma iSup_partial_haltJoint {S O : Type} [Fintype S] [DecidableEq S]
    [Fintype O] [DecidableEq O] (next : S → PMF (O ⊕ S)) (cfg : O ⊕ S) (o : O) :
    (⨆ fuel, ∑ j ∈ Finset.range (fuel + 1), haltJoint next cfg o j) =
      ∑' t, haltJoint next cfg o t := by
  have hmono : Monotone
      (fun fuel => ∑ j ∈ Finset.range (fuel + 1), haltJoint next cfg o j) := by
    intro a b hab
    exact Finset.sum_le_sum_of_subset (Finset.range_mono (Nat.succ_le_succ hab))
  have htend : Filter.Tendsto
      (fun fuel => ∑ j ∈ Finset.range (fuel + 1), haltJoint next cfg o j)
      Filter.atTop (nhds (∑' t, haltJoint next cfg o t)) :=
    (HasSum.tendsto_sum_nat (ENNReal.summable (f := haltJoint next cfg o)).hasSum).comp
      (Filter.tendsto_add_atTop_nat 1)
  exact tendsto_nhds_unique (tendsto_atTop_iSup hmono) htend

/-- For finite state and output spaces, summing halted mass over costs gives the first-hit
output mass, and total halted mass plus nontermination mass equals one. -/
theorem g1 :
    ∀ (S O : Type) [Fintype S] [DecidableEq S] [Fintype O] [DecidableEq O]
      (next : S → PMF (O ⊕ S)) (cost : S → ℕ) (cfg : O ⊕ S),
      (∀ o, (∑' k, haltMass next cost cfg o k) = ∑' t, haltJoint next cfg o t) ∧
      (∑' o, ∑' k, haltMass next cost cfg o k) + nonterminationMass next cfg = 1 := by
  intro S O _ _ _ _ next cost cfg
  have hmass : ∀ o, (∑' k, haltMass next cost cfg o k) =
      ∑' t, haltJoint next cfg o t := by
    intro o
    unfold haltMass
    rw [weighted_tsum_iSup (fun k fuel => weightedRunFor next cost fuel cfg (.inl o, k))
      (fun k => weightedRunFor_halt_monotone next cost cfg o k)]
    have hstep : ∀ fuel, (∑' k, weightedRunFor next cost fuel cfg (.inl o, k)) =
        ∑ j ∈ Finset.range (fuel + 1), haltJoint next cfg o j := by
      intro fuel
      rw [weighted_halted_eq_runFor, runFor_halted_partial]
    simp_rw [hstep]
    exact iSup_partial_haltJoint next cfg o
  refine ⟨hmass, ?_⟩
  rw [tsum_congr hmass]
  exact haltJoint_tsum_add_nonterminationMass next cfg

end Qatlib.Concepts.ZeroCostLimit.FirstHitMass
