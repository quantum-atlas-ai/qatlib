/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.AmplitudeSearch.Amplification.ChargedClock
import Qatlib.Concepts.AmplitudeSearch.Amplification.InitializedBudgetCoupling

/-!
# Success at a charged minimum-finding budget

`chargedInitialSuccess` averages initialized budgeted success over a uniform initial index. The
module bounds this average between zero and one, couples charged completion to actual success,
and obtains success at least one half at `chargedBudget`.

The probability estimate uses the mean-clock and timeout argument for quantum minimum finding
associated with [DurrHoyer1996].

## Main statements

* `chargedCompletion_le_actual_success`: transfers the charged completion bound to the actual
  procedure.
* `charged_initial_success_half`: proves the one-half success guarantee.

## References

* [Durr and Hoyer, 1996][DurrHoyer1996]
-/

set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

open Qatlib.Concepts.LinearLearning.ConcisePipeline

open Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw
open Qatlib.Concepts.AmplitudeSearch.Amplification.Experiment
open Qatlib.Concepts.AmplitudeSearch.Amplification.RankedCallLaw
open Qatlib.Concepts.AmplitudeSearch.Amplification.SortedRankedTable

set_option autoImplicit false

namespace Qatlib.Concepts.AmplitudeSearch.Amplification

/-- The uniform initial average of minimum-finding success probabilities with initialization
charge `initCharge N`. -/
noncomputable def chargedInitialSuccess {N : ℕ} {α : Type*} [LinearOrder α]
    (T : Fin N → α) (budget : ℕ) : ℝ :=
  (∑ current : Fin N, minimumBudgetSuccessWithInit T (initCharge N) budget current) / (N : ℝ)

/-- For a nonempty table, charged initial success lies between zero and one. -/
theorem chargedInitialSuccess_bounds {N : ℕ} {α : Type*} [LinearOrder α]
    (T : Fin N → α) (hN : 0 < N) (budget : ℕ) :
    0 ≤ chargedInitialSuccess T budget ∧ chargedInitialSuccess T budget ≤ 1 := by
  constructor
  · exact div_nonneg (Finset.sum_nonneg
      (fun i _ => (minimumBudgetSuccessWithInit_bounds T (initCharge N) hN budget i).1))
      (Nat.cast_nonneg N)
  · have hs : (∑ i : Fin N, minimumBudgetSuccessWithInit T (initCharge N) budget i) ≤
        ∑ _i : Fin N, (1 : ℝ) := Finset.sum_le_sum
      (fun i _ => (minimumBudgetSuccessWithInit_bounds T (initCharge N) hN budget i).2)
    have h := div_le_div_of_nonneg_right hs (Nat.cast_nonneg N)
    have hn : (N : ℝ) ≠ 0 := by exact_mod_cast hN.ne'
    simpa only [chargedInitialSuccess, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      nsmul_eq_mul, mul_one, div_self hn] using! h

/-- The completion mass of the charged ranked run is bounded by the actual success probability
with the corresponding initialization charge. -/
theorem chargedCompletion_le_actual_success {N : ℕ} {α : Type*} [LinearOrder α]
    (T : SortedRankedTable N α) (hN : 0 < N) (initial : Fin N) (budget : ℕ) :
    (chargedBBHTLaw T.indexOfRank hN).completionMass T.skip (chargedCallCost N)
      (T.skip.next initial) budget ≤
        minimumBudgetSuccessWithInit T.value (initCharge N) budget (T.indexOfRank initial) := by
  simpa only [chargedBBHTLaw, chargedCallCost, initializedBBHTLaw] using!
    initializedCompletion_le_actual_success T hN (initCharge N) initial budget

/-- A nonempty table has charged initial success probability at least `1 / 2` at `chargedBudget
N` [DurrHoyer1996]. -/
theorem charged_initial_success_half {N : ℕ} {α : Type*} [LinearOrder α]
    (T : Fin N → α) (hN : 0 < N) :
    (1 / 2 : ℝ) ≤ chargedInitialSuccess T (chargedBudget N) := by
  let ranked := SortedRankedTable.ofTable T
  let law := chargedBBHTLaw ranked.indexOfRank hN
  let B := chargedBudget N
  have hceil : 2 * chargedMeanBudget N ≤ (B : ℝ) := chargedBudget_ge_twice_mean N
  obtain ⟨q, hq, _, hqb⟩ := charged_attainment_moment ranked hN
  have hmeanpos : 0 < chargedMeanBudget N :=
    mul_pos (by norm_num) (sourceMeanBudget_pos N hN)
  have hm : (0 : ℝ) < (B : ℝ) / 2 := by linarith
  have hqm : q ≤ (B : ℝ) / 2 := by linarith
  obtain ⟨p, hp, hhalf, _⟩ := nonnegative_clock_half_mass
    (law.initialMass ranked.skip) (fun x : Fin N × List (SearchTrace N) => law.runClock x.2)
    (law.initialMass_normalized ranked.skip hN).1
    (law.initialMass_normalized ranked.skip hN).2
    (fun x => law.runClock_nonneg x.2) q ((B : ℝ) / 2) hq hqm hm
  have htwo : 2 * ((B : ℝ) / 2) = (B : ℝ) := by ring
  change HasSum (fun x : Fin N × List (SearchTrace N) =>
    if (chargedBBHTLaw ranked.indexOfRank hN).runClock x.2 ≤ 2 * ((B : ℝ) / 2) then
      (chargedBBHTLaw ranked.indexOfRank hN).initialMass ranked.skip x else 0) p at hp
  simp only [chargedRunClock_eq_real, htwo, Nat.cast_le] at hp
  have heq := hp.unique
    (law.initial_completion_hasSum ranked.skip (chargedCallCost N) hN B)
  rw [heq] at hhalf
  have hsums := Finset.sum_le_sum (fun i (_hi : i ∈ Finset.univ) =>
    chargedCompletion_le_actual_success ranked hN i B)
  have hd := div_le_div_of_nonneg_right hsums (Nat.cast_nonneg N)
  rw [ranked.indexOfRank.sum_comp] at hd
  exact hhalf.trans hd

end Qatlib.Concepts.AmplitudeSearch.Amplification
