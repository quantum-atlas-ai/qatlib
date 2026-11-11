/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.AmplitudeSearch.Amplification.SortedTable
import Qatlib.Concepts.AmplitudeSearch.Amplification.RunMoment

/-!
# Minimum attainment along table runs

This module turns ranked call outcomes into the clocked table trace `tableClockedTrace` and
connects positive run mass to minimum attainment. A completed run of positive mass ends at a
minimum value, and a run fitting the budget retains a minimum after any further checked update,
supporting the budgeted minimum-finding analysis [DurrHoyer1996].

## Main statements

* `tableClockedTrace_clock`: identifies the table-trace clock with the ranked run clock.
* `positive_initial_run_is_minimum`: proves minimum attainment for initial runs of positive
  mass.
* `fitting_initial_run_preserves_minimum`: preserves a minimum under budget truncation and a
  checked update.

## References

* [Dürr and Høyer, 1996][DurrHoyer1996]
-/

set_option backward.isDefEq.respectTransparency false
set_option warningAsError false

open Qatlib.Concepts.AmplitudeSearch.Amplification.Experiment

open Qatlib.Concepts.AmplitudeSearch.Amplification.RankedCallLaw
open Qatlib.Concepts.AmplitudeSearch.Amplification.SortedRankedTable

set_option autoImplicit false

namespace Qatlib.Concepts.AmplitudeSearch.Amplification

variable {N : ℕ} {Ω : Type} {α : Type*} [LinearOrder α]

/-- The clocked trace of table indices obtained by mapping each call output rank through
`T.indexOfRank` and pairing it with its duration. -/
noncomputable def tableClockedTrace (T : SortedRankedTable N α) (law : RankedCallLaw N Ω)
    (xs : List Ω) : ClockedTrace (Fin N) :=
  xs.map (fun x => (T.indexOfRank (law.outputRank x), law.duration x))

/-- Every duration in the table clocked trace is nonnegative. -/
theorem tableClockedTrace_nonneg (T : SortedRankedTable N α) (law : RankedCallLaw N Ω)
    (xs : List Ω) : ∀ x ∈ tableClockedTrace T law xs, 0 ≤ x.2 := by
  intro x hx
  obtain ⟨y, _, rfl⟩ := List.mem_map.mp hx
  exact law.duration_nonneg y

/-- The total clock of the table trace equals the accumulated clock of the ranked call outcomes. -/
theorem tableClockedTrace_clock (T : SortedRankedTable N α) (law : RankedCallLaw N Ω)
    (xs : List Ω) : traceClock (tableClockedTrace T law xs) = law.runClock xs := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    simpa only [tableClockedTrace, List.map_cons, traceClock, RankedCallLaw.runClock,
      add_right_inj] using ih

/-- A completed ranked run of positive mass, started at the skip threshold of `initial`, yields
a minimum table value after all checked updates. -/
theorem positive_run_is_minimum (T : SortedRankedTable N α) (law : RankedCallLaw N Ω)
    (initial : Fin N) (xs : List Ω)
    (hm : 0 < law.runMass T.skip (T.skip.next initial) xs) :
    ∀ j, T.value (finalCheckedIndex T.value (T.indexOfRank initial)
      (tableClockedTrace T law xs)) ≤ T.value j := by
  induction xs generalizing initial with
  | nil =>
    have hz : T.skip.next initial = 0 := by
      by_contra hz
      simp [RankedCallLaw.runMass, hz] at hm
    exact (T.lowerCut_zero_iff_minimum initial).mp hz
  | cons x xs ih =>
    have htN : T.skip.next initial < N := lt_of_le_of_lt (T.skip.le_rank initial) initial.isLt
    by_cases ht : T.skip.next initial = 0
    · simp [RankedCallLaw.runMass, ht] at hm
    by_cases hx : (law.outputRank x).val < T.skip.next initial
    · have hprod : 0 < law.mass (T.skip.next initial) x *
          law.runMass T.skip (T.skip.next (law.outputRank x)) xs := by
        simpa only [RankedCallLaw.runMass, if_neg ht, if_pos hx] using hm
      have htail : 0 < law.runMass T.skip (T.skip.next (law.outputRank x)) xs := by
        rcases mul_pos_iff.mp hprod with h | h
        · exact h.2
        · linarith [law.mass_nonneg _ htN x, h.1]
      have hlt : T.value (T.indexOfRank (law.outputRank x)) < T.value (T.indexOfRank initial) :=
        (T.smaller_iff_lowerCut initial (law.outputRank x)).mpr hx
      simp only [tableClockedTrace, List.map_cons, finalCheckedIndex, checkedUpdate, if_pos hlt]
      exact ih (law.outputRank x) htail
    · simp only [RankedCallLaw.runMass, if_neg ht, if_neg hx] at hm
      linarith

/-- For a nonempty table, every initial run of positive mass yields an index whose value is at
most every table value. -/
theorem positive_initial_run_is_minimum (T : SortedRankedTable N α) (law : RankedCallLaw N Ω)
    (hN : 0 < N) (x : Fin N × List Ω) (hm : 0 < law.initialMass T.skip x) :
    ∀ j, T.value (finalCheckedIndex T.value (T.indexOfRank x.1)
      (tableClockedTrace T law x.2)) ≤ T.value j := by
  apply positive_run_is_minimum T law x.1 x.2
  exact (div_pos_iff_of_pos_right (by exact_mod_cast hN : (0 : ℝ) < N)).mp hm

/-- If an initial run has positive mass and its clock fits the budget, its budget-prefix index
remains a minimum after a checked update with any candidate. -/
theorem fitting_initial_run_preserves_minimum (T : SortedRankedTable N α)
    (law : RankedCallLaw N Ω) (hN : 0 < N) (x : Fin N × List Ω)
    (hm : 0 < law.initialMass T.skip x) (budget : ℝ) (hb : law.runClock x.2 ≤ budget)
    (candidate : Fin N) :
    ∀ j, T.value (checkedUpdate T.value
      (budgetPrefixIndex T.value (T.indexOfRank x.1) budget (tableClockedTrace T law x.2))
        candidate) ≤ T.value j := by
  apply interrupted_output_preserves T.value _ (tableClockedTrace_nonneg T law x.2)
    (T.indexOfRank x.1) candidate budget
  · simpa only [tableClockedTrace_clock] using hb
  · exact positive_initial_run_is_minimum T law hN x hm

end Qatlib.Concepts.AmplitudeSearch.Amplification
