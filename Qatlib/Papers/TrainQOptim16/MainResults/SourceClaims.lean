/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.TrainQOptim16.MainResults.Ratio.OverlapRatio
import Qatlib.Papers.TrainQOptim16.MainResults.Schedule.TrotterSchedule
import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic

set_option backward.isDefEq.respectTransparency false

/-!
# The paper's two main empirical claims

Source: Wecker, Hastings, Troyer, *Training A Quantum Optimizer*,
fixed arXiv:1605.05370v1.

This module states the two active claims of the paper as Lean theorems over
the **published table data**. The claims are empirical/numerical: they report
measurements of a schedule search over 202078 candidate schedules trained on at
most 20-bit MAX-2-SAT instances, and the paper does not derive the numbers from
a closed-form theorem. Accordingly the Lean statements below record exactly the
reported quantities (all entries of Table II, p. 5; schedule 154's ratios in
Table IV, p. 6; and its average overlaps in Table III, p. 6) and prove the
arithmetic content of the claims from those recorded values. They are not a
re-simulation of the search, and no claim is made that the training procedure
would reproduce the values.

* `mainResult_learned_schedules_beat_optimized_annealing` — c001, Sec. III,
  p. 4–5 and Table II: the ratio of averages of the learned schedules to the
  optimized anneal is larger than one for every reported training set, every
  reported initial schedule, and in grand average (`2.9`).
* `mainResult_learned_schedules_generalize_to_larger_ensembles` — c002,
  Sec. VI, p. 9 and Tables III–IV, p. 6: schedule 154, trained on 20-bit
  instances, has ratio-of-averages larger than one on CFLLS and on the
  20-, 24- and 28-bit ensembles, with the ratio increasing from 20 to 28 bits.

The overlap ratios use `Ratio.ratioOfAverages`; the bridge from pointwise
overlap improvement to that ratio is `Ratio.ratioOfAverages_gt_one_of_pointwise`.
-/

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.TrainQOptim16.MainResults

open Qatlib.Papers.TrainQOptim16.MainResults.Ratio
open scoped BigOperators

namespace SourceClaims

/-- The 137 CFLLS instances used as the full test set of Sec. III, p. 4. -/
def cfllsInstances : Finset (Fin 137) := Finset.univ

/-- The CFLLS test set has 137 instances. -/
theorem cfllsInstances_card : cfllsInstances.card = 137 := by
  simp [cfllsInstances]

/-! ## c001: Table II of p. 5 -/

/-- Table II, p. 5: the ratio of averages for the 13 reported initial schedules
(rows 2 through 14 of Table I) against the five training sets (columns 0–4).
Each entry is the ratio of the average squared overlap of the learned schedule
to the average squared overlap of the optimized anneal. -/
def tableIIEntries (i : Fin 13) (j : Fin 5) : ℝ :=
  ![
    ![1.4, 2.0, 1.7, 1.9, 2.2],
    ![4.2, 3.6, 3.5, 3.3, 3.8],
    ![2.5, 2.4, 2.4, 2.3, 2.4],
    ![2.4, 2.3, 2.4, 2.4, 2.4],
    ![2.9, 3.0, 3.1, 3.3, 2.6],
    ![2.4, 2.0, 2.3, 2.2, 2.1],
    ![3.5, 3.5, 3.4, 3.5, 3.7],
    ![2.7, 3.2, 2.8, 3.1, 3.4],
    ![2.5, 2.2, 2.1, 2.4, 2.1],
    ![4.4, 4.2, 4.2, 4.1, 4.1],
    ![3.1, 2.9, 3.3, 3.5, 3.1],
    ![2.0, 2.4, 2.3, 2.0, 2.0],
    ![4.5, 4.5, 4.3, 4.5, 4.4]
  ] i j

/-- Table II, p. 5, column "Avg": the average of each row over the five
training sets. -/
def tableIIRowAverages : Fin 13 → ℝ :=
  ![1.8, 3.7, 2.4, 2.4, 3.0, 2.2, 3.5, 3.0, 2.3, 4.2, 3.2, 2.1, 4.4]

/-- Table II, p. 5, row "Avg": the average of each training-set column over the
13 initial schedules, followed by the grand average `2.9`. -/
def tableIIColumnAverages : Fin 6 → ℝ := ![3.0, 2.9, 2.9, 2.9, 3.0, 2.9]

/-- The grand average reported in the bottom-right corner of Table II, p. 5. -/
def tableIIGrandAverage : ℝ := 2.9

/-- Every reported Table II entry is larger than one. -/
theorem tableIIEntries_gt_one : ∀ i j, 1 < tableIIEntries i j := by
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [tableIIEntries]

/-- Every reported Table II row average is larger than one. -/
theorem tableIIRowAverages_gt_one : ∀ i, 1 < tableIIRowAverages i := by
  intro i
  fin_cases i <;> norm_num [tableIIRowAverages]

/-- Every reported Table II column average is larger than one. -/
theorem tableIIColumnAverages_gt_one : ∀ j, 1 < tableIIColumnAverages j := by
  intro j
  fin_cases j <;> norm_num [tableIIColumnAverages]

/-- The grand average of Table II is the reported value `2.9`, and it is
significantly larger than one (`3/2`). -/
theorem tableIIGrandAverage_spec :
    tableIIGrandAverage = 2.9 ∧ (3 / 2 : ℝ) < tableIIGrandAverage := by
  refine ⟨rfl, ?_⟩
  norm_num [tableIIGrandAverage]

/-- **c001** (Sec. III, p. 4–5; Table II, p. 5). The learned schedules beat the
per-instance optimized anneal: over the 137 CFLLS instances the reported ratio
of averages is larger than one for every entry, every row average and every
column average of Table II, and the reported grand average is `2.9 > 3/2`.

Boundary: this theorem records the published measurements of Table II; it is
not a re-derivation of the schedule search. The ratio is the paper's "ratio of
averages" (see `Ratio.ratioOfAverages`). -/
theorem mainResult_learned_schedules_beat_optimized_annealing :
    cfllsInstances.card = 137 ∧
      (∀ i j, 1 < tableIIEntries i j) ∧
      (∀ i, 1 < tableIIRowAverages i) ∧
      (∀ j, 1 < tableIIColumnAverages j) ∧
      tableIIGrandAverage = 2.9 ∧
      (3 / 2 : ℝ) < tableIIGrandAverage :=
  ⟨cfllsInstances_card, tableIIEntries_gt_one, tableIIRowAverages_gt_one,
    tableIIColumnAverages_gt_one, tableIIGrandAverage_spec.1,
    tableIIGrandAverage_spec.2⟩

/-! ## c002: Tables III–IV of p. 6 -/

/-- The size `N` (number of bits) of the training ensemble of Sec. IV and
Sec. VI: the schedules were trained on 20-bit instances. -/
def trainingBits : ℕ := 20

/-- The sizes of the related test ensembles `N = 20, 24, 28` of Tables III–IV,
p. 6. -/
def testEnsembleBits : Fin 3 → ℕ := ![20, 24, 28]

/-- Table IV, p. 6: ratio of averages of learned schedule 154 against
`L(10,1,1)` on the CFLLS instances. -/
def schedule154RatioCFLLS : ℝ := 4.6

/-- Table IV, p. 6: ratio of averages of learned schedule 154 against
`L(10,1,1)` on the `N = 20, 24, 28` ensembles. -/
def schedule154RatioBySize : Fin 3 → ℝ := ![4.4, 5.9, 7.6]

/-- Table III, p. 6: average squared overlap of learned schedule 154 on the
four test sets (CFLLS, `N = 20`, `N = 24`, `N = 28`). -/
def schedule154AverageOverlap : Fin 4 → ℝ := ![0.117, 0.085, 0.050, 0.034]

/-- Table III, p. 6: average squared overlap of the reference anneal
`L(10,1,1)` on the same four test sets. -/
def linear10AverageOverlap : Fin 4 → ℝ := ![0.025, 0.019, 0.009, 0.004]

/-- The 20-bit training ensemble is one of the tested ensembles. -/
theorem trainingBits_is_first_ensemble : trainingBits = testEnsembleBits 0 := rfl

/-- Every reported ratio of averages for schedule 154 in Table IV is larger
than one. -/
theorem schedule154Ratios_gt_one :
    1 < schedule154RatioCFLLS ∧ ∀ k, 1 < schedule154RatioBySize k := by
  refine ⟨by norm_num [schedule154RatioCFLLS], ?_⟩
  intro k
  fin_cases k <;> simp [schedule154RatioBySize] <;> norm_num

/-- The reported ratio of averages of schedule 154 increases from `N = 20` to
`N = 24` to `N = 28` (Table IV, p. 6). -/
theorem schedule154Ratios_increasing_with_size :
    schedule154RatioBySize 0 < schedule154RatioBySize 1 ∧
      schedule154RatioBySize 1 < schedule154RatioBySize 2 := by
  simp [schedule154RatioBySize]
  norm_num

/-- The average overlaps of Table III are sorted by test ensemble and the
learned schedule 154 dominates the reference anneal `L(10,1,1)` entrywise. -/
theorem schedule154_overlap_dominates :
    ∀ k, linear10AverageOverlap k < schedule154AverageOverlap k := by
  intro k
  fin_cases k <;>
    norm_num [schedule154AverageOverlap, linear10AverageOverlap]

/-- Consequently the ratio of averages of the Table III overlaps is larger than
one, by the pointwise bridge `ratioOfAverages_gt_one_of_pointwise`. -/
theorem schedule154_overlap_ratioOfAverages_gt_one :
    1 < ratioOfAverages schedule154AverageOverlap linear10AverageOverlap
      (Finset.univ : Finset (Fin 4)) := by
  refine ratioOfAverages_gt_one_of_pointwise _ _ _ ⟨0, by simp⟩ ?_ ?_
  · intro k _
    fin_cases k <;> norm_num [linear10AverageOverlap]
  · intro k _
    exact schedule154_overlap_dominates k

/-- **c002** (Sec. VI, p. 9; Tables III–IV, p. 6). Schedules trained on the
20-bit subset generalize: schedule 154, trained on 20-bit instances, has
ratio of averages larger than one on the full CFLLS set and on the 20-, 24- and
28-bit ensembles, that ratio increases with the ensemble size from `N = 20` to
`N = 28`, and the underlying Table III average overlaps make the learned
schedule dominate the reference anneal `L(10,1,1)` entrywise.

Boundary: these are the published measurements of Tables III–IV, not a
re-simulation of the search; `trainingBits = 20` is the training regime
reported in Sec. IV, p. 5. -/
theorem mainResult_learned_schedules_generalize_to_larger_ensembles :
    trainingBits = 20 ∧
      testEnsembleBits 0 = 20 ∧ testEnsembleBits 1 = 24 ∧
      testEnsembleBits 2 = 28 ∧
      1 < schedule154RatioCFLLS ∧
      (∀ k, 1 < schedule154RatioBySize k) ∧
      schedule154RatioBySize 0 < schedule154RatioBySize 1 ∧
      schedule154RatioBySize 1 < schedule154RatioBySize 2 ∧
      (∀ k, linear10AverageOverlap k < schedule154AverageOverlap k) ∧
      1 < ratioOfAverages schedule154AverageOverlap linear10AverageOverlap
        (Finset.univ : Finset (Fin 4)) := by
  refine ⟨rfl, rfl, rfl, rfl, schedule154Ratios_gt_one.1,
    schedule154Ratios_gt_one.2, schedule154Ratios_increasing_with_size.1,
    schedule154Ratios_increasing_with_size.2, schedule154_overlap_dominates,
    schedule154_overlap_ratioOfAverages_gt_one⟩

end SourceClaims

end Qatlib.Papers.TrainQOptim16.MainResults
