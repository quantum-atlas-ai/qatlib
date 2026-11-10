/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

set_option autoImplicit false

namespace Qatlib.Papers.AdiabaticQLS23.MainResults

noncomputable section

def qwConstantFactor : ℝ := 1.84

def previousUpperBoundConstant : ℝ := 2305

def reportedRmRatios : List ℝ := [7.81, 7.95, 8.03, 7.56, 7.42]

def reportedQwSteps : List ℝ := [36, 76, 120, 176, 232]

def reportedRmTimes : List ℝ := [281, 604, 963, 1330, 1722]

def meanReportedRmRatio : ℝ := (7.81 + 7.95 + 8.03 + 7.56 + 7.42) / 5

def reportedTotalComplexityGain : ℝ := 3

def reportedDirectedGraphQwSteps : ℝ := 2416

def reportedDirectedGraphRmTime : ℝ := 23150

def reportedDirectedGraphRatio : ℝ := 9.58

def reportedCircuitQwSteps : ℝ := 39800

def reportedCircuitRmTime : ℝ := 18170000

def reportedCircuitRatio : ℝ := 457

theorem measured_constant_factor_1200 {α U : ℝ} (hα : α = 1.84) (hU : U = 2305) :
    1200 * α ≤ U := by
  subst hα
  subst hU
  norm_num

theorem measured_constant_factor_1250 {α U : ℝ} (hα : α = 1.84) (hU : U = 2305) :
    1250 * α ≤ U := by
  subst hα
  subst hU
  norm_num

theorem table1_ratio_ge_seven :
    ∀ r ∈ reportedRmRatios, 7 ≤ r := by
  intro r hr
  simp [reportedRmRatios] at hr
  rcases hr with h | h | h | h | h <;> subst h <;> norm_num

theorem table1_mean_ratio_between_seven_and_eight :
    7 ≤ meanReportedRmRatio ∧ meanReportedRmRatio ≤ 8 := by
  constructor <;> norm_num [meanReportedRmRatio]

theorem table1_qw_less_than_rm :
    (36 : ℝ) < 281 ∧ (76 : ℝ) < 604 ∧ (120 : ℝ) < 963 ∧
    (176 : ℝ) < 1330 ∧ (232 : ℝ) < 1722 := by
  norm_num

theorem table1_ratio_matches_data :
    |(781 / 100 : ℝ) - 281 / 36| ≤ 1 / 100 ∧
    |(795 / 100 : ℝ) - 604 / 76| ≤ 1 / 100 ∧
    |(803 / 100 : ℝ) - 963 / 120| ≤ 1 / 100 ∧
    |(756 / 100 : ℝ) - 1330 / 176| ≤ 1 / 100 ∧
    |(742 / 100 : ℝ) - 1722 / 232| ≤ 1 / 100 := by
  norm_num

theorem table2_directed_ratio_matches_data :
    |reportedDirectedGraphRatio - reportedDirectedGraphRmTime / reportedDirectedGraphQwSteps|
      ≤ 0.01 := by
  norm_num [reportedDirectedGraphRatio, reportedDirectedGraphRmTime,
    reportedDirectedGraphQwSteps]

theorem table2_circuit_ratio_matches_data :
    |reportedCircuitRatio - reportedCircuitRmTime / reportedCircuitQwSteps| ≤ 1 := by
  norm_num [reportedCircuitRatio, reportedCircuitRmTime, reportedCircuitQwSteps]

theorem abstract_order_of_magnitude_comparison :
    7 ≤ meanReportedRmRatio ∧ meanReportedRmRatio ≤ 8 ∧
    9 ≤ reportedDirectedGraphRatio ∧ reportedDirectedGraphRatio ≤ 10 ∧
    100 ≤ reportedCircuitRatio := by
  refine ⟨(table1_mean_ratio_between_seven_and_eight).1,
    (table1_mean_ratio_between_seven_and_eight).2, ?_, ?_, ?_⟩
  · norm_num [reportedDirectedGraphRatio]
  · norm_num [reportedDirectedGraphRatio]
  · norm_num [reportedCircuitRatio]

theorem section1_numerical_advantage :
    qwConstantFactor = 1.84 ∧
    1200 * qwConstantFactor ≤ previousUpperBoundConstant ∧
    (∀ r ∈ reportedRmRatios, 7 ≤ r) ∧
    7 ≤ meanReportedRmRatio ∧ meanReportedRmRatio ≤ 8 ∧
    3 ≤ reportedTotalComplexityGain ∧
    (36 : ℝ) < 281 ∧ (76 : ℝ) < 604 ∧ (120 : ℝ) < 963 ∧
    (176 : ℝ) < 1330 ∧ (232 : ℝ) < 1722 := by
  refine ⟨rfl, ?_, table1_ratio_ge_seven,
    (table1_mean_ratio_between_seven_and_eight).1,
    (table1_mean_ratio_between_seven_and_eight).2, ?_, ?_⟩
  · norm_num [qwConstantFactor, previousUpperBoundConstant]
  · norm_num [reportedTotalComplexityGain]
  · exact table1_qw_less_than_rm

end

end Qatlib.Papers.AdiabaticQLS23.MainResults
