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

/-!
# Arithmetic checks for reported QLS benchmarks

Records the numerical constants and benchmark values used in [CostaEtAl2025] and verifies
arithmetic comparisons among them. The table checks compare reported ratios with the quotients
of the stored quantum-walk step counts and randomized-method times.

The theorem `section1_numerical_advantage` assembles the constant-factor comparison, ratio
bounds, reported total complexity gain, and inequalities between the five pairs of stored
counts.

## Main statements

* `measured_constant_factor_1200`: Checks `1200 * 1.84 ≤ 2305`.
* `table1_ratio_matches_data`: Checks the five reported ratios to tolerance `0.01`.
* `section1_numerical_advantage`: Collects the benchmark arithmetic statements.

## References

* [Costa et al., 2025][CostaEtAl2025]
-/

set_option autoImplicit false

namespace Qatlib.Papers.AdiabaticQLS23.MainResults

noncomputable section

/-- The reported quantum-walk constant factor `1.84`. -/
def qwConstantFactor : ℝ := 1.84

/-- The previous upper-bound constant `2305` used for the numerical comparison. -/
def previousUpperBoundConstant : ℝ := 2305

/-- The five reported randomized-method to quantum-walk ratios `[7.81, 7.95, 8.03, 7.56, 7.42]`. -/
def reportedRmRatios : List ℝ := [7.81, 7.95, 8.03, 7.56, 7.42]

/-- The five reported quantum-walk step counts `[36, 76, 120, 176, 232]`. -/
def reportedQwSteps : List ℝ := [36, 76, 120, 176, 232]

/-- The five reported randomized-method times `[281, 604, 963, 1330, 1722]`. -/
def reportedRmTimes : List ℝ := [281, 604, 963, 1330, 1722]

/-- The arithmetic mean of the five stored randomized-method to quantum-walk ratios. -/
def meanReportedRmRatio : ℝ := (7.81 + 7.95 + 8.03 + 7.56 + 7.42) / 5

/-- The reported total-complexity gain, stored as the real number three. -/
def reportedTotalComplexityGain : ℝ := 3

/-- The reported directed-graph quantum-walk step count `2416`. -/
def reportedDirectedGraphQwSteps : ℝ := 2416

/-- The reported directed-graph randomized-method time `23150`. -/
def reportedDirectedGraphRmTime : ℝ := 23150

/-- The reported directed-graph ratio `9.58`. -/
def reportedDirectedGraphRatio : ℝ := 9.58

/-- The reported circuit benchmark quantum-walk step count `39800`. -/
def reportedCircuitQwSteps : ℝ := 39800

/-- The reported circuit benchmark randomized-method time `18170000`. -/
def reportedCircuitRmTime : ℝ := 18170000

/-- The reported circuit benchmark ratio `457`. -/
def reportedCircuitRatio : ℝ := 457

/-- If `α = 1.84` and `U = 2305`, then `1200 * α ≤ U`. See [CostaEtAl2025]. -/
theorem measured_constant_factor_1200 {α U : ℝ} (hα : α = 1.84) (hU : U = 2305) :
    1200 * α ≤ U := by
  subst hα
  subst hU
  norm_num

/-- If `α = 1.84` and `U = 2305`, then `1250 * α ≤ U`. See [CostaEtAl2025]. -/
theorem measured_constant_factor_1250 {α U : ℝ} (hα : α = 1.84) (hU : U = 2305) :
    1250 * α ≤ U := by
  subst hα
  subst hU
  norm_num

/-- Each of the five stored Table 1 ratios is at least seven. See [CostaEtAl2025]. -/
theorem table1_ratio_ge_seven :
    ∀ r ∈ reportedRmRatios, 7 ≤ r := by
  intro r hr
  simp [reportedRmRatios] at hr
  rcases hr with h | h | h | h | h <;> subst h <;> norm_num

/-- The mean of the stored Table 1 ratios lies between seven and eight. See [CostaEtAl2025]. -/
theorem table1_mean_ratio_between_seven_and_eight :
    7 ≤ meanReportedRmRatio ∧ meanReportedRmRatio ≤ 8 := by
  constructor <;> norm_num [meanReportedRmRatio]

/-- Each of the five specified quantum-walk counts is strictly less than its paired
randomized-method time. See [CostaEtAl2025]. -/
theorem table1_qw_less_than_rm :
    (36 : ℝ) < 281 ∧ (76 : ℝ) < 604 ∧ (120 : ℝ) < 963 ∧
    (176 : ℝ) < 1330 ∧ (232 : ℝ) < 1722 := by
  norm_num

/-- Each stored Table 1 ratio differs from its corresponding time-to-step quotient by at most `1
/ 100`. See [CostaEtAl2025]. -/
theorem table1_ratio_matches_data :
    |(781 / 100 : ℝ) - 281 / 36| ≤ 1 / 100 ∧
    |(795 / 100 : ℝ) - 604 / 76| ≤ 1 / 100 ∧
    |(803 / 100 : ℝ) - 963 / 120| ≤ 1 / 100 ∧
    |(756 / 100 : ℝ) - 1330 / 176| ≤ 1 / 100 ∧
    |(742 / 100 : ℝ) - 1722 / 232| ≤ 1 / 100 := by
  norm_num

/-- The reported directed-graph ratio differs from the quotient of its stored time and step
count by at most `0.01`. See [CostaEtAl2025]. -/
theorem table2_directed_ratio_matches_data :
    |reportedDirectedGraphRatio - reportedDirectedGraphRmTime / reportedDirectedGraphQwSteps|
      ≤ 0.01 := by
  norm_num [reportedDirectedGraphRatio, reportedDirectedGraphRmTime,
    reportedDirectedGraphQwSteps]

/-- The reported circuit ratio differs from the quotient of its stored time and step count by at
most one. See [CostaEtAl2025]. -/
theorem table2_circuit_ratio_matches_data :
    |reportedCircuitRatio - reportedCircuitRmTime / reportedCircuitQwSteps| ≤ 1 := by
  norm_num [reportedCircuitRatio, reportedCircuitRmTime, reportedCircuitQwSteps]

/-- The stored mean Table 1 ratio lies in `[7, 8]`, the directed-graph ratio lies in `[9, 10]`,
and the circuit ratio is at least 100. See [CostaEtAl2025]. -/
theorem abstract_order_of_magnitude_comparison :
    7 ≤ meanReportedRmRatio ∧ meanReportedRmRatio ≤ 8 ∧
    9 ≤ reportedDirectedGraphRatio ∧ reportedDirectedGraphRatio ≤ 10 ∧
    100 ≤ reportedCircuitRatio := by
  refine ⟨(table1_mean_ratio_between_seven_and_eight).1,
    (table1_mean_ratio_between_seven_and_eight).2, ?_, ?_, ?_⟩
  · norm_num [reportedDirectedGraphRatio]
  · norm_num [reportedDirectedGraphRatio]
  · norm_num [reportedCircuitRatio]

/-- Collects the stored constant `1.84`, its factor-1200 comparison with the prior bound, the
Table 1 ratio bounds, the reported gain of at least three, and the five strict count
comparisons. See [CostaEtAl2025]. -/
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
