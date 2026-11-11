/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Analysis.Asymptotics.Theta
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Qatlib.Papers.Connectivity14.MainResults.TwoLevel

/-!
# Two-stage effective simplex search

This module defines the size, coupling parameters, two-level stage Hamiltonians, and stage times
for the simplex-of-complete-graphs effective model of [MeyerWong2015]. Each stage has an exact
sine-squared transition probability and reaches probability one at its specified time for
positive `M`.

The total time `simplexTotalTime` is asymptotically comparable to `M * sqrt M` and to `nPow34
(simplexN M)`, expressing the three-quarter-power scale in the derived size parameter.

## Main statements

* `simplex_stage1_success_at_peak`: The first effective stage reaches transition probability
  one.
* `simplex_stage2_success_at_peak`: The second effective stage reaches transition probability
  one.
* `simplex_total_runtime_isTheta_N`: The total stage time has the three-quarter-power size
  scale.

## References

* [Meyer and Wong, 2015][MeyerWong2015]
-/

set_option backward.isDefEq.respectTransparency false
set_option warningAsError false

set_option autoImplicit false
noncomputable section

open Qatlib.Foundations.PureStateMath
open scoped Matrix Matrix.Norms.L2Operator

namespace Qatlib.Papers.Connectivity14.MainResults

/-- The size expression `M * (M + 1)` for the simplex-of-complete-graphs model. -/
def simplexN (M : ℝ) : ℝ := M * (M + 1)

/-- The first-stage critical-coupling expression `(-M + sqrt(M * (M + 8))) / (2 * M)`. -/
def gammaC1 (M : ℝ) : ℝ := (-M + Real.sqrt (M * (M + 8))) / (2 * M)

/-- For positive `M`, the first-stage critical coupling satisfies `2 * M * gammaC1 M + M =
sqrt(M * (M + 8))`, as used in [MeyerWong2015]. -/
theorem gammaC1_key (M : ℝ) (hM : 0 < M) :
    2 * M * gammaC1 M + M = Real.sqrt (M * (M + 8)) := by
  unfold gammaC1
  have hM0 : M ≠ 0 := hM.ne'
  field_simp
  ring

/-- The second-stage critical-coupling expression `1 / M`. -/
def gammaC2 (M : ℝ) : ℝ := 1 / M

/-- The first-stage coupling scale `2 / (M * sqrt M)`. -/
def stage1Gap (M : ℝ) : ℝ := 2 / (M * Real.sqrt M)

/-- The second-stage coupling scale `1 / sqrt M`. -/
def stage2Gap (M : ℝ) : ℝ := 1 / Real.sqrt M

/-- The first effective two-level Hamiltonian, with diagonal parameter `4 / M - 2` and
off-diagonal parameter `-stage1Gap M`. -/
def simplexStage (M : ℝ) : Matrix (Fin 2) (Fin 2) ℂ :=
  twoLevelH (4 / M - 2) (-(stage1Gap M))

/-- The second effective two-level Hamiltonian, with diagonal parameter `-1` and off-diagonal
parameter `-stage2Gap M`. -/
def simplexStage_core (M : ℝ) : Matrix (Fin 2) (Fin 2) ℂ :=
  twoLevelH (-1) (-(stage2Gap M))

/-- The first-stage time `(π / 4) * M * sqrt M`. -/
def simplexTime1 (M : ℝ) : ℝ := Real.pi / 4 * (M * Real.sqrt M)

/-- The second-stage time `(π / 2) * sqrt M`. -/
def simplexTime2 (M : ℝ) : ℝ := Real.pi / 2 * Real.sqrt M

/-- The sum of the first- and second-stage times. -/
def simplexTotalTime (M : ℝ) : ℝ := simplexTime1 M + simplexTime2 M

/-- The first effective stage has coordinate-zero transition probability `sin(stage1Gap M * t) ^
2`, as in the stage model associated with [MeyerWong2015]. -/
theorem simplex_stage1_success_prob (M t : ℝ) :
    ‖(HamiltonianEvolution (simplexStage M) t *ᵥ twoKet1) 0‖ ^ 2 =
      Real.sin (stage1Gap M * t) ^ 2 := by
  unfold simplexStage
  rw [twoLevel_transition_prob]
  have harg : -(stage1Gap M) * t = -(stage1Gap M * t) := by ring
  rw [harg, Real.sin_neg, neg_pow]
  ring

/-- For positive `M`, the first-stage coupling scale multiplied by `simplexTime1 M` equals `π /
2`. -/
theorem simplex_stage1_gap_mul_time (M : ℝ) (hM : 0 < M) :
    stage1Gap M * simplexTime1 M = Real.pi / 2 := by
  unfold stage1Gap simplexTime1
  have hM0 : M ≠ 0 := hM.ne'
  have hs : Real.sqrt M ≠ 0 := (Real.sqrt_pos.2 hM).ne'
  field_simp <;> norm_num

/-- For positive `M`, the first effective stage reaches coordinate-zero transition probability
one at `simplexTime1 M`. See [MeyerWong2015]. -/
theorem simplex_stage1_success_at_peak (M : ℝ) (hM : 0 < M) :
    ‖(HamiltonianEvolution (simplexStage M) (simplexTime1 M) *ᵥ twoKet1) 0‖ ^ 2 = 1 := by
  rw [simplex_stage1_success_prob, simplex_stage1_gap_mul_time M hM,
    Real.sin_pi_div_two]
  norm_num

/-- The second effective stage has coordinate-zero transition probability `sin(stage2Gap M * t)
^ 2`, as in the stage model associated with [MeyerWong2015]. -/
theorem simplex_stage2_success_prob (M t : ℝ) :
    ‖(HamiltonianEvolution (simplexStage_core M) t *ᵥ twoKet1) 0‖ ^ 2 =
      Real.sin (stage2Gap M * t) ^ 2 := by
  unfold simplexStage_core
  rw [twoLevel_transition_prob]
  have harg : -(stage2Gap M) * t = -(stage2Gap M * t) := by ring
  rw [harg, Real.sin_neg, neg_pow]
  ring

/-- For positive `M`, the second-stage coupling scale multiplied by `simplexTime2 M` equals `π /
2`. -/
theorem simplex_stage2_gap_mul_time (M : ℝ) (hM : 0 < M) :
    stage2Gap M * simplexTime2 M = Real.pi / 2 := by
  unfold stage2Gap simplexTime2
  have hs : Real.sqrt M ≠ 0 := (Real.sqrt_pos.2 hM).ne'
  field_simp <;> norm_num

/-- For positive `M`, the second effective stage reaches coordinate-zero transition probability
one at `simplexTime2 M`. See [MeyerWong2015]. -/
theorem simplex_stage2_success_at_peak (M : ℝ) (hM : 0 < M) :
    ‖(HamiltonianEvolution (simplexStage_core M) (simplexTime2 M) *ᵥ twoKet1) 0‖ ^ 2 = 1 := by
  rw [simplex_stage2_success_prob, simplex_stage2_gap_mul_time M hM,
    Real.sin_pi_div_two]
  norm_num

/-- As `M` tends to infinity, `simplexTotalTime M` is asymptotically comparable to `M * sqrt M`,
the two-stage effective runtime scale in [MeyerWong2015]. -/
theorem simplex_total_runtime_isTheta :
    Asymptotics.IsTheta Filter.atTop simplexTotalTime
      (fun M : ℝ => M * Real.sqrt M) := by
  constructor
  · have h1 : (fun M : ℝ => Real.pi / 4 * (M * Real.sqrt M)) =O[Filter.atTop]
        (fun M : ℝ => M * Real.sqrt M) :=
      (Asymptotics.isBigO_refl (fun M : ℝ => M * Real.sqrt M) Filter.atTop).const_mul_left _
    have h2 : (fun M : ℝ => Real.pi / 2 * Real.sqrt M) =O[Filter.atTop]
        (fun M : ℝ => M * Real.sqrt M) := by
      refine Asymptotics.IsBigO.of_bound (Real.pi / 2) ?_
      filter_upwards [Filter.eventually_ge_atTop (1 : ℝ)] with M hM
      have hMn : (0 : ℝ) ≤ Real.pi / 2 * Real.sqrt M := by positivity
      have hgn : (0 : ℝ) ≤ M * Real.sqrt M := by positivity
      rw [Real.norm_of_nonneg hMn, Real.norm_of_nonneg hgn]
      have hle : Real.sqrt M ≤ M * Real.sqrt M := by
        calc Real.sqrt M = 1 * Real.sqrt M := (one_mul _).symm
          _ ≤ M * Real.sqrt M := by
              apply mul_le_mul_of_nonneg_right hM (Real.sqrt_nonneg _)
      calc Real.pi / 2 * Real.sqrt M ≤ Real.pi / 2 * (M * Real.sqrt M) := by
            apply mul_le_mul_of_nonneg_left hle (by positivity)
        _ = Real.pi / 2 * (M * Real.sqrt M) := rfl
    have hsum := h1.add h2
    simpa [simplexTotalTime, simplexTime1, simplexTime2] using! hsum
  · refine Asymptotics.IsBigO.of_bound (4 / Real.pi) ?_
    filter_upwards [Filter.eventually_ge_atTop (0 : ℝ)] with M hM
    have hMn : (0 : ℝ) ≤ M * Real.sqrt M := by positivity
    have htn : (0 : ℝ) ≤ simplexTotalTime M := by
      unfold simplexTotalTime simplexTime1 simplexTime2
      positivity
    rw [Real.norm_of_nonneg hMn, Real.norm_of_nonneg htn]
    have hcoef : (4 / Real.pi) * (Real.pi / 4) = 1 := by
      field_simp
    calc M * Real.sqrt M = (4 / Real.pi) * (Real.pi / 4 * (M * Real.sqrt M)) := by
          rw [← mul_assoc, hcoef, one_mul]
      _ ≤ (4 / Real.pi) * simplexTotalTime M := by
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          unfold simplexTotalTime simplexTime1 simplexTime2
          have h2 : (0 : ℝ) ≤ Real.pi / 2 * Real.sqrt M := by positivity
          linarith

/-- The nested-square-root expression `sqrt N * sqrt(sqrt N)` representing the
three-quarter-power size scale for nonnegative `N`. -/
def nPow34 (N : ℝ) : ℝ := Real.sqrt N * Real.sqrt (Real.sqrt N)

/-- As `M` tends to infinity, `M * sqrt M` is asymptotically comparable to `nPow34 (simplexN
M)`. -/
theorem simplex_nPow34_isTheta :
    Asymptotics.IsTheta Filter.atTop (fun M : ℝ => M * Real.sqrt M)
      (fun M : ℝ => nPow34 (simplexN M)) := by
  constructor
  · refine Asymptotics.IsBigO.of_bound 1 ?_
    filter_upwards [Filter.eventually_ge_atTop (1 : ℝ)] with M hM
    have hM0 : (0 : ℝ) ≤ M := by linarith
    have hN0 : (0 : ℝ) ≤ simplexN M := by unfold simplexN; positivity
    have hsq1 : M ≤ Real.sqrt (simplexN M) := by
      calc M = Real.sqrt (M * M) := (Real.sqrt_mul_self hM0).symm
        _ ≤ Real.sqrt (simplexN M) := by
            apply Real.sqrt_le_sqrt
            unfold simplexN
            nlinarith
    have hsq2 : Real.sqrt M ≤ Real.sqrt (Real.sqrt (simplexN M)) := by
      apply Real.sqrt_le_sqrt
      exact hsq1
    have hmn : (0 : ℝ) ≤ M * Real.sqrt M := by positivity
    have hnn : (0 : ℝ) ≤ nPow34 (simplexN M) := by unfold nPow34; positivity
    rw [Real.norm_of_nonneg hmn, Real.norm_of_nonneg hnn, one_mul]
    unfold nPow34
    exact mul_le_mul hsq1 hsq2 (Real.sqrt_nonneg M) (Real.sqrt_nonneg (simplexN M))
  · refine Asymptotics.IsBigO.of_bound (2 * Real.sqrt 2) ?_
    filter_upwards [Filter.eventually_ge_atTop (1 : ℝ)] with M hM
    have hM0 : (0 : ℝ) ≤ M := by linarith
    have hN0 : (0 : ℝ) ≤ simplexN M := by unfold simplexN; positivity
    have hsq1 : Real.sqrt (simplexN M) ≤ M + 1 := by
      calc Real.sqrt (simplexN M) ≤ Real.sqrt ((M + 1) * (M + 1)) := by
            apply Real.sqrt_le_sqrt
            unfold simplexN
            nlinarith
        _ = M + 1 := Real.sqrt_mul_self (by linarith)
    have hsq2 : Real.sqrt (Real.sqrt (simplexN M)) ≤ Real.sqrt (M + 1) := by
      apply Real.sqrt_le_sqrt
      exact hsq1
    have hsqrt_le : Real.sqrt (M + 1) ≤ Real.sqrt 2 * Real.sqrt M := by
      rw [← Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 2)]
      apply Real.sqrt_le_sqrt
      nlinarith
    have hM1 : M + 1 ≤ 2 * M := by nlinarith
    have hprod : (M + 1) * Real.sqrt (M + 1) ≤
        (2 * M) * (Real.sqrt 2 * Real.sqrt M) := by
      apply mul_le_mul hM1 hsqrt_le (Real.sqrt_nonneg _) (by positivity)
    have heq : (2 * M) * (Real.sqrt 2 * Real.sqrt M) =
        (2 * Real.sqrt 2) * (M * Real.sqrt M) := by ring
    have hup : nPow34 (simplexN M) ≤ (M + 1) * Real.sqrt (M + 1) := by
      unfold nPow34
      exact mul_le_mul hsq1 hsq2 (Real.sqrt_nonneg _) (by positivity)
    have hmn : (0 : ℝ) ≤ M * Real.sqrt M := by positivity
    have hnn : (0 : ℝ) ≤ nPow34 (simplexN M) := by unfold nPow34; positivity
    rw [Real.norm_of_nonneg hnn, Real.norm_of_nonneg hmn]
    calc nPow34 (simplexN M) ≤ (M + 1) * Real.sqrt (M + 1) := hup
      _ ≤ (2 * M) * (Real.sqrt 2 * Real.sqrt M) := hprod
      _ = (2 * Real.sqrt 2) * (M * Real.sqrt M) := heq

/-- As `M` tends to infinity, the total effective stage time is asymptotically comparable to
`nPow34 (simplexN M)`, giving the three-quarter-power size scale associated with
[MeyerWong2015]. -/
theorem simplex_total_runtime_isTheta_N :
    Asymptotics.IsTheta Filter.atTop simplexTotalTime
      (fun M : ℝ => nPow34 (simplexN M)) :=
  simplex_total_runtime_isTheta.trans simplex_nPow34_isTheta

end Qatlib.Papers.Connectivity14.MainResults
