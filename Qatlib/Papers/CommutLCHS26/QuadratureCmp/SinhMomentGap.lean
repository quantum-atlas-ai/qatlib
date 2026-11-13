/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.CommutLCHS26.QuadratureCmp.SinhBudget
import Qatlib.Papers.CommutLCHS26.QuadratureCmp.SinhMoments

/-!
# A gap in uniform sinh moment bounds

This module constructs a family of budget-selected sinh rules in the setting of
[AftabAnTrivisa2026] whose zeroth moments exceed every fixed multiple of the proposed moment
growth factor. The choice `unitBudget` forces unit mesh step, while the sinh scale grows as
`2c`.

The witness remains within the analytic-width conditions and shows why an unrestricted scale
cannot satisfy the displayed uniform moment bound.

## Main statements

* `selected_moment_exceeds`: a selected rule exceeding any prescribed positive bound constant.
* `not_uniform_selected_moment_bound`: failure of a uniform bound over the witness family.

## References

* [Aftab et al., 2026][AftabAnTrivisa2026]
-/

set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false
noncomputable section
namespace Qatlib.Papers.CommutLCHS26.QuadratureCmp.SinhMomentGap
open Complex Matrix Set Filter MeasureTheory
open scoped Topology BigOperators Matrix.Norms.L2Operator ComplexOrder
open Qatlib.Papers.CommutLCHS26.MainResults.KernelStrip
open Qatlib.Papers.CommutLCHS26.MainResults.SinhStrip
open Qatlib.Papers.CommutLCHS26.MainResults.SinhWidth
open Qatlib.Papers.CommutLCHS26.QuadratureCmp.SinhRule
open Qatlib.Papers.CommutLCHS26.QuadratureCmp.SinhError
open Qatlib.Papers.CommutLCHS26.QuadratureCmp.TailBudget
open Qatlib.Papers.CommutLCHS26.QuadratureCmp.Trapezoid (cutoff)
variable {ι : Type} [Fintype ι] [DecidableEq ι]
local instance : ContinuousENorm (Matrix ι ι ℂ) :=
  SeminormedAddGroup.toESeminormedAddMonoid.toContinuousENorm

open Qatlib.Papers.CommutLCHS26.QuadratureCmp.SinhBudget
open Qatlib.Papers.CommutLCHS26.QuadratureCmp.SinhMoments

/-- The mesh budget `2M / (exp (2πβ) - 1)` that selects unit mesh step. -/
def unitBudget (β M : ℝ) : ℝ := 2 * M / (Real.exp (2 * Real.pi * β) - 1)

/-- The unit-step budget is positive for positive strip half-width and mass. -/
theorem unitBudget_pos {β M : ℝ} (hβ : 0 < β) (hM : 0 < M) : 0 < unitBudget β M := by
  have hd : 0 < Real.exp (2 * Real.pi * β) - 1 :=
      sub_pos.mpr (Real.one_lt_exp_iff.mpr (by positivity))
  exact div_pos (by positivity) hd

/-- The mesh logarithm for the unit-step budget equals `2πβ` when both parameters are positive. -/
theorem meshLog_unitBudget {β M : ℝ} (hβ : 0 < β) (hM : 0 < M) :
    meshLog M (unitBudget β M) = 2 * Real.pi * β := by
  have hd : Real.exp (2 * Real.pi * β) - 1 ≠ 0 :=
    (sub_pos.mpr (Real.one_lt_exp_iff.mpr (by positivity))).ne'
  have he : 1 + 2 * M / unitBudget β M = Real.exp (2 * Real.pi * β) := by
    unfold unitBudget
    field_simp
    ring
  unfold meshLog
  rw [he, Real.log_exp]

/-- The unit-step budget makes the selected mesh step equal to one. -/
theorem step_unitBudget {β M : ℝ} (hβ : 0 < β) (hM : 0 < M) : step β M (unitBudget β M) = 1 := by
  unfold step
  rw [meshLog_unitBudget hβ hM, div_self (by positivity : 2 * Real.pi * β ≠ 0), min_self]

/-- The witness strip half-width `1 / (4c)`. -/
def witnessBeta (c : ℝ) : ℝ := 1 / (4 * c)

/-- For `c ≥ 1`, the witness half-width is positive, below `π / 4`, and below the analytic width
for the specified two-dimensional zero-generator instance. -/
theorem witness_width {c : ℝ} (hc : 1 ≤ c) :
    0 < witnessBeta c ∧ witnessBeta c < Real.pi / 4 ∧
      ((witnessBeta c : ℝ) : EReal) < analyticWidth 2 1 c 1 1 (2 * c)
        (0 : Matrix (Fin 2) (Fin 2) ℂ) 0 := by
  have hc₀ : 0 < c := by linarith
  have hβ₀ : 0 < witnessBeta c := by unfold witnessBeta; positivity
  have hβ₁ : witnessBeta c ≤ 1/4 := by
    unfold witnessBeta
    apply one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 4)
    nlinarith
  have hβπ : witnessBeta c < Real.pi / 4 := by linarith [Real.pi_gt_three]
  have he : (2 * c) * witnessBeta c = 1/2 := by unfold witnessBeta; field_simp; ring
  have hsin : (2 * c) * Real.sin (witnessBeta c) < 1 := by
    have h := mul_le_mul_of_nonneg_left (Real.sin_le hβ₀.le) (show 0 ≤ 2 * c by positivity)
    rw [he] at h
    linarith
  exact ⟨hβ₀, hβπ, lt_width_of_gaps 2 (by positivity) hβ₀.le (by linarith [Real.pi_pos])
    1 c 1 1 (0 : Matrix (Fin 2) (Fin 2) ℂ) 0 hsin (Or.inr hsin)⟩

/-- The strip mass of the specified witness instance is positive for `c ≥ 1`. -/
theorem witness_mass_pos {c : ℝ} (hc : 1 ≤ c) :
    0 < stripMass 2 1 c 1 (2 * c) (witnessBeta c) 0 := by
  obtain ⟨hβ₀, hβπ, hw⟩ := witness_width hc
  simpa only [norm_zero, mul_zero] using! stripMass_pos 2 1 c 1 (2 * c) (witnessBeta c)
    (by norm_num) (by linarith) (by positivity) hβ₀.le hβπ 1
    (0 : Matrix (Fin 2) (Fin 2) ℂ) 0 hw

/-- For every positive `C`, a budget-selected witness with sinh scale `2c` and unit mesh step
has zeroth moment strictly exceeding `kernelScale * C * momentGrowth`. -/
theorem selected_moment_exceeds (C : ℝ) (hC : 0 < C) :
    ∃ c : ℝ, 1 ≤ c ∧
      let β := witnessBeta c
      let M := stripMass 2 1 c 1 (2 * c) β 0
      let εm := unitBudget β M
      let εt := tailConstant 2 1 c 1
      let h := step β M εm
      let Y := selectedWindow 2 1 c 1 (2 * c) εt
      0 < εm ∧ 0 < εt ∧ 0 < h ∧ h = 1 ∧ 1 ≤ Y ∧
        (β : EReal) < analyticWidth 2 1 c 1 1 (2 * c) (0 : Matrix (Fin 2) (Fin 2) ℂ) 0 ∧
        Qatlib.Papers.CommutLCHS26.QuadratureCmp.Moments.kernelScale 2 1 c 1 * C *
          Qatlib.Papers.CommutLCHS26.QuadratureCmp.Moments.momentGrowth 2 0 c <
          moment 2 1 c 1 0 (2 * c) h (cutoff Y h) := by
  let c := C + 1
  have hc : 1 ≤ c := by dsimp [c]; linarith
  have hc₀ : 0 < c := by linarith
  obtain ⟨hβ₀, _, hw⟩ := witness_width hc
  have hM := witness_mass_pos hc
  have hh := step_unitBudget hβ₀ hM
  refine ⟨c, hc, unitBudget_pos hβ₀ hM, tailConstant_pos 2 1 c 1 (by norm_num) hc₀, ?_, hh, ?_, hw,
      ?_⟩
  · rw [hh]
    norm_num
  · exact le_max_left _ _
  · rw [hh]
    have hs : 0 < Qatlib.Papers.CommutLCHS26.QuadratureCmp.Moments.kernelScale 2 1 c 1 := by
      unfold Qatlib.Papers.CommutLCHS26.QuadratureCmp.Moments.kernelScale
      positivity
    have hg : Qatlib.Papers.CommutLCHS26.QuadratureCmp.Moments.momentGrowth 2 0 c = 1 := by
      norm_num [Qatlib.Papers.CommutLCHS26.QuadratureCmp.Moments.momentGrowth]
    have hcentral := central_le_moment 2 1 c 1 (2 * c) 1 (by norm_num) (by positivity) (by norm_num)
      (cutoff (selectedWindow 2 1 c 1 (2 * c) (tailConstant 2 1 c 1)) 1)
    norm_num only [one_mul, one_pow, div_one] at hcentral
    rw [hg, mul_one]
    have he : C < 2 * c := by dsimp [c]; linarith
    exact (mul_lt_mul_of_pos_left he hs).trans_le (by simpa only [mul_comm] using! hcentral)

/-- No positive constant uniformly bounds the selected zeroth moments of the witness family by
`kernelScale * momentGrowth` for all `c ≥ 1`. -/
theorem not_uniform_selected_moment_bound :
    ¬ ∃ C : ℝ, 0 < C ∧ ∀ c : ℝ, 1 ≤ c →
      let β := witnessBeta c
      let M := stripMass 2 1 c 1 (2 * c) β 0
      let h := step β M (unitBudget β M)
      let Y := selectedWindow 2 1 c 1 (2 * c) (tailConstant 2 1 c 1)
      moment 2 1 c 1 0 (2 * c) h (cutoff Y h) ≤
        Qatlib.Papers.CommutLCHS26.QuadratureCmp.Moments.kernelScale 2 1 c 1 * C *
          Qatlib.Papers.CommutLCHS26.QuadratureCmp.Moments.momentGrowth 2 0 c := by
  rintro ⟨C, hC, hall⟩
  obtain ⟨c, hc, hm, ht, hh, hunit, hY, hw, hlt⟩ := selected_moment_exceeds C hC
  exact (not_lt_of_ge (hall c hc)) hlt

end Qatlib.Papers.CommutLCHS26.QuadratureCmp.SinhMomentGap
