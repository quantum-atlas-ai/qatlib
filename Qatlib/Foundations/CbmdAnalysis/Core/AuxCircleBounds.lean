/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Foundations.CbmdAnalysis.Core.AuxRegulator
import Qatlib.Foundations.CbmdAnalysis.Core.FinitePoleBounds
set_option warningAsError false

namespace Qatlib.Foundations.CbmdAnalysis.Core

set_option autoImplicit false
set_option maxHeartbeats 400000
noncomputable section
namespace CBMD
open Complex Metric Set Filter
open scoped Topology BigOperators
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

theorem auxContourIntegrand_circle_le (s : Finset ℂ) (hs : s.Nonempty)
    {a ρ : ℝ} (ha : 0 < a) (hρ : ρ ≤ 2 * Real.pi * a) (U : ℂ → E)
    (hU : ∀ z, ‖U z‖ ≤ Real.exp (max z.im 0 * ρ)) (n : ℕ)
    (hRa : 4 * a ≤ halfGridRadius a n) (hRs : finitePoleRadius s + 1 ≤ halfGridRadius a n)
    (z : ℂ) (hz : z ∈ sphere 0 (halfGridRadius a n)) :
    ‖auxContourIntegrand s a U z‖ ≤
      (∏ p ∈ s, ‖-Complex.I - p‖) * Real.exp |ρ| /
        (halfGridRadius a n - finitePoleRadius s) ^ 2 := by
  have hzn : ‖z‖ = halfGridRadius a n := by simpa only [mem_sphere_iff_norm, sub_zero] using! hz
  have hd0 : 0 < halfGridRadius a n - finitePoleRadius s := by linarith
  have hden := finite_pole_denominator_lower s hs (finitePoleRadius s)
    (finitePoleRadius_ge_one s) (norm_le_finitePoleRadius s) z (by rwa [hzn])
  rw [hzn] at hden
  have hLU : ‖latticePoleFactor a z‖ * ‖U z‖ ≤ Real.exp |ρ| :=
    (mul_le_mul_of_nonneg_left (hU z) (norm_nonneg _)).trans
      (lattice_circle_growth_le ha hρ n hRa z hzn)
  have hN : 0 ≤ ∏ p ∈ s, ‖-Complex.I - p‖ := Finset.prod_nonneg (fun _ _ => norm_nonneg _)
  rw [auxContourIntegrand, norm_smul, auxContourKernel_norm]
  calc
    _ = (∏ p ∈ s, ‖-Complex.I - p‖) * (‖latticePoleFactor a z‖ * ‖U z‖) /
        (‖z + Complex.I‖ * ∏ p ∈ s, ‖z - p‖) := by ring
    _ ≤ (∏ p ∈ s, ‖-Complex.I - p‖) * Real.exp |ρ| /
        (‖z + Complex.I‖ * ∏ p ∈ s, ‖z - p‖) :=
      div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hLU hN) (by positivity)
    _ ≤ _ := div_le_div_of_nonneg_left (mul_nonneg hN (Real.exp_pos _).le) (sq_pos_of_pos hd0) hden

theorem auxContour_circle_tendsto_zero (s : Finset ℂ) (hs : s.Nonempty)
    {a ρ : ℝ} (ha : 0 < a) (hρ : ρ ≤ 2 * Real.pi * a) (U : ℂ → E)
    (hU : ∀ z, ‖U z‖ ≤ Real.exp (max z.im 0 * ρ)) :
    Tendsto (fun n : ℕ => (2 * Real.pi * Complex.I : ℂ)⁻¹ •
      ∮ z in C(0, halfGridRadius a n), auxContourIntegrand s a U z) atTop (𝓝 0) := by
  have hR := halfGridRadius_tendsto ha
  have hd : Tendsto (fun n => halfGridRadius a n - finitePoleRadius s) atTop atTop := by
    simpa only [sub_eq_add_neg] using! tendsto_atTop_add_const_right atTop (-finitePoleRadius s) hR
  have hlim : Tendsto (fun n => 2 * ((∏ p ∈ s, ‖-Complex.I - p‖) * Real.exp |ρ|) /
      (halfGridRadius a n - finitePoleRadius s)) atTop (𝓝 0) := tendsto_const_nhds.div_atTop hd
  apply squeeze_zero_norm' _ hlim
  filter_upwards [hR.eventually_ge_atTop (4 * a), hR.eventually_ge_atTop (2 * (finitePoleRadius s + 1))]
    with n hRa hRs
  have hRs' : finitePoleRadius s + 1 ≤ halfGridRadius a n := by linarith [finitePoleRadius_ge_one s]
  have hd0 : 0 < halfGridRadius a n - finitePoleRadius s := by linarith
  have hN : 0 ≤ ∏ p ∈ s, ‖-Complex.I - p‖ := Finset.prod_nonneg (fun _ _ => norm_nonneg _)
  have hb := circleIntegral.norm_two_pi_i_inv_smul_integral_le_of_norm_le_const
    (show 0 ≤ halfGridRadius a n by dsimp [halfGridRadius]; positivity)
    (auxContourIntegrand_circle_le s hs ha hρ U hU n hRa hRs')
  apply hb.trans
  calc
    _ ≤ (2 * (halfGridRadius a n - finitePoleRadius s)) *
        ((∏ p ∈ s, ‖-Complex.I - p‖) * Real.exp |ρ| /
          (halfGridRadius a n - finitePoleRadius s) ^ 2) :=
      mul_le_mul_of_nonneg_right (by linarith) (by positivity)
    _ = _ := by field_simp

end CBMD

end
end Qatlib.Foundations.CbmdAnalysis.Core
