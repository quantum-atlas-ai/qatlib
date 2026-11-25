/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Papers.QChemImprove14.MainResults.FactorDomain

@[expose] public section

/-!
# A continuous magnitude correction for signed gaps

The positive-gap branch of Eq. (7) in arXiv:1403.1539v2 equals the inverse
half-angle cosine. The printed quotient is odd off zero. Using its magnitude
for negative gaps gives the even correction consistent with the magnitude
and continuous-time limit stated for Eq. (8).
-/

set_option autoImplicit false

open Filter
open scoped Topology
open Qatlib.Papers.QChemImprove14.MainResults
open Qatlib.Papers.QChemImprove14.MainResults.FactorDomain

namespace Qatlib.Papers.QChemImprove14.MainResults

/-- The positive-gap magnitude correction applied to an absolute gap, with value one at zero. -/
noncomputable def continuousGapFactor (x : ℝ) : ℝ :=
  if x = 0 then 1 else trotterFactor |x|

/-- On the physical interval around zero the correction is exactly the half-angle secant. -/
theorem continuousGapFactor_eq_sec {x : ℝ} (hx : |x| < Real.pi) :
    continuousGapFactor x = 1 / Real.cos (x / 2) := by
  by_cases h : x = 0
  · subst x
    simp [continuousGapFactor]
  · rw [continuousGapFactor, ite_eq_right h, trotterFactor_eq_inv_cos _ (abs_pos.mpr h) hx]
    rcases le_or_gt 0 x with h0 | h0
    · rw [abs_of_nonneg h0]
    · rw [abs_of_neg h0, neg_div, Real.cos_neg]

/-- The even magnitude correction tends to one at zero without a sign condition on the gap. -/
theorem continuousGapFactor_tendsto : Tendsto continuousGapFactor (𝓝 (0 : ℝ)) (𝓝 1) := by
  have hsec : ContinuousAt (fun x : ℝ => 1 / Real.cos (x / 2)) 0 := by
    apply ContinuousAt.div continuousAt_const
    · fun_prop
    · simp
  have hlim : Tendsto (fun x : ℝ => 1 / Real.cos (x / 2)) (𝓝 (0 : ℝ)) (𝓝 1) := by
    simpa using hsec.tendsto
  have hev : continuousGapFactor =ᶠ[𝓝 0] fun x => 1 / Real.cos (x / 2) := by
    filter_upwards [Metric.ball_mem_nhds (0 : ℝ) Real.pi_pos] with x hx
    apply continuousGapFactor_eq_sec
    simpa [Metric.mem_ball, Real.dist_eq] using hx
  exact Tendsto.congr' hev.symm hlim

/-- Equation (8)'s magnitude-corrected coefficient returns to the input coefficient as the
time step shrinks, for any real linear combination of frequencies. -/
theorem correctedCoefficient_tendsto (c gap : ℝ) :
    Tendsto (fun δ : ℝ => c * continuousGapFactor (δ * gap)) (𝓝[>] (0 : ℝ)) (𝓝 c) := by
  have hgap : Tendsto (fun δ : ℝ => δ * gap) (𝓝 0) (𝓝 0) := by
    simpa using (tendsto_id.mul_const gap : Tendsto (fun δ : ℝ => δ * gap) (𝓝 0) (𝓝 (0 * gap)))
  simpa only [mul_one, Function.comp_def] using
    ((continuousGapFactor_tendsto.comp hgap).const_mul c).mono_left nhdsWithin_le_nhds

/-- Replacing only the value of the printed odd quotient at zero leaves its negative-gap
right-step limit equal to minus one. -/
theorem pointPatch_negativeGap {gap : ℝ} (hg : gap < 0) :
    Tendsto (fun δ : ℝ => if δ * gap = 0 then 1 else trotterFactor (δ * gap))
      (𝓝[>] (0 : ℝ)) (𝓝 (-1)) := by
  have hpos : Tendsto (fun δ : ℝ => δ * (-gap)) (𝓝[>] (0 : ℝ)) (𝓝[>] (0 : ℝ)) := by
    apply tendsto_nhdsWithin_iff.mpr
    refine ⟨?_, ?_⟩
    · have h : Tendsto (fun δ : ℝ => δ * (-gap)) (𝓝 (0 : ℝ)) (𝓝 0) := by
        simpa using (tendsto_id.mul_const (-gap) : Tendsto (fun δ : ℝ => δ * (-gap)) (𝓝 0)
          (𝓝 (0 * (-gap))))
      exact h.mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with δ hδ
      exact mul_pos hδ (neg_pos.mpr hg)
  have he : (fun δ : ℝ => if δ * gap = 0 then 1 else trotterFactor (δ * gap)) =ᶠ[𝓝[>] 0]
      (fun δ : ℝ => -trotterFactor (δ * (-gap))) := by
    filter_upwards [self_mem_nhdsWithin] with δ hδ
    rw [ite_eq_right (mul_ne_zero (ne_of_gt hδ) hg.ne), mul_neg, factorOdd, neg_neg]
  exact Tendsto.congr' he.symm ((trotterFactor_tendsto_one.comp hpos).neg)

end Qatlib.Papers.QChemImprove14.MainResults
