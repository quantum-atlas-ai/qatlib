/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Papers.SuperfluidHel18.CenterlineCL.OrientedVorticity

import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-!
# Removing the Gauss denominator cutoff

The regularized kernel is a scalar multiple of the full kernel with
factor in the unit interval. Its error is supported where the two
positions are closer than the cutoff. This isolates the part of
the interaction requiring uniform control for a weak limit.
-/

@[expose] public section
set_option autoImplicit false

namespace Qatlib.Papers.SuperfluidHel18.CenterlineCL

open Filter MeasureTheory Set
open Qatlib.Papers.KnottedLight08.HopfField (dot3 cross3)
open scoped Real Topology

/-- The softened kernel differs from the full kernel only by the cube
of the ratio of the original and softened chord lengths. -/
theorem gaussSoftKernel_eq_scale_full (δ : ℝ) (hδ : 0 < δ) (p q : VorticityElement) :
    gaussSoftKernel δ p q =
      (euclideanLength (p.1 - q.1) / max δ (euclideanLength (p.1 - q.1))) ^ 3 *
        gaussSoftKernel 0 p q := by
  let d := euclideanLength (p.1 - q.1)
  have hd : 0 ≤ d := norm_nonneg _
  have hm : 0 < max δ d := hδ.trans_le (le_max_left _ _)
  by_cases hz : d = 0
  · have hsub : p.1 - q.1 = 0 := norm_eq_zero.mp
      (le_antisymm ((norm_le_euclideanLength _).trans_eq hz) (norm_nonneg _))
    simp only [gaussSoftKernel, hsub]
    simp [dot3, cross3]
  · let N := dot3 p.2.val (cross3 q.2.val (p.1 - q.1))
    change N / (4 * π * max δ d ^ 3) = (d / max δ d) ^ 3 * (N / (4 * π * max 0 d ^ 3))
    rw [max_eq_right hd]
    field_simp [hz, hm.ne', Real.pi_ne_zero]

/-- Putting a floor on the denominator does not increase the kernel magnitude. -/
theorem abs_gaussSoftKernel_le_full {δ : ℝ} (hδ : 0 < δ) (p q : VorticityElement) :
    |gaussSoftKernel δ p q| ≤ |gaussSoftKernel 0 p q| := by
  let d := euclideanLength (p.1 - q.1)
  have hd : 0 ≤ d := norm_nonneg _
  have hm : 0 < max δ d := hδ.trans_le (le_max_left _ _)
  have h₀ : 0 ≤ (d / max δ d) ^ 3 := pow_nonneg (div_nonneg hd hm.le) _
  have h₁ : (d / max δ d) ^ 3 ≤ 1 :=
    pow_le_one₀ (div_nonneg hd hm.le) ((div_le_one hm).2 (le_max_right _ _))
  rw [gaussSoftKernel_eq_scale_full δ hδ, abs_mul, abs_of_nonneg h₀]
  exact mul_le_of_le_one_left (abs_nonneg _) h₁

/-- The set of pairs whose spatial chord lies below the denominator cutoff. -/
def gaussNearPairs (δ : ℝ) : Set (VorticityElement × VorticityElement) :=
  {p | euclideanLength (p.1.1 - p.2.1) < δ}

/-- The spatial near-pair set is measurable. -/
theorem measurableSet_gaussNearPairs (δ : ℝ) : MeasurableSet (gaussNearPairs δ) := by
  exact measurableSet_lt (continuous_euclideanLength.measurable.comp (by fun_prop)) measurable_const

/-- The softened kernel error is bounded by the full absolute
interaction restricted to spatial near pairs. -/
theorem abs_gaussSoftKernel_error {δ : ℝ} (hδ : 0 < δ)
    (p : VorticityElement × VorticityElement) :
    |gaussSoftKernel 0 p.1 p.2 - gaussSoftKernel δ p.1 p.2| ≤
      (gaussNearPairs δ).indicator (fun s => |gaussSoftKernel 0 s.1 s.2|) p := by
  let d := euclideanLength (p.1.1 - p.2.1)
  by_cases h : d < δ
  · rw [indicator_of_mem (show p ∈ gaussNearPairs δ from h)]
    have hd : 0 ≤ d := norm_nonneg _
    have hm : 0 < max δ d := hδ.trans_le (le_max_left _ _)
    have h₀ : 0 ≤ (d / max δ d) ^ 3 := pow_nonneg (div_nonneg hd hm.le) _
    have h₁ : (d / max δ d) ^ 3 ≤ 1 :=
      pow_le_one₀ (div_nonneg hd hm.le) ((div_le_one hm).2 (le_max_right _ _))
    rw [gaussSoftKernel_eq_scale_full δ hδ]
    change |gaussSoftKernel 0 p.1 p.2 - (d / max δ d) ^ 3 * gaussSoftKernel 0 p.1 p.2| ≤ _
    rw [show gaussSoftKernel 0 p.1 p.2 - (d / max δ d) ^ 3 * gaussSoftKernel 0 p.1 p.2 =
      (1 - (d / max δ d) ^ 3) * gaussSoftKernel 0 p.1 p.2 by ring,
      abs_mul, abs_of_nonneg (sub_nonneg.mpr h₁)]
    exact mul_le_of_le_one_left (abs_nonneg _) (sub_le_self _ h₀)
  · rw [indicator_of_notMem (show p ∉ gaussNearPairs δ from h)]
    have he := gaussSoftKernel_eq_bsPairKernel p.1 p.2 (le_of_not_gt h)
    have h₀ := gaussSoftKernel_eq_bsPairKernel p.1 p.2 (show 0 ≤ d from norm_nonneg _)
    rw [he, h₀, sub_self, abs_zero]

/-- The difference of the full and softened product integrals is at most
the absolute full interaction of the near pairs. -/
theorem abs_integral_gaussSoftKernel_error {δ : ℝ} (hδ : 0 < δ)
    {ρ : Measure (VorticityElement × VorticityElement)}
    (hρ : Integrable (fun p => gaussSoftKernel 0 p.1 p.2) ρ) :
    |(∫ p, gaussSoftKernel 0 p.1 p.2 ∂ρ) - (∫ p, gaussSoftKernel δ p.1 p.2 ∂ρ)| ≤
      ∫ p in gaussNearPairs δ, |gaussSoftKernel 0 p.1 p.2| ∂ρ := by
  have hK := hρ.abs.mono' (measurable_gaussSoftKernel δ).aestronglyMeasurable
    (Eventually.of_forall fun p => by
      simpa only [Real.norm_eq_abs] using abs_gaussSoftKernel_le_full hδ p.1 p.2)
  have hI := hρ.abs.indicator (measurableSet_gaussNearPairs δ)
  rw [← integral_sub hρ hK, ← integral_indicator (measurableSet_gaussNearPairs δ)]
  exact abs_integral_le_integral_abs.trans <|
    integral_mono (hρ.sub hK).abs hI (abs_gaussSoftKernel_error hδ)

/-- An absolutely integrable oriented interaction is recovered as the
positive soft cutoff goes to zero. -/
theorem tendsto_integral_gaussSoftKernel {ρ : Measure (VorticityElement × VorticityElement)}
    (hρ : Integrable (fun p => gaussSoftKernel 0 p.1 p.2) ρ) :
    Tendsto (fun δ => ∫ p, gaussSoftKernel δ p.1 p.2 ∂ρ) (𝓝[>] (0 : ℝ))
      (𝓝 (∫ p, gaussSoftKernel 0 p.1 p.2 ∂ρ)) := by
  refine tendsto_integral_filter_of_dominated_convergence
    (fun p => |gaussSoftKernel 0 p.1 p.2|) ?_ ?_ hρ.abs ?_
  · exact Eventually.of_forall fun δ => (measurable_gaussSoftKernel δ).aestronglyMeasurable
  · filter_upwards [show ∀ᶠ δ : ℝ in 𝓝[>] 0, 0 < δ from self_mem_nhdsWithin] with δ hδ
    exact Eventually.of_forall fun p => by
      simpa only [Real.norm_eq_abs] using abs_gaussSoftKernel_le_full hδ p.1 p.2
  · refine Eventually.of_forall fun p => ?_
    let d := euclideanLength (p.1.1 - p.2.1)
    have hd : 0 ≤ d := norm_nonneg _
    by_cases h : 0 < d
    · apply Filter.Tendsto.congr' _ tendsto_const_nhds
      have hL : ∀ᶠ δ : ℝ in 𝓝 0, δ < d := isOpen_Iio.mem_nhds h
      filter_upwards [hL.filter_mono nhdsWithin_le_nhds] with δ hδ
      exact (gaussSoftKernel_eq_bsPairKernel p.1 p.2 hd).trans
        (gaussSoftKernel_eq_bsPairKernel p.1 p.2 hδ.le).symm
    · have hzero : d = 0 := hd.antisymm' (le_of_not_gt h)
      have hz : p.1.1 - p.2.1 = 0 := norm_eq_zero.mp
        (le_antisymm ((norm_le_euclideanLength _).trans_eq hzero) (norm_nonneg _))
      simp only [gaussSoftKernel, hz]
      simp [dot3, cross3]

end Qatlib.Papers.SuperfluidHel18.CenterlineCL
