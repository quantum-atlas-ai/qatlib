/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Papers.SuperfluidHel18.CenterlineCL.BiotSavart
public import Mathlib.MeasureTheory.Measure.FiniteMeasureProd

import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Weak continuity of a regularized Gauss pairing

The position and bounded direction of a vorticity element are retained
together. Replacing the chord length by its maximum with a positive
cutoff makes the Gauss interaction a bounded continuous function of
two oriented elements. Thus weak convergence of their probability
measures implies convergence of the regularized pairing.
-/

@[expose] public section
set_option autoImplicit false

namespace Qatlib.Papers.SuperfluidHel18.CenterlineCL

open Filter MeasureTheory
open Qatlib.Papers.KnottedLight08.HopfField (dot3 cross3)
open Qatlib.Papers.SuperfluidHel18.VanishCharge
  (cross3_apply_zero cross3_apply_one cross3_apply_two)
open scoped BoundedContinuousFunction Real Topology

local notation "VorticitySpace" => Fin 3 → ℝ

/-- A position together with a direction in the coordinate unit ball.
The magnitude of vorticity is represented by the measure on these elements. -/
abbrev VorticityElement := VorticitySpace × {v : VorticitySpace // ‖v‖ ≤ 1}

instance : Nonempty VorticityElement :=
  ⟨(0, ⟨0, by simp⟩)⟩

/-- The Gauss pairing of two oriented elements with a positive floor
on the chord length in the denominator. -/
noncomputable def gaussSoftKernel (δ : ℝ) (p q : VorticityElement) : ℝ :=
  dot3 p.2.val (cross3 q.2.val (p.1 - q.1)) / (4 * π * max δ (euclideanLength (p.1 - q.1)) ^ 3)

/-- For pairs separated by at least the cutoff, the softened interaction
agrees with the full Biot–Savart kernel evaluated on their directions. -/
theorem gaussSoftKernel_eq_bsPairKernel {δ : ℝ} (p q : VorticityElement)
    (h : δ ≤ euclideanLength (p.1 - q.1)) :
    gaussSoftKernel δ p q = bsPairKernel (fun _ => p.2.val) (fun _ => q.2.val) p.1 q.1 := by
  rw [gaussSoftKernel, bsPairKernel, max_eq_right h]

/-- The softened kernel is uniformly bounded even when the positions coincide. -/
theorem abs_gaussSoftKernel_le {δ : ℝ} (hδ : 0 < δ) (p q : VorticityElement) :
    |gaussSoftKernel δ p q| ≤ 3 / (2 * π * δ ^ 2) := by
  let d := max δ (euclideanLength (p.1 - q.1))
  have hdδ : δ ≤ d := le_max_left _ _
  have hd : 0 < d := hδ.trans_le hdδ
  have hx : ‖p.1 - q.1‖ ≤ d := (norm_le_euclideanLength _).trans (le_max_right _ _)
  have hc : ‖cross3 q.2.val (p.1 - q.1)‖ ≤ 2 * d := by
    calc
      _ ≤ 2 * ‖q.2.val‖ * ‖p.1 - q.1‖ := norm_cross3_le_mul _ _
      _ ≤ 2 * 1 * d := by
        gcongr
        exact q.2.property
      _ = _ := by rw [mul_one]
  have hnum : |dot3 p.2.val (cross3 q.2.val (p.1 - q.1))| ≤ 6 * d := by
    calc
      _ ≤ 3 * ‖p.2.val‖ * ‖cross3 q.2.val (p.1 - q.1)‖ := abs_dot3_le _ _
      _ ≤ 3 * 1 * (2 * d) := by
        gcongr
        exact p.2.property
      _ = _ := by ring
  have hden : 0 < 4 * π * d ^ 3 := by positivity
  rw [gaussSoftKernel, abs_div]
  change |dot3 p.2.val (cross3 q.2.val (p.1 - q.1))| / |4 * π * d ^ 3| ≤ _
  rw [abs_of_pos hden]
  calc
    _ ≤ 6 * d / (4 * π * d ^ 3) := div_le_div_of_nonneg_right hnum hden.le
    _ = 3 * (1 / (2 * π * d ^ 2)) := by
      field_simp [Real.pi_ne_zero, hd.ne']
      norm_num
    _ ≤ 3 * (1 / (2 * π * δ ^ 2)) := by
      apply mul_le_mul_of_nonneg_left _ (by norm_num)
      apply one_div_le_one_div_of_le (by positivity)
      gcongr
    _ = _ := by ring

/-- The positive denominator floor makes the oriented kernel continuous
across the diagonal as well as away from it. -/
theorem continuous_gaussSoftKernel {δ : ℝ} (hδ : 0 < δ) :
    Continuous (fun p : VorticityElement × VorticityElement => gaussSoftKernel δ p.1 p.2) := by
  have hne (p : VorticityElement × VorticityElement) :
      4 * π * max δ (euclideanLength (p.1.1 - p.2.1)) ^ 3 ≠ 0 := by
    have hmax : 0 < max δ (euclideanLength (p.1.1 - p.2.1)) := hδ.trans_le (le_max_left _ _)
    exact ne_of_gt (by positivity)
  let u := fun p : VorticityElement × VorticityElement => p.1.2.val
  let v := fun p : VorticityElement × VorticityElement => p.2.2.val
  let w := fun p : VorticityElement × VorticityElement => p.1.1 - p.2.1
  have hu : Continuous u := continuous_subtype_val.comp (continuous_snd.comp continuous_fst)
  have hv : Continuous v := continuous_subtype_val.comp (continuous_snd.comp continuous_snd)
  have hw : Continuous w := (continuous_fst.comp continuous_fst).sub (continuous_fst.comp continuous_snd)
  have hp : Continuous fun p => dot3 (u p) (cross3 (v p) (w p)) := by
    simp only [dot3, cross3_apply_zero, cross3_apply_one, cross3_apply_two]
    fun_prop
  exact hp.div₀ (by fun_prop) hne

/-- The softened kernel as a test function for weak convergence of the
probability measure on a pair of oriented elements. -/
noncomputable def gaussSoftTest {δ : ℝ} (hδ : 0 < δ) :
    (VorticityElement × VorticityElement) →ᵇ ℝ :=
  BoundedContinuousFunction.ofNormedAddCommGroup (fun p => gaussSoftKernel δ p.1 p.2)
    (continuous_gaussSoftKernel hδ) (3 / (2 * π * δ ^ 2)) (fun p => by
      simpa only [Real.norm_eq_abs] using abs_gaussSoftKernel_le hδ p.1 p.2)

/-- Weak convergence of each oriented probability measure gives convergence
of their actual regularized Gauss interaction. -/
theorem tendsto_gaussSoftPairing {ι : Type*} {l : Filter ι}
    {δ : ℝ} (hδ : 0 < δ) {μ ν : ProbabilityMeasure VorticityElement}
    {F G : ι → ProbabilityMeasure VorticityElement}
    (hF : Tendsto F l (𝓝 μ)) (hG : Tendsto G l (𝓝 ν)) :
    Tendsto (fun i => ∫ p, gaussSoftKernel δ p.1 p.2 ∂((F i).prod (G i)).toMeasure) l
      (𝓝 (∫ p, gaussSoftKernel δ p.1 p.2 ∂(μ.prod ν).toMeasure)) := by
  have hp : Tendsto (fun i => (F i).prod (G i)) l (𝓝 (μ.prod ν)) :=
    ProbabilityMeasure.continuous_prod.continuousAt.tendsto.comp (hF.prodMk_nhds hG)
  exact (ProbabilityMeasure.continuous_integral_boundedContinuousFunction
    (gaussSoftTest hδ)).continuousAt.tendsto.comp hp

end Qatlib.Papers.SuperfluidHel18.CenterlineCL
