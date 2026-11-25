/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Papers.KnottedLight08.NullLinking.MagneticAxisLimit

import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# The Gauss kernel at the magnetic axis limit

The rescaled finite-circle Gauss kernel is continuous through the
zero-label limit at every pair of parameters. The limiting kernel
is the positively signed Gauss density of the oriented axis and
the true initial magnetic pole.
-/

@[expose] public section
set_option autoImplicit false

namespace Qatlib.Papers.KnottedLight08.NullLinking

open Qatlib.Papers.KnottedLight08.HopfField (dot3 cross3)
open Qatlib.Papers.SuperfluidHel18.VanishCharge (cross3_apply_zero
  cross3_apply_one cross3_apply_two)
open Qatlib.Papers.SuperfluidHel18.CenterlineCL (euclideanLength gaussKernel
  continuous_euclideanLength)
open Filter
open scoped Topology

/-- The oriented derivative of the true pole curve in Cartesian coordinates. -/
theorem hasDerivAt_magneticPoleCircleAt_zero_coords (t : ℝ) :
    HasDerivAt (cartesianCoordinates ∘ magneticPoleCircleAt 0)
      ![0, -Real.sin t, -Real.cos t] t := by
  have h : cartesianCoordinates ∘ magneticPoleCircleAt 0 =
      (fun q => ![0, Real.cos q, -Real.sin q]) := funext magneticPoleCircleAt_zero_coords
  rw [h, hasDerivAt_pi]
  intro j
  fin_cases j
  · exact hasDerivAt_const t (0 : ℝ)
  · exact Real.hasDerivAt_cos t
  · exact (Real.hasDerivAt_sin t).neg

/-- The finite-circle Gauss kernel after rescaling the first parameter.
The explicit tangent and position formulas extend it to zero label. -/
noncomputable def rescaledMagneticGaussKernel (u s t : ℝ) : ℝ :=
  let d := rescaledMagneticCircle u s - ![0, Real.cos t, -Real.sin t]
  dot3 (cross3 (rescaledMagneticTangent u s) ![0, -Real.sin t, -Real.cos t]) d /
    (4 * Real.pi * euclideanLength d ^ 3)

/-- At a nonzero label the extended kernel equals the actual Gauss
kernel of the rescaled circle and the pole. -/
theorem rescaledMagneticGaussKernel_eq (u s t : ℝ) (hu : u ≠ 0) :
    rescaledMagneticGaussKernel u s t =
      gaussKernel (rescaledMagneticCircle u) (cartesianCoordinates ∘ magneticPoleCircleAt 0) s t := by
  simp only [rescaledMagneticGaussKernel, gaussKernel, Function.comp_apply,
    (hasDerivAt_rescaledMagneticCircle u s hu).deriv,
    (hasDerivAt_magneticPoleCircleAt_zero_coords t).deriv, magneticPoleCircleAt_zero_coords]

/-- The limit chord from the oriented axis to the pole has squared
Euclidean length equal to one plus the squared axis parameter. -/
theorem euclideanLength_magnetic_axis_chord (s t : ℝ) :
    euclideanLength (( ![-s, 0, 0] : Fin 3 → ℝ) - ![0, Real.cos t, -Real.sin t]) =
      Real.sqrt (s ^ 2 + 1) := by
  rw [euclideanLength, PiLp.norm_eq_of_L2, Fin.sum_univ_three]
  congr 1
  change |(-s) - 0| ^ 2 + |(0 : ℝ) - Real.cos t| ^ 2 + |(0 : ℝ) - (-Real.sin t)| ^ 2 = _
  rw [sq_abs, sq_abs, sq_abs, sub_zero, zero_sub, zero_sub,
    neg_neg, neg_sq, neg_sq, add_assoc, add_comm (Real.cos t ^ 2),
    Real.sin_sq_add_cos_sq]

/-- The oriented limiting kernel is independent of the pole angle,
and its triple-product numerator equals one. -/
theorem rescaledMagneticGaussKernel_zero (s t : ℝ) :
    rescaledMagneticGaussKernel 0 s t = 1 / (4 * Real.pi * Real.sqrt (s ^ 2 + 1) ^ 3) := by
  rw [rescaledMagneticGaussKernel, rescaledMagneticCircle_zero, rescaledMagneticTangent_zero,
    euclideanLength_magnetic_axis_chord]
  congr 1
  simp only [dot3, cross3_apply_zero, cross3_apply_one, cross3_apply_two, Pi.sub_apply]
  change (0 * -Real.cos t - 0 * -Real.sin t) * (-s - 0) +
    (0 * 0 - (-1) * -Real.cos t) * (0 - Real.cos t) +
    ((-1) * -Real.sin t - 0 * 0) * (0 - -Real.sin t) = 1
  nlinarith only [Real.sin_sq_add_cos_sq t]

/-- The extended kernel converges pointwise to the oriented axis–pole
kernel as the positive real chart label tends to zero. -/
theorem tendsto_rescaledMagneticGaussKernel (s t : ℝ) :
    Tendsto (fun u => rescaledMagneticGaussKernel u s t) (𝓝[>] (0 : ℝ))
      (𝓝 (1 / (4 * Real.pi * Real.sqrt (s ^ 2 + 1) ^ 3))) := by
  have hP : Continuous (fun u => rescaledMagneticCircle u s) :=
    continuous_rescaledMagneticCircle.comp (continuous_id.prodMk continuous_const)
  have hT : Continuous (fun u => rescaledMagneticTangent u s) :=
    continuous_rescaledMagneticTangent.comp (continuous_id.prodMk continuous_const)
  have hn : ∀ j : Fin 3, Continuous (fun u => rescaledMagneticTangent u s j) :=
    fun j => (continuous_pi_iff.mp hT) j
  have hd : ∀ j : Fin 3, Continuous
      (fun u => (rescaledMagneticCircle u s - ![0, Real.cos t, -Real.sin t]) j) :=
    fun j => continuous_pi_iff.mp (hP.sub continuous_const) j
  have hl : Continuous
      (fun u => euclideanLength (rescaledMagneticCircle u s - ![0, Real.cos t, -Real.sin t])) :=
    continuous_euclideanLength.comp (hP.sub continuous_const)
  have hden : 4 * Real.pi *
      euclideanLength (rescaledMagneticCircle 0 s - ![0, Real.cos t, -Real.sin t]) ^ 3 ≠ 0 := by
    rw [rescaledMagneticCircle_zero, euclideanLength_magnetic_axis_chord]
    positivity
  have hcont : ContinuousAt (fun u => rescaledMagneticGaussKernel u s t) 0 := by
    simp only [rescaledMagneticGaussKernel, dot3, cross3_apply_zero, cross3_apply_one,
      cross3_apply_two]
    fun_prop
  rw [← rescaledMagneticGaussKernel_zero]
  exact hcont.continuousWithinAt

end Qatlib.Papers.KnottedLight08.NullLinking
