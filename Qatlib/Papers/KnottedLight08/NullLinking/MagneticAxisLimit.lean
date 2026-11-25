/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Papers.KnottedLight08.NullLinking.RealLabelLinking

public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Sinc

import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring

/-!
# The rescaled magnetic circle at the vanishing real label

When the positive real magnetic label tends to zero, the finite
circle has growing radius. Rescaling its traversal parameter by the
label gives an oriented limit along the negative Cartesian axis.
The position and rescaled tangent have jointly continuous extensions.
-/

@[expose] public section
set_option autoImplicit false

namespace Qatlib.Papers.KnottedLight08.NullLinking

/-- The position of the rescaled finite circle, expressed by continuous
functions of the label and the new parameter even at zero label. -/
noncomputable def rescaledMagneticCircle (u s : ℝ) : Fin 3 → ℝ :=
  ![-s * Real.sinc (u * s),
    u * (Real.cos (u * s) / (Real.sqrt (u ^ 2 + 1) + 1) -
      s ^ 2 / 2 * Real.sinc (u * s / 2) ^ 2),
    -Real.sin (u * s)]

/-- The continuous extension agrees exactly with the original finite
circle at the rescaled angle for every nonzero label. -/
theorem rescaledMagneticCircle_eq (u s : ℝ) (hu : u ≠ 0) :
    rescaledMagneticCircle u s = realLabelMagneticCircle u (u * s) := by
  have hsinc (x : ℝ) : x * Real.sinc x = Real.sin x := by
    by_cases hx : x = 0
    · simp [hx]
    · rw [Real.sinc_of_ne_zero hx]
      field_simp
  let R := Real.sqrt (u ^ 2 + 1)
  have hR : R ^ 2 = u ^ 2 + 1 := Real.sq_sqrt (by positivity)
  have hR' : 0 < R + 1 := by dsimp only [R]; positivity
  have hcos : Real.cos (u * s) - 1 = -2 * Real.sin (u * s / 2) ^ 2 := by
    calc
      _ = Real.cos (2 * (u * s / 2)) - 1 := by ring_nf
      _ = _ := by
        rw [two_mul, Real.cos_add]
        nlinarith only [Real.sin_sq_add_cos_sq (u * s / 2)]
  funext j
  fin_cases j
  · change -s * Real.sinc (u * s) = -Real.sin (u * s) / u
    apply (eq_div_iff hu).2
    linear_combination -hsinc (u * s)
  · change u * (Real.cos (u * s) / (R + 1) -
        s ^ 2 / 2 * Real.sinc (u * s / 2) ^ 2) = (R * Real.cos (u * s) - 1) / u
    have hmul : (R - 1) * (R + 1) = u ^ 2 := by nlinarith only [hR]
    have hRdiv : u ^ 2 / (R + 1) = R - 1 := (div_eq_iff hR'.ne').mpr hmul.symm
    have htrig : (u * s / 2) ^ 2 * Real.sinc (u * s / 2) ^ 2 =
        Real.sin (u * s / 2) ^ 2 := by
      rw [← mul_pow, hsinc]
    apply (eq_div_iff hu).2
    calc
      _ = (u ^ 2 / (R + 1)) * Real.cos (u * s) -
          2 * ((u * s / 2) ^ 2 * Real.sinc (u * s / 2) ^ 2) := by ring
      _ = _ := by rw [hRdiv, htrig]; linarith only [hcos]
  · rfl

/-- The rescaled positions extend continuously to zero label, jointly
in the label and the parameter. -/
theorem continuous_rescaledMagneticCircle :
    Continuous (fun p : ℝ × ℝ => rescaledMagneticCircle p.1 p.2) := by
  apply continuous_pi
  intro j
  fin_cases j
  · change Continuous (fun p : ℝ × ℝ => -p.2 * Real.sinc (p.1 * p.2))
    fun_prop
  · change Continuous (fun p : ℝ × ℝ =>
      p.1 * (Real.cos (p.1 * p.2) / (Real.sqrt (p.1 ^ 2 + 1) + 1) -
        p.2 ^ 2 / 2 * Real.sinc (p.1 * p.2 / 2) ^ 2))
    exact continuous_fst.mul
      ((by fun_prop : Continuous fun p : ℝ × ℝ => Real.cos (p.1 * p.2)).div
        (by fun_prop : Continuous fun p : ℝ × ℝ => Real.sqrt (p.1 ^ 2 + 1) + 1)
        (fun _ => by positivity) |>.sub (by fun_prop))
  · change Continuous (fun p : ℝ × ℝ => -Real.sin (p.1 * p.2))
    fun_prop

/-- At zero label the extension is exactly the axis traversed in the
negative first-coordinate direction. -/
theorem rescaledMagneticCircle_zero (s : ℝ) :
    rescaledMagneticCircle 0 s = ![-s, 0, 0] := by
  simp [rescaledMagneticCircle]

/-- The tangent of the rescaled finite circle, continuously extended in
the label. -/
noncomputable def rescaledMagneticTangent (u s : ℝ) : Fin 3 → ℝ :=
  ![-Real.cos (u * s), -Real.sqrt (u ^ 2 + 1) * Real.sin (u * s), -u * Real.cos (u * s)]

/-- The extended tangent at zero is the constant oriented axis tangent. -/
theorem rescaledMagneticTangent_zero (s : ℝ) :
    rescaledMagneticTangent 0 s = ![-1, 0, 0] := by
  simp [rescaledMagneticTangent]

/-- The rescaled tangent is jointly continuous in the label and angle
parameter at and away from the axis limit. -/
theorem continuous_rescaledMagneticTangent :
    Continuous (fun p : ℝ × ℝ => rescaledMagneticTangent p.1 p.2) := by
  apply continuous_pi
  intro j
  fin_cases j
  · change Continuous fun p : ℝ × ℝ => -Real.cos (p.1 * p.2)
    fun_prop
  · change Continuous fun p : ℝ × ℝ => -Real.sqrt (p.1 ^ 2 + 1) * Real.sin (p.1 * p.2)
    fun_prop
  · change Continuous fun p : ℝ × ℝ => -p.1 * Real.cos (p.1 * p.2)
    fun_prop

/-- The continuous extension supplies the actual parameter derivative
of the rescaled finite circle. -/
theorem hasDerivAt_rescaledMagneticCircle (u s : ℝ) (hu : u ≠ 0) :
    HasDerivAt (rescaledMagneticCircle u) (rescaledMagneticTangent u s) s := by
  have he : rescaledMagneticCircle u = fun x => realLabelMagneticCircle u (u * x) :=
    funext fun x => rescaledMagneticCircle_eq u x hu
  rw [he, hasDerivAt_pi]
  intro i
  have hs := (Real.hasDerivAt_sin (u * s)).comp s ((hasDerivAt_id s).const_mul u)
  have hc := (Real.hasDerivAt_cos (u * s)).comp s ((hasDerivAt_id s).const_mul u)
  fin_cases i
  · change HasDerivAt (fun x => -Real.sin (u * x) / u) (-Real.cos (u * s)) s
    convert hs.neg.div_const u using 1
    · funext x
      simp only [Function.comp_apply, Pi.neg_apply, neg_div]
    · field_simp
  · change HasDerivAt (fun x => (Real.sqrt (u ^ 2 + 1) * Real.cos (u * x) - 1) / u)
      (-Real.sqrt (u ^ 2 + 1) * Real.sin (u * s)) s
    convert ((hc.const_mul (Real.sqrt (u ^ 2 + 1))).sub_const 1).div_const u using 1
    · rfl
    · field_simp
  · change HasDerivAt (fun x => -Real.sin (u * x)) (-u * Real.cos (u * s)) s
    convert hs.neg using 1
    · rfl
    · ring

open Qatlib.Papers.KnotLight13.TorusFamily (batemanRay_zero)
open Qatlib.Papers.SuperfluidHel18.CenterlineCL (euclideanLength)

/-- The squared distance from the origin separates the minimum distance
of the circle from its angular displacement. -/
theorem rescaledMagneticCircle_length_sq (u s : ℝ) (hu : u ≠ 0) :
    euclideanLength (rescaledMagneticCircle u s) ^ 2 =
      ((Real.sqrt (u ^ 2 + 1) - 1) ^ 2 +
        4 * Real.sqrt (u ^ 2 + 1) * Real.sin (u * s / 2) ^ 2) / u ^ 2 := by
  rw [rescaledMagneticCircle_eq u s hu, euclideanLength, PiLp.norm_eq_of_L2,
    Real.sq_sqrt (Finset.sum_nonneg fun _ _ => sq_nonneg _), Fin.sum_univ_three]
  simp only [Real.norm_eq_abs, sq_abs, realLabelMagneticCircle,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two]
  let R := Real.sqrt (u ^ 2 + 1)
  let θ := u * s
  change (-Real.sin θ / u) ^ 2 + ((R * Real.cos θ - 1) / u) ^ 2 +
    (-Real.sin θ) ^ 2 = ((R - 1) ^ 2 + 4 * R * Real.sin (θ / 2) ^ 2) / u ^ 2
  have hR : R ^ 2 = u ^ 2 + 1 := Real.sq_sqrt (by positivity)
  have hcos : Real.cos θ - 1 = -2 * Real.sin (θ / 2) ^ 2 := by
    have hh := Real.cos_add (θ / 2) (θ / 2)
    rw [show θ / 2 + θ / 2 = θ by ring] at hh
    nlinarith only [hh, Real.sin_sq_add_cos_sq (θ / 2)]
  field_simp
  linear_combination
    (Real.sin θ ^ 2) * (-hR) + R ^ 2 * Real.sin_sq_add_cos_sq θ - 2 * R * hcos

/-- On its expanding symmetric parameter interval the circle moves
away from the origin at least linearly in the rescaled parameter. -/
theorem le_rescaledMagneticCircle_length (u s : ℝ) (hu : 0 < u)
    (hs : |u * s| ≤ Real.pi) :
    2 * |s| / Real.pi ≤ euclideanLength (rescaledMagneticCircle u s) := by
  have hhalf : |u * s / 2| ≤ Real.pi / 2 := by
    rwa [abs_div, abs_of_pos (two_pos : (0 : ℝ) < 2), div_le_div_iff_of_pos_right two_pos]
  have hsin := Real.mul_abs_le_abs_sin hhalf
  rw [abs_div, abs_mul, abs_of_pos hu, abs_of_pos (two_pos : (0 : ℝ) < 2)] at hsin
  have hb : 2 * |s| / Real.pi ≤ 2 * |Real.sin (u * s / 2)| / u := by
    apply (le_div_iff₀ hu).2
    rw [show 2 * |s| / Real.pi * u = 2 * (2 / Real.pi * (u * |s| / 2)) by ring]
    exact mul_le_mul_of_nonneg_left hsin (by norm_num)
  have hR : 1 ≤ Real.sqrt (u ^ 2 + 1) := by
    calc
      1 = Real.sqrt 1 := Real.sqrt_one.symm
      _ ≤ _ := Real.sqrt_le_sqrt (by linarith [sq_nonneg u])
  refine (sq_le_sq₀ (by positivity)
    (norm_nonneg (WithLp.toLp 2 (rescaledMagneticCircle u s)))).1 ?_
  calc
    _ ≤ (2 * |Real.sin (u * s / 2)| / u) ^ 2 :=
      pow_le_pow_left₀ (by positivity) hb 2
    _ = 4 * Real.sin (u * s / 2) ^ 2 / u ^ 2 := by rw [div_pow, mul_pow, sq_abs]; norm_num
    _ ≤ _ := by
      change _ ≤ euclideanLength (rescaledMagneticCircle u s) ^ 2
      rw [rescaledMagneticCircle_length_sq u s hu.ne']
      apply div_le_div_of_nonneg_right _ (by positivity)
      nlinarith only [sq_nonneg (Real.sqrt (u ^ 2 + 1) - 1),
        mul_nonneg (sub_nonneg.mpr hR) (sq_nonneg (Real.sin (u * s / 2)))]

/-- The actual initial pole circle in Cartesian coordinates. -/
theorem magneticPoleCircleAt_zero_coords (t : ℝ) :
    cartesianCoordinates (magneticPoleCircleAt 0 t) = ![0, Real.cos t, -Real.sin t] := by
  rw [magneticPoleCircleAt, neg_zero, batemanRay_zero]
  rfl

/-- Each point on the initial pole circle has unit distance from the
origin. -/
theorem euclideanLength_magneticPoleCircleAt_zero (t : ℝ) :
    euclideanLength (cartesianCoordinates (magneticPoleCircleAt 0 t)) = 1 := by
  rw [magneticPoleCircleAt_zero_coords, euclideanLength, PiLp.norm_eq_of_L2, Fin.sum_univ_three]
  simp only [Real.norm_eq_abs, sq_abs, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, zero_pow (by decide : (2 : ℕ) ≠ 0), zero_add]
  change Real.sqrt (Real.cos t ^ 2 + (-Real.sin t) ^ 2) = 1
  rw [neg_sq]
  rw [add_comm, Real.sin_sq_add_cos_sq, Real.sqrt_one]

/-- Away from the central parameter interval the magnetic chord grows
at least linearly, uniformly as the positive real label tends to zero. -/
theorem le_rescaledMagneticCircle_pole_chord (u s t : ℝ) (hu : 0 < u)
    (hs : |u * s| ≤ Real.pi) (hlarge : Real.pi ≤ |s|) :
    |s| / Real.pi ≤ euclideanLength
      (rescaledMagneticCircle u s - cartesianCoordinates (magneticPoleCircleAt 0 t)) := by
  let x := rescaledMagneticCircle u s
  let y := cartesianCoordinates (magneticPoleCircleAt 0 t)
  have htriangle : euclideanLength x ≤ euclideanLength (x - y) + euclideanLength y := by
    change ‖WithLp.toLp 2 x‖ ≤ ‖WithLp.toLp 2 (x - y)‖ + ‖WithLp.toLp 2 y‖
    rw [WithLp.toLp_sub]
    exact norm_le_norm_sub_add _ _
  have hy : euclideanLength y = 1 := euclideanLength_magneticPoleCircleAt_zero t
  rw [hy] at htriangle
  have hlow := le_rescaledMagneticCircle_length u s hu hs
  change 2 * |s| / Real.pi ≤ euclideanLength x at hlow
  rw [show 2 * |s| / Real.pi = 2 * (|s| / Real.pi) by ring] at hlow
  have hlarge' : 1 ≤ |s| / Real.pi := (le_div_iff₀ Real.pi_pos).2 (by simpa using hlarge)
  change |s| / Real.pi ≤ euclideanLength (x - y)
  linarith only [htriangle, hlow, hlarge']

end Qatlib.Papers.KnottedLight08.NullLinking
