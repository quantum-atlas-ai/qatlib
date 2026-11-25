/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Papers.KnottedLight08.NullLinking.MagneticLinking

import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-!
# Deformation of the positive real magnetic labels

[IrvineBouwmeester2008KnottedLight], Eq. (2) and Fig. 1,
[DOI](https://doi.org/10.1038/nphys1056).
Within the positive real chart labels, the initial finite magnetic
circle changes smoothly without touching the pole. This deformation
keeps the Gauss integral fixed as the circle's radius grows.
-/

@[expose] public section
set_option autoImplicit false

namespace Qatlib.Papers.KnottedLight08.NullLinking

open Qatlib.Papers.KnotLight13.TorusFamily (batemanRay_zero)
open Qatlib.Papers.SuperfluidHel18.CenterlineCL (gaussLinking gaussLinking_eq_on_interval)

/-- Cartesian parametrization of the finite circle on the positive real
axis of the magnetic chart at physical time zero. -/
noncomputable def realLabelMagneticCircle (u θ : ℝ) : Fin 3 → ℝ :=
  ![-Real.sin θ / u, (Real.sqrt (u ^ 2 + 1) * Real.cos θ - 1) / u, -Real.sin θ]

/-- The simplified real-label formula agrees with the actual initial
magnetic circle, including its direction of traversal. -/
theorem realLabelMagneticCircle_eq (u θ : ℝ) (hu : 0 < u) :
    realLabelMagneticCircle u θ = cartesianCoordinates (magneticCircleAt u 0 0 θ) := by
  rw [magneticCircleAt, neg_zero, batemanRay_zero]
  have hs : Real.sqrt (u ^ 2 + (0 : ℝ) ^ 2) = u := by
    simpa using Real.sqrt_sq hu.le
  have hd : u ^ 2 + (0 : ℝ) ^ 2 = u ^ 2 := by ring
  funext j
  fin_cases j
  · change -Real.sin θ / u = 0 + -(Real.sqrt (u ^ 2 + (0 : ℝ) ^ 2) * Real.sin θ) /
      (u ^ 2 + (0 : ℝ) ^ 2)
    rw [hs, hd]
    field_simp
    ring
  · change (Real.sqrt (u ^ 2 + 1) * Real.cos θ - 1) / u =
      -u / (u ^ 2 + (0 : ℝ) ^ 2) +
        (u * (Real.sqrt (u ^ 2 + (0 : ℝ) ^ 2 + 1) * Real.cos θ) +
          0 * (Real.sqrt (u ^ 2 + (0 : ℝ) ^ 2) * Real.sin θ)) / (u ^ 2 + (0 : ℝ) ^ 2)
    rw [hd, zero_mul, add_zero]
    field_simp
    ring
  · change -Real.sin θ = -(0 : ℝ) / (u ^ 2 + (0 : ℝ) ^ 2) +
      (0 * (Real.sqrt (u ^ 2 + (0 : ℝ) ^ 2 + 1) * Real.cos θ) -
        u * (Real.sqrt (u ^ 2 + (0 : ℝ) ^ 2) * Real.sin θ)) / (u ^ 2 + (0 : ℝ) ^ 2)
    rw [hs, hd]
    field_simp
    ring

/-- The real-label circle varies smoothly at every positive real label. -/
private theorem contDiffOn_real_label_magnetic_circle :
    ContDiffOn ℝ 2 (fun p : ℝ × ℝ => realLabelMagneticCircle p.1 p.2)
      (Set.Ioi (0 : ℝ) ×ˢ Set.univ) := by
  apply contDiffOn_pi.mpr
  intro j p hp
  have hu : 0 < p.1 := hp.1
  have hfst : ContDiffAt ℝ 2 (fun x : ℝ × ℝ => x.1) p := by fun_prop
  have hsin : ContDiffAt ℝ 2 (fun x : ℝ × ℝ => Real.sin x.2) p := by fun_prop
  have hcos : ContDiffAt ℝ 2 (fun x : ℝ × ℝ => Real.cos x.2) p := by fun_prop
  have hrad : ContDiffAt ℝ 2 (fun x : ℝ × ℝ => Real.sqrt (x.1 ^ 2 + 1)) p :=
    ((hfst.pow 2).add contDiffAt_const).sqrt (by positivity)
  apply ContDiffAt.contDiffWithinAt
  fin_cases j
  · exact hsin.neg.div hfst hu.ne'
  · exact ((hrad.mul hcos).sub contDiffAt_const).div hfst hu.ne'
  · exact hsin.neg

/-- The Gauss integral with the oriented pole is constant over the
positive real magnetic labels on the initial slice. -/
theorem gaussLinking_real_label_pole_eq {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    gaussLinking (realLabelMagneticCircle a) (cartesianCoordinates ∘ magneticPoleCircleAt 0) =
      gaussLinking (realLabelMagneticCircle b) (cartesianCoordinates ∘ magneticPoleCircleAt 0) := by
  wlog hab : a ≤ b generalizing a b
  · exact (this hb ha (le_of_not_ge hab)).symm
  have hC : ContDiff ℝ 2 cartesianCoordinates :=
    cartesianCoordinates.toContinuousLinearEquiv.contDiff
  have hPole : ContDiff ℝ 2 (fun p : ℝ × ℝ =>
      cartesianCoordinates (magneticPoleCircleAt 0 p.2)) := by
    exact hC.comp ((contDiff_magnetic_pole_circle_at_joint.of_le le_top).comp
      (contDiff_const.prodMk contDiff_snd))
  apply gaussLinking_eq_on_interval
    (fun p => realLabelMagneticCircle p.1 p.2)
    (fun p => cartesianCoordinates (magneticPoleCircleAt 0 p.2)) hab
  · exact contDiffOn_real_label_magnetic_circle.mono
      (Set.prod_mono (fun _ hx => ha.trans_le hx.1) (subset_refl _))
  · exact hPole.contDiffOn
  · intro u hu s t h
    have hu' := ha.trans_le hu.1
    rw [realLabelMagneticCircle_eq u s hu'] at h
    exact (Set.disjoint_left.mp (magnetic_circle_disjoint_pole u 0 0 (by positivity)))
      (Set.mem_range_self s) (cartesianCoordinates.injective h ▸ Set.mem_range_self t)
  · intro u _ s
    simp only [realLabelMagneticCircle, Real.sin_add_two_pi, Real.cos_add_two_pi]
  · exact fun _ _ s => congrArg cartesianCoordinates (magnetic_pole_circle_at_periodic 0 s)

end Qatlib.Papers.KnottedLight08.NullLinking
