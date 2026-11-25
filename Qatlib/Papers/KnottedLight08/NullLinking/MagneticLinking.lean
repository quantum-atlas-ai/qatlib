/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Papers.KnottedLight08.NullLinking.MagneticLineTransport
public import Qatlib.Papers.SuperfluidHel18.CenterlineCL.GaussHomotopy

import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv

/-!
# Conservation of the Gauss integral of closed magnetic field lines

[IrvineBouwmeester2008KnottedLight], Eq. (2) and Fig. 1,
[DOI](https://doi.org/10.1038/nphys1056).
Distinct finite nonzero magnetic fibers and the projective pole form
smooth families of disjoint oriented closed curves. Their Gauss linking
integrals are constant across the real time slices.
-/

@[expose] public section
set_option autoImplicit false

namespace Qatlib.Papers.KnottedLight08.NullLinking

open Qatlib.Papers.KnotLight13.TorusFamily

open Qatlib.Papers.SuperfluidHel18.CenterlineCL (gaussLinking gaussLinking_eq_of_smooth_homotopy)

/-- Each Cartesian component of the initial finite circle is smooth
in its traversal angle. -/
private theorem contDiff_initial_magnetic_circle_coord (u v : ℝ) (j : Fin 3) :
    ContDiff ℝ ⊤ (fun θ => initialMagneticCircle u v θ j) := by
  let d := u ^ 2 + v ^ 2
  let ρ := Real.sqrt d
  let σ := Real.sqrt (d + 1)
  fin_cases j
  · change ContDiff ℝ ⊤ (fun θ => 0 + -(ρ * Real.sin θ) / d)
    fun_prop
  · change ContDiff ℝ ⊤ (fun θ => -u / d + (u * (σ * Real.cos θ) + v * (ρ * Real.sin θ)) / d)
    fun_prop
  · change ContDiff ℝ ⊤ (fun θ => -v / d + (v * (σ * Real.cos θ) - u * (ρ * Real.sin θ)) / d)
    fun_prop

/-- Joint smoothness in physical time and angle for a finite magnetic
circle. -/
theorem contDiff_magnetic_circle_at_joint (u v : ℝ) :
    ContDiff ℝ ⊤ (fun a : ℝ × ℝ => magneticCircleAt u v a.1 a.2) := by
  have h (j : Fin 3) : ContDiff ℝ ⊤ (fun a : ℝ × ℝ => initialMagneticCircle u v a.2 j) :=
    (contDiff_initial_magnetic_circle_coord u v j).comp contDiff_snd
  exact contDiff_bateman_ray_joint.comp
    (contDiff_fst.neg.prodMk ((h 0).prodMk ((h 1).prodMk (h 2))))

/-- Joint smoothness in physical time and angle for the pole circle. -/
theorem contDiff_magnetic_pole_circle_at_joint :
    ContDiff ℝ ⊤ (fun a : ℝ × ℝ => magneticPoleCircleAt a.1 a.2) := by
  exact contDiff_bateman_ray_joint.comp (contDiff_fst.neg.prodMk
    (contDiff_const.prodMk ((Real.contDiff_cos.comp contDiff_snd).prodMk
      (Real.contDiff_sin.comp contDiff_snd).neg)))

/-- Two circles with distinct finite nonzero magnetic labels share no
point on any real time slice. -/
theorem magnetic_circles_disjoint (u v p q t : ℝ)
    (huv : 0 < u ^ 2 + v ^ 2) (hpq : 0 < p ^ 2 + q ^ 2)
    (hne : ((u : ℂ) + Complex.I * (v : ℂ)) ≠ ((p : ℂ) + Complex.I * (q : ℂ))) :
    Disjoint (Set.range (magneticCircleAt u v t)) (Set.range (magneticCircleAt p q t)) := by
  rw [range_magnetic_circle_at u v t huv, range_magnetic_circle_at p q t hpq]
  exact Set.disjoint_left.mpr fun _ hx hy => hne (hx.2.symm.trans hy.2)

/-- The affine magnetic chart excludes the entire projective pole on
every real time slice. -/
theorem magnetic_circle_disjoint_pole (u v t : ℝ) (huv : 0 < u ^ 2 + v ^ 2) :
    Disjoint (Set.range (magneticCircleAt u v t)) (Set.range (magneticPoleCircleAt t)) := by
  rw [range_magnetic_circle_at u v t huv, range_magnetic_pole_circle_at]
  exact Set.disjoint_left.mpr fun _ hx hy => hx.1 hy

/-- The actual Gauss linking integral of two distinct oriented finite
magnetic circles is the same at any two real times. -/
theorem gaussLinking_magnetic_circles_eq (u v p q a b : ℝ)
    (huv : 0 < u ^ 2 + v ^ 2) (hpq : 0 < p ^ 2 + q ^ 2)
    (hne : ((u : ℂ) + Complex.I * (v : ℂ)) ≠ ((p : ℂ) + Complex.I * (q : ℂ))) :
    gaussLinking (cartesianCoordinates ∘ magneticCircleAt u v a)
        (cartesianCoordinates ∘ magneticCircleAt p q a) =
      gaussLinking (cartesianCoordinates ∘ magneticCircleAt u v b)
        (cartesianCoordinates ∘ magneticCircleAt p q b) := by
  have hC : ContDiff ℝ 2 cartesianCoordinates :=
    cartesianCoordinates.toContinuousLinearEquiv.contDiff
  exact gaussLinking_eq_of_smooth_homotopy
    (fun x => cartesianCoordinates (magneticCircleAt u v x.1 x.2))
    (fun x => cartesianCoordinates (magneticCircleAt p q x.1 x.2))
    (hC.comp ((contDiff_magnetic_circle_at_joint u v).of_le le_top))
    (hC.comp ((contDiff_magnetic_circle_at_joint p q).of_le le_top))
    (fun t s r h => (Set.disjoint_left.mp (magnetic_circles_disjoint u v p q t huv hpq hne))
      (Set.mem_range_self s) (cartesianCoordinates.injective h ▸ Set.mem_range_self r))
    (fun t s => congrArg cartesianCoordinates (magnetic_circle_at_periodic u v t s))
    (fun t s => congrArg cartesianCoordinates (magnetic_circle_at_periodic p q t s)) a b

/-- The actual Gauss linking integral of an oriented finite magnetic
circle with the oriented pole is conserved at every real time. -/
theorem gaussLinking_magnetic_circle_pole_eq (u v a b : ℝ) (huv : 0 < u ^ 2 + v ^ 2) :
    gaussLinking (cartesianCoordinates ∘ magneticCircleAt u v a)
        (cartesianCoordinates ∘ magneticPoleCircleAt a) =
      gaussLinking (cartesianCoordinates ∘ magneticCircleAt u v b)
        (cartesianCoordinates ∘ magneticPoleCircleAt b) := by
  have hC : ContDiff ℝ 2 cartesianCoordinates :=
    cartesianCoordinates.toContinuousLinearEquiv.contDiff
  exact gaussLinking_eq_of_smooth_homotopy
    (fun x => cartesianCoordinates (magneticCircleAt u v x.1 x.2))
    (fun x => cartesianCoordinates (magneticPoleCircleAt x.1 x.2))
    (hC.comp ((contDiff_magnetic_circle_at_joint u v).of_le le_top))
    (hC.comp (contDiff_magnetic_pole_circle_at_joint.of_le le_top))
    (fun t s r h => (Set.disjoint_left.mp (magnetic_circle_disjoint_pole u v t huv))
      (Set.mem_range_self s) (cartesianCoordinates.injective h ▸ Set.mem_range_self r))
    (fun t s => congrArg cartesianCoordinates (magnetic_circle_at_periodic u v t s))
    (fun t s => congrArg cartesianCoordinates (magnetic_pole_circle_at_periodic t s)) a b

end Qatlib.Papers.KnottedLight08.NullLinking
