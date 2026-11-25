/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Papers.KnottedLight08.NullLinking.MagneticCircles
public import Qatlib.Papers.KnottedLight08.NullLinking.MagneticFiberTransport

import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-!
# Closed magnetic fibers on every time slice

[IrvineBouwmeester2008KnottedLight], Eq. (2) and Fig. 1,
[DOI](https://doi.org/10.1038/nphys1056).
The reflected ray homeomorphism carries the explicit initial closed
circles to precisely the corresponding level sets of the actual magnetic
scalar on each later or earlier slice. Each such level set is compact and
has a continuous periodic parameterization.
-/

@[expose] public section
set_option autoImplicit false

namespace Qatlib.Papers.KnottedLight08.NullLinking

open Qatlib.Papers.KnotLight13.TorusFamily
open Qatlib.Papers.KnottedLight08.HopfField

/-- The explicit initial circle carried to the time slice by the
reflected physical ray map. -/
noncomputable def magneticCircleAt (u v t θ : ℝ) : ℝ × ℝ × ℝ :=
  let s := initialMagneticCircle u v θ
  batemanRay (-t) (s 0, s 1, s 2)

/-- The initial fiber has the same points in the Euclidean model and
in the Cartesian triple model used by the ray map. -/
private theorem magnetic_fiber_zero_eq_coordinate_image (u v : ℝ) :
    (fun s : EuclideanSpace ℝ (Fin 3) => (s 0, s 1, s 2)) '' initialMagneticFiber u v =
      magneticFiberAt 0 ((u : ℂ) + Complex.I * (v : ℂ)) := by
  ext s
  constructor
  · rintro ⟨q, hq, rfl⟩
    exact hq
  · intro hs
    let q : EuclideanSpace ℝ (Fin 3) := WithLp.toLp 2 ![s.1, s.2.1, s.2.2]
    exact ⟨q, hs, by rcases s with ⟨x, y, z⟩; rfl⟩

/-- The transported circle parameterization is continuous. -/
theorem continuous_magnetic_circle_at (u v t : ℝ) :
    Continuous (magneticCircleAt u v t) := by
  have h (j : Fin 3) : Continuous fun θ => initialMagneticCircle u v θ j :=
    continuous_iff_continuousAt.mpr fun θ =>
      (hasDerivAt_initial_magnetic_circle u v θ j).continuousAt
  exact continuous_batemanRay_joint.comp
    (continuous_const.prodMk ((h 0).prodMk ((h 1).prodMk (h 2))))

/-- The transported parameterization retains the initial (2π) period. -/
theorem magnetic_circle_at_periodic (u v t : ℝ) :
    Function.Periodic (magneticCircleAt u v t) (2 * Real.pi) := by
  intro θ
  unfold magneticCircleAt
  rw [initial_magnetic_circle_periodic u v θ]

/-- The parameterization covers the full literal magnetic fiber at
the given time, with the nonzero finite chart value held fixed. -/
theorem range_magnetic_circle_at (u v t : ℝ) (hd : 0 < u ^ 2 + v ^ 2) :
    Set.range (magneticCircleAt u v t) = magneticFiberAt t ((u : ℂ) + Complex.I * (v : ℂ)) := by
  let coords := fun s : EuclideanSpace ℝ (Fin 3) => (s 0, s 1, s 2)
  calc
    _ = batemanRay (-t) '' (coords '' Set.range (initialMagneticCircle u v)) := by
      rw [Set.image_image, ← Set.range_comp]
      rfl
    _ = _ := by
      rw [range_initial_magnetic_circle u v hd, magnetic_fiber_zero_eq_coordinate_image u v,
        magnetic_fiber_at_eq_reflected_ray_image]

/-- Every finite nonzero magnetic fiber is compact in physical space
at every time. -/
theorem magnetic_fiber_at_isCompact (u v t : ℝ) (hd : 0 < u ^ 2 + v ^ 2) :
    IsCompact (magneticFiberAt t ((u : ℂ) + Complex.I * (v : ℂ))) := by
  have h (j : Fin 3) : Continuous fun s : EuclideanSpace ℝ (Fin 3) => s j :=
    PiLp.continuous_apply 2 _ j
  have h0 := (initialMagneticFiber_isCompact u v hd).image ((h 0).prodMk ((h 1).prodMk (h 2)))
  rw [magnetic_fiber_zero_eq_coordinate_image] at h0
  rw [← magnetic_fiber_at_eq_reflected_ray_image]
  exact h0.image (batemanSliceHomeomorph (-t)).continuous

/-- The initial pole circle rotated in the orientation of the magnetic
field and carried to the chosen time by the reflected ray map. -/
noncomputable def magneticPoleCircleAt (t θ : ℝ) : ℝ × ℝ × ℝ :=
  batemanRay (-t) (0, Real.cos θ, -Real.sin θ)

/-- The initial parameterization covers the entire projective pole
of the magnetic chart. -/
private theorem range_initial_magnetic_pole :
    Set.range (fun θ : ℝ => ((0 : ℝ), Real.cos θ, -Real.sin θ)) =
      {s : ℝ × ℝ × ℝ | etaDen s.1 s.2.1 s.2.2 0 = 0} := by
  ext s
  rcases s with ⟨x, y, z⟩
  change (∃ θ : ℝ, ((0 : ℝ), Real.cos θ, -Real.sin θ) = (x, y, z)) ↔ etaDen x y z 0 = 0
  rw [etaDen, ranadaEta_den_zero_t_zero_iff]
  constructor
  · rintro ⟨θ, he⟩
    obtain ⟨rfl, rfl, rfl⟩ := by simpa only [Prod.mk.injEq] using he.symm
    refine ⟨rfl, ?_⟩
    rw [neg_sq, add_comm]
    exact Real.sin_sq_add_cos_sq θ
  · rintro ⟨rfl, hl⟩
    obtain ⟨θ, hy, hz⟩ := exists_angle_of_unit_coordinates y (-z) (by rw [neg_sq, hl])
    exact ⟨θ, by rw [hy, hz, neg_neg]⟩

/-- The same continuously moving parameterization covers the entire
pole fiber at each time. -/
theorem range_magnetic_pole_circle_at (t : ℝ) :
    Set.range (magneticPoleCircleAt t) =
      {s : ℝ × ℝ × ℝ | etaDen s.1 s.2.1 s.2.2 t = 0} := by
  calc
    _ = batemanRay (-t) '' Set.range (fun θ : ℝ => ((0 : ℝ), Real.cos θ, -Real.sin θ)) := by
      rw [← Set.range_comp]
      rfl
    _ = _ := by rw [range_initial_magnetic_pole, magnetic_pole_fiber_eq_reflected_ray_image]

/-- The pole parameterization depends continuously on the angle. -/
theorem continuous_magnetic_pole_circle_at (t : ℝ) : Continuous (magneticPoleCircleAt t) :=
  continuous_batemanRay_joint.comp
    (continuous_const.prodMk (continuous_const.prodMk
      (Real.continuous_cos.prodMk Real.continuous_sin.neg)))

/-- The pole circle retains the initial period on every slice. -/
theorem magnetic_pole_circle_at_periodic (t : ℝ) :
    Function.Periodic (magneticPoleCircleAt t) (2 * Real.pi) := by
  intro θ
  simp only [magneticPoleCircleAt, Real.cos_add_two_pi, Real.sin_add_two_pi]

/-- Coordinate derivatives of the initial pole circle in its orientation
of traversal. -/
theorem hasDerivAt_initial_magnetic_pole_circle (θ : ℝ) (j : Fin 3) :
    let c (r : ℝ) := magneticPoleCircleAt 0 r
    HasDerivAt (fun r => ![(c r).1, (c r).2.1, (c r).2.2] j)
      (![0, -Real.sin θ, -Real.cos θ] j) θ := by
  fin_cases j <;> simp only [magneticPoleCircleAt, neg_zero, batemanRay_zero]
  · exact hasDerivAt_const θ (0 : ℝ)
  · exact Real.hasDerivAt_cos θ
  · exact (Real.hasDerivAt_sin θ).neg

/-- Along the initial pole circle the actual magnetic field is its
coordinate tangent times the positive constant (1/(2π)). -/
theorem ranada_b_along_initial_magnetic_pole_circle (θ : ℝ) (j : Fin 3) :
    let s := magneticPoleCircleAt 0 θ
    (ranadaB s.1 s.2.1 s.2.2 0 j).re = (1 / (2 * Real.pi)) *
      (![0, -Real.sin θ, -Real.cos θ] j) := by
  have htrig := Real.sin_sq_add_cos_sq θ
  have hS : hopfScale 0 (Real.cos θ) (-Real.sin θ) = 2 := by
    simp [hopfScale]
    linarith only [htrig]
  simp only [magneticPoleCircleAt, neg_zero, batemanRay_zero, ranada_b_initial_re, hS]
  fin_cases j <;> simp [initialMagneticDirection]
  · have hv : 1 - Real.cos θ ^ 2 - Real.sin θ ^ 2 = 0 := by linarith only [htrig]
    rw [hv]
  · field_simp [Real.pi_ne_zero]
  · field_simp [Real.pi_ne_zero]

/-- The finite zero level is the image of the initial Cartesian
axis on every slice. -/
theorem magnetic_zero_fiber_eq_reflected_axis (t : ℝ) :
    magneticFiberAt t 0 = Set.range (fun x : ℝ => batemanRay (-t) (x, 0, 0)) := by
  have h0 : magneticFiberAt 0 0 = Set.range (fun x : ℝ => (x, (0 : ℝ), (0 : ℝ))) := by
    ext s
    rcases s with ⟨x, y, z⟩
    change (etaDen x y z 0 ≠ 0 ∧ ranadaEta x y z 0 = 0) ↔
      ∃ a : ℝ, (a, (0 : ℝ), (0 : ℝ)) = (x, y, z)
    rw [ranadaEta_initial_zero_iff]
    constructor
    · rintro ⟨rfl, rfl⟩
      exact ⟨x, rfl⟩
    · rintro ⟨a, he⟩
      obtain ⟨_, hy, hz⟩ := by simpa only [Prod.mk.injEq] using he.symm
      exact ⟨hy, hz⟩
  rw [← magnetic_fiber_at_eq_reflected_ray_image, h0, ← Set.range_comp]
  rfl

end Qatlib.Papers.KnottedLight08.NullLinking
