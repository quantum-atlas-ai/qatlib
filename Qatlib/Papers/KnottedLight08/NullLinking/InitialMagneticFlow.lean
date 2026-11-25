/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Papers.KnottedLight08.HopfField.RanadaInitialPotential
public import Qatlib.Papers.KnottedLight08.NullLinking.InitialMagneticCircles

import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring

/-!
# The initial magnetic field on finite Hopf circles

[IrvineBouwmeester2008KnottedLight], Eq. (2),
[DOI](https://doi.org/10.1038/nphys1056).
On each initial finite nonzero magnetic fiber, the actual magnetic
direction is a strictly negative multiple of rotation about the normal
axis through the center of its circle.
-/

@[expose] public section
set_option autoImplicit false

namespace Qatlib.Papers.KnottedLight08.NullLinking

open Qatlib.Papers.KnottedLight08.HopfField (cross3)
open Qatlib.Papers.KnottedLight08.HopfField

/-- The normal axis to the plane of the initial finite magnetic fiber. -/
noncomputable def initialMagneticAxis (u v : ℝ) : Fin 3 → ℝ := ![u ^ 2 + v ^ 2, v, -u]

/-- The rotational direction at a point, around the fiber center and normal axis. -/
noncomputable def initialMagneticRotation (u v x y z : ℝ) : Fin 3 → ℝ :=
  cross3 (initialMagneticAxis u v)
    ![x, y + u / (u ^ 2 + v ^ 2), z + v / (u ^ 2 + v ^ 2)]

/-- The magnetic rotation has a polynomial Cartesian form on the nonzero fibers. -/
private theorem initial_magnetic_rotation_eq (u v x y z : ℝ) (hd : 0 < u ^ 2 + v ^ 2) :
    initialMagneticRotation u v x y z =
      ![1 + u * y + v * z, -u * x - (u ^ 2 + v ^ 2) * z - v,
        (u ^ 2 + v ^ 2) * y + u - v * x] := by
  funext j
  fin_cases j <;> simp [initialMagneticRotation, initialMagneticAxis, cross3] <;>
    field_simp [hd.ne'] <;> ring

/-- On a genuine finite nonzero magnetic fiber, the polynomial magnetic
direction is the rotational vector times the positive normalization
`(1 + x² + y² + z²) / (1 + u² + v²)`. -/
theorem initial_magnetic_direction_eq_rotation (u v x y z : ℝ) (hd : 0 < u ^ 2 + v ^ 2)
    (hf : etaDen x y z 0 ≠ 0 ∧ ranadaEta x y z 0 = (u : ℂ) + Complex.I * (v : ℂ))
    (j : Fin 3) :
    (u ^ 2 + v ^ 2 + 1) * initialMagneticDirection x y z j =
      hopfScale x y z * initialMagneticRotation u v x y z j := by
  let d := u ^ 2 + v ^ 2
  let c := (x ^ 2 + y ^ 2 + z ^ 2 - 1) / 2
  have hd' : d ≠ 0 := hd.ne'
  obtain ⟨hp, hs⟩ := (ranadaEta_initial_fiber_iff u v x y z hd).1 hf
  change d * x = u * z - v * y at hp
  change x ^ 2 + (y + u / d) ^ 2 + (z + v / d) ^ 2 = 1 + 1 / d at hs
  have hsum : u * y + v * z = -d * c := by
    have h : d * c + u * y + v * z =
        (d / 2) * (x ^ 2 + (y + u / d) ^ 2 + (z + v / d) ^ 2 - (1 + 1 / d)) := by
      unfold c
      field_simp [hd']
      unfold d
      ring
    rw [hs, sub_self, mul_zero] at h
    linarith only [h]
  have hy : y = -v * x - u * c := by
    apply mul_left_cancel₀ hd'
    unfold d at hp hsum ⊢
    linear_combination v * hp + u * hsum
  have hz : z = u * x - v * c := by
    apply mul_left_cancel₀ hd'
    unfold d at hp hsum ⊢
    linear_combination -u * hp + v * hsum
  have hrSq : x ^ 2 + y ^ 2 + z ^ 2 = (d + 1) * x ^ 2 + d * c ^ 2 := by
    rw [hy, hz]
    unfold d
    ring
  have hc : x ^ 2 + y ^ 2 + z ^ 2 = 2 * c + 1 := by
    unfold c
    ring
  have hpoly : (d + 1) * x ^ 2 + d * c ^ 2 = 2 * c + 1 := hrSq.symm.trans hc
  have hS : hopfScale x y z = 2 * (c + 1) := by
    unfold hopfScale
    linarith only [hc]
  rw [hS, initial_magnetic_rotation_eq u v x y z hd]
  change (d + 1) * initialMagneticDirection x y z j =
    (2 * (c + 1)) * ![1 + u * y + v * z, -u * x - d * z - v, d * y + u - v * x] j
  fin_cases j
  · simp [initialMagneticDirection]
    rw [hy, hz]
    unfold d at hpoly ⊢
    linear_combination (1 - (u ^ 2 + v ^ 2)) * hpoly
  · simp [initialMagneticDirection]
    rw [hy, hz]
    unfold d at hpoly ⊢
    linear_combination (-2 * v) * hpoly
  · simp [initialMagneticDirection]
    rw [hy, hz]
    unfold d at hpoly ⊢
    linear_combination (2 * u) * hpoly

/-- The actual magnetic field at the initial time is rotation in the
fiber plane with a nonzero negative coefficient. -/
theorem ranada_b_initial_eq_rotation (u v x y z : ℝ) (hd : 0 < u ^ 2 + v ^ 2)
    (hf : etaDen x y z 0 ≠ 0 ∧ ranadaEta x y z 0 = (u : ℂ) + Complex.I * (v : ℂ))
    (j : Fin 3) :
    (ranadaB x y z 0 j).re =
      (-2 / (Real.pi * hopfScale x y z ^ 2 * (u ^ 2 + v ^ 2 + 1))) *
        initialMagneticRotation u v x y z j := by
  have hd' : 0 < u ^ 2 + v ^ 2 + 1 := by positivity
  have hS := hopf_scale_pos x y z
  have hdir : initialMagneticDirection x y z j =
      hopfScale x y z * initialMagneticRotation u v x y z j / (u ^ 2 + v ^ 2 + 1) :=
    (eq_div_iff hd'.ne').2 (by simpa only [mul_comm] using
      initial_magnetic_direction_eq_rotation u v x y z hd hf j)
  rw [ranada_b_initial_re, hdir]
  field_simp [hS.ne', hd'.ne', Real.pi_ne_zero]

end Qatlib.Papers.KnottedLight08.NullLinking
