/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Papers.KnottedLight08.NullLinking.InitialMagneticFlow

import Mathlib.Analysis.SpecialFunctions.Complex.Arg
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring

/-!
# Closed oriented magnetic field lines on the initial slice

[IrvineBouwmeester2008KnottedLight], Eq. (2) and Fig. 1,
[DOI](https://doi.org/10.1038/nphys1056).
A periodic regular parameterization covers each finite nonzero fiber of
the Rañada magnetic scalar. Its actual coordinate derivatives agree
with the magnetic field up to a strictly positive speed factor.
-/

@[expose] public section
set_option autoImplicit false

namespace Qatlib.Papers.KnottedLight08.NullLinking

open Qatlib.Papers.KnottedLight08.HopfField (dot3 cross3)
open Qatlib.Papers.KnottedLight08.HopfField

/-- Cartesian coordinates in the plane normal to `(u²+v²,v,−u)`.
The displacement is measured from the center of the corresponding circle. -/
noncomputable def planeDisplacement (u v p q : ℝ) : Fin 3 → ℝ :=
  let d := u ^ 2 + v ^ 2
  ![-q / d, (u * p + v * q) / d, (v * p - u * q) / d]

/-- At unit angular rate the negative rotation traverses the initial
magnetic circle in the orientation of the actual magnetic field. -/
noncomputable def initialMagneticCircle (u v θ : ℝ) : EuclideanSpace ℝ (Fin 3) :=
  let d := u ^ 2 + v ^ 2
  let w := planeDisplacement u v (Real.sqrt (d + 1) * Real.cos θ) (Real.sqrt d * Real.sin θ)
  WithLp.toLp 2 (fun j => initialMagneticFiberCenter u v j + w j)

/-- The tangent vector in the circle parameter is the displacement with
the differentiated trigonometric coordinates. -/
noncomputable def initialMagneticCircleTangent (u v θ : ℝ) : Fin 3 → ℝ :=
  let d := u ^ 2 + v ^ 2
  planeDisplacement u v (Real.sqrt (d + 1) * (-Real.sin θ)) (Real.sqrt d * Real.cos θ)

/-- The plane coordinates lie in the plane normal to the magnetic axis. -/
private theorem plane_displacement_plane (u v p q : ℝ) (hd : 0 < u ^ 2 + v ^ 2) :
    let d := u ^ 2 + v ^ 2
    let w := planeDisplacement u v p q
    d * w 0 = u * w 2 - v * w 1 := by
  simp [planeDisplacement]
  field_simp [hd.ne']
  ring

/-- The plane-coordinate metric in terms of its two scalar coordinates. -/
private theorem plane_displacement_length (u v p q : ℝ) (hd : 0 < u ^ 2 + v ^ 2) :
    let d := u ^ 2 + v ^ 2
    let w := planeDisplacement u v p q
    dot3 w w = (d * p ^ 2 + (d + 1) * q ^ 2) / d ^ 2 := by
  simp [planeDisplacement, dot3]
  field_simp [hd.ne']
  ring

/-- A unit-circle coefficient pair yields the correct squared radius in
the plane coordinates. -/
private theorem plane_displacement_circle_length (u v a b : ℝ)
    (hd : 0 < u ^ 2 + v ^ 2) (hab : a ^ 2 + b ^ 2 = 1) :
    let d := u ^ 2 + v ^ 2
    let w := planeDisplacement u v (Real.sqrt (d + 1) * a) (Real.sqrt d * b)
    dot3 w w = 1 + 1 / d := by
  dsimp only
  rw [plane_displacement_length u v _ _ hd, mul_pow, mul_pow,
    Real.sq_sqrt (by positivity : 0 ≤ u ^ 2 + v ^ 2 + 1), Real.sq_sqrt hd.le]
  let d := u ^ 2 + v ^ 2
  change (d * ((d + 1) * a ^ 2) + (d + 1) * (d * b ^ 2)) / d ^ 2 = 1 + 1 / d
  rw [show d * ((d + 1) * a ^ 2) + (d + 1) * (d * b ^ 2) =
    (d * (d + 1)) * (a ^ 2 + b ^ 2) by ring, hab, mul_one]
  field_simp [show d ≠ 0 from hd.ne']

/-- The circle parameterization is (2π)-periodic. -/
theorem initial_magnetic_circle_periodic (u v : ℝ) :
    Function.Periodic (initialMagneticCircle u v) (2 * Real.pi) := by
  intro θ
  unfold initialMagneticCircle
  rw [Real.cos_add_two_pi, Real.sin_add_two_pi]

/-- The parameterized circle stays on the literal magnetic scalar
fiber, inside its affine chart. -/
theorem initial_magnetic_circle_mem_fiber (u v θ : ℝ) (hd : 0 < u ^ 2 + v ^ 2) :
    initialMagneticCircle u v θ ∈ initialMagneticFiber u v := by
  let d := u ^ 2 + v ^ 2
  let w := planeDisplacement u v (Real.sqrt (d + 1) * Real.cos θ) (Real.sqrt d * Real.sin θ)
  let c := initialMagneticFiberCenter u v
  let s := initialMagneticCircle u v θ
  have hcoord (j : Fin 3) : s j = c j + w j := rfl
  have hc0 : c 0 = 0 := rfl
  have hc1 : c 1 = -u / d := rfl
  have hc2 : c 2 = -v / d := rfl
  have hp : d * w 0 = u * w 2 - v * w 1 := plane_displacement_plane u v _ _ hd
  have hl : dot3 w w = 1 + 1 / d :=
    plane_displacement_circle_length u v _ _ hd (by
      rw [add_comm]; exact Real.sin_sq_add_cos_sq θ)
  change etaDen (s 0) (s 1) (s 2) 0 ≠ 0 ∧ ranadaEta (s 0) (s 1) (s 2) 0 =
    (u : ℂ) + Complex.I * (v : ℂ)
  apply (ranadaEta_initial_fiber_iff u v (s 0) (s 1) (s 2) hd).2
  change d * s 0 = u * s 2 - v * s 1 ∧
    s 0 ^ 2 + (s 1 + u / d) ^ 2 + (s 2 + v / d) ^ 2 = 1 + 1 / d
  constructor
  · rw [hcoord, hcoord, hcoord, hc0, hc1, hc2]
    rw [zero_add]
    field_simp [show d ≠ 0 from hd.ne']
    linear_combination d * hp
  · rw [hcoord, hcoord, hcoord, hc0, hc1, hc2]
    have hy : -u / d + w 1 + u / d = w 1 := by ring
    have hz : -v / d + w 2 + v / d = w 2 := by ring
    rw [zero_add, hy, hz]
    unfold dot3 at hl
    simpa only [pow_two] using hl

/-- The inverse plane coordinates recover any displacement satisfying
the plane equation. -/
private theorem plane_displacement_recover (u v x y z : ℝ) (hd : 0 < u ^ 2 + v ^ 2)
    (hplane : (u ^ 2 + v ^ 2) * x = u * z - v * y) :
    planeDisplacement u v (u * y + v * z) (-(u ^ 2 + v ^ 2) * x) = ![x, y, z] := by
  funext j
  fin_cases j
  · simp [planeDisplacement]
    field_simp [hd.ne']
    ring
  · simp [planeDisplacement]
    field_simp [hd.ne']
    linear_combination -v * hplane
  · simp [planeDisplacement]
    field_simp [hd.ne']
    linear_combination u * hplane

/-- A real coordinate pair of unit squared length admits an angle
with exactly those cosine and sine values. -/
theorem exists_angle_of_unit_coordinates (a b : ℝ) (hab : a ^ 2 + b ^ 2 = 1) :
    ∃ θ : ℝ, Real.cos θ = a ∧ Real.sin θ = b := by
  let w : ℂ := (a : ℂ) + Complex.I * (b : ℂ)
  have hre : w.re = a := by simp [w, Complex.mul_re]
  have him : w.im = b := by simp [w, Complex.mul_im]
  have hn : ‖w‖ = 1 := by
    rw [Complex.norm_def, Complex.normSq_apply, hre, him, ← pow_two, ← pow_two, hab,
      Real.sqrt_one]
  have hw : w ≠ 0 := by
    intro h0
    rw [h0, norm_zero] at hn
    exact zero_ne_one hn
  refine ⟨Complex.arg w, ?_, ?_⟩
  · rw [Complex.cos_arg hw, hn, hre, div_one]
  · rw [Complex.sin_arg, hn, him, div_one]

/-- The periodic parameterization covers the entire finite nonzero
initial magnetic fiber. -/
theorem range_initial_magnetic_circle (u v : ℝ) (hd : 0 < u ^ 2 + v ^ 2) :
    Set.range (initialMagneticCircle u v) = initialMagneticFiber u v := by
  ext s
  constructor
  · rintro ⟨θ, rfl⟩
    exact initial_magnetic_circle_mem_fiber u v θ hd
  · intro h
    let d := u ^ 2 + v ^ 2
    let x := s 0
    let y := s 1 + u / d
    let z := s 2 + v / d
    let p := u * y + v * z
    let q := -d * x
    let σ := Real.sqrt (d + 1)
    let ρ := Real.sqrt d
    have hd' : d ≠ 0 := hd.ne'
    have hd₁ : 0 < d + 1 := by positivity
    have hσ : 0 < σ := Real.sqrt_pos.mpr hd₁
    have hρ : 0 < ρ := Real.sqrt_pos.mpr hd
    obtain ⟨hp, hlength⟩ := (ranadaEta_initial_fiber_iff u v (s 0) (s 1) (s 2) hd).1 h
    change x ^ 2 + y ^ 2 + z ^ 2 = 1 + 1 / d at hlength
    have hplane : d * x = u * z - v * y := by
      change d * x = u * s 2 - v * s 1 at hp
      dsimp only [y, z]
      field_simp [hd']
      linear_combination d * hp
    have he : planeDisplacement u v p q = ![x, y, z] :=
      plane_displacement_recover u v x y z hd hplane
    have hm := plane_displacement_length u v p q hd
    change dot3 (planeDisplacement u v p q) (planeDisplacement u v p q) =
      (d * p ^ 2 + (d + 1) * q ^ 2) / d ^ 2 at hm
    rw [he] at hm
    simp only [dot3, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.tail_cons, Matrix.head_cons, ← pow_two, hlength] at hm
    have hpq : d * p ^ 2 + (d + 1) * q ^ 2 = d * (d + 1) := by
      calc
        _ = (1 + 1 / d) * d ^ 2 := (div_eq_iff (pow_ne_zero 2 hd')).mp hm.symm
        _ = _ := by field_simp [hd']
    let a := p / σ
    let b := q / ρ
    have hab : a ^ 2 + b ^ 2 = 1 := by
      dsimp only [a, b, σ, ρ]
      rw [div_pow, div_pow, Real.sq_sqrt hd₁.le, Real.sq_sqrt hd.le]
      field_simp [hd', hd₁.ne']
      linear_combination hpq
    obtain ⟨θ, hcos, hsin⟩ := exists_angle_of_unit_coordinates a b hab
    have hP : σ * Real.cos θ = p := by
      rw [hcos]
      dsimp only [a]
      field_simp [hσ.ne']
    have hQ : ρ * Real.sin θ = q := by
      rw [hsin]
      dsimp only [b]
      field_simp [hρ.ne']
    refine ⟨θ, ?_⟩
    have hcoord (j : Fin 3) : initialMagneticCircle u v θ j =
        initialMagneticFiberCenter u v j +
          planeDisplacement u v (σ * Real.cos θ) (ρ * Real.sin θ) j := rfl
    ext j
    change initialMagneticCircle u v θ j = s j
    rw [hcoord, hP, hQ, he]
    fin_cases j <;> simp [initialMagneticFiberCenter, x, y, z, d] <;> ring

/-- A Cartesian component of the trigonometric circle has the actual
coordinate derivative prescribed by the tangent vector. -/
theorem hasDerivAt_initial_magnetic_circle (u v θ : ℝ) (j : Fin 3) :
    HasDerivAt (fun t => initialMagneticCircle u v t j) (initialMagneticCircleTangent u v θ j) θ := by
  let d := u ^ 2 + v ^ 2
  let ρ := Real.sqrt d
  let σ := Real.sqrt (d + 1)
  have hsin := (Real.hasDerivAt_sin θ).const_mul ρ
  have hcos := (Real.hasDerivAt_cos θ).const_mul σ
  fin_cases j
  · change HasDerivAt (fun t => 0 + -(ρ * Real.sin t) / d) (-(ρ * Real.cos θ) / d) θ
    exact (hsin.neg.div_const d).const_add 0
  · change HasDerivAt (fun t => -u / d + (u * (σ * Real.cos t) + v * (ρ * Real.sin t)) / d)
      ((u * (σ * (-Real.sin θ)) + v * (ρ * Real.cos θ)) / d) θ
    exact (((hcos.const_mul u).add (hsin.const_mul v)).div_const d).const_add (-u / d)
  · change HasDerivAt (fun t => -v / d + (v * (σ * Real.cos t) - u * (ρ * Real.sin t)) / d)
      ((v * (σ * (-Real.sin θ)) - u * (ρ * Real.cos θ)) / d) θ
    exact (((hcos.const_mul v).sub (hsin.const_mul u)).div_const d).const_add (-v / d)

/-- The periodic parameterization is regular at every angle, with
constant positive squared speed. -/
theorem initial_magnetic_circle_tangent_length (u v θ : ℝ) (hd : 0 < u ^ 2 + v ^ 2) :
    dot3 (initialMagneticCircleTangent u v θ) (initialMagneticCircleTangent u v θ) =
      1 + 1 / (u ^ 2 + v ^ 2) :=
  plane_displacement_circle_length u v (-Real.sin θ) (Real.cos θ) hd (by
    rw [neg_sq]; exact Real.sin_sq_add_cos_sq θ)

/-- Cross product with the fixed axis acts as rotation in the
two scalar plane coordinates. -/
private theorem rotate_plane_displacement (u v p q : ℝ) (hd : 0 < u ^ 2 + v ^ 2)
    (j : Fin 3) :
    let d := u ^ 2 + v ^ 2
    cross3 (initialMagneticAxis u v) (planeDisplacement u v p q) j =
      planeDisplacement u v ((d + 1) * q) (-d * p) j := by
  fin_cases j <;> simp [initialMagneticAxis, planeDisplacement, cross3] <;>
    field_simp [hd.ne'] <;> ring

/-- On the parameterized fiber the true magnetic field is a positive
multiple of the tangent, so increasing the angle follows its orientation. -/
theorem ranada_b_along_initial_magnetic_circle (u v θ : ℝ) (hd : 0 < u ^ 2 + v ^ 2) :
    let s := initialMagneticCircle u v θ
    ∃ c > 0, ∀ j, (ranadaB (s 0) (s 1) (s 2) 0 j).re =
      c * initialMagneticCircleTangent u v θ j := by
  let d := u ^ 2 + v ^ 2
  let ρ := Real.sqrt d
  let σ := Real.sqrt (d + 1)
  let s := initialMagneticCircle u v θ
  let C := hopfScale (s 0) (s 1) (s 2)
  let p := σ * Real.cos θ
  let q := ρ * Real.sin θ
  let w := planeDisplacement u v p q
  have hρ : 0 < ρ := Real.sqrt_pos.mpr hd
  have hσ : 0 < σ := Real.sqrt_pos.mpr (show 0 < d + 1 from by positivity)
  have hρsq : ρ ^ 2 = d := Real.sq_sqrt hd.le
  have hσsq : σ ^ 2 = d + 1 := Real.sq_sqrt (by positivity)
  have hC : 0 < C := hopf_scale_pos _ _ _
  have hs (j : Fin 3) : s j = initialMagneticFiberCenter u v j + w j := rfl
  have hvec : (![s 0, s 1 + u / d, s 2 + v / d] : Fin 3 → ℝ) = w := by
    funext j
    fin_cases j <;> simp [hs, initialMagneticFiberCenter, d] <;> ring
  have hrotate (j : Fin 3) :
      initialMagneticRotation u v (s 0) (s 1) (s 2) j =
        -(ρ * σ) * initialMagneticCircleTangent u v θ j := by
    unfold initialMagneticRotation
    change cross3 (initialMagneticAxis u v) ![s 0, s 1 + u / d, s 2 + v / d] j = _
    rw [hvec, rotate_plane_displacement u v p q hd]
    change planeDisplacement u v ((d + 1) * q) (-d * p) j =
      -(ρ * σ) * planeDisplacement u v (σ * (-Real.sin θ)) (ρ * Real.cos θ) j
    rw [← hσsq, ← hρsq]
    fin_cases j <;> simp [planeDisplacement, p, q] <;> ring
  change ∃ c > 0, ∀ j, (ranadaB (s 0) (s 1) (s 2) 0 j).re =
    c * initialMagneticCircleTangent u v θ j
  refine ⟨2 * (ρ * σ) / (Real.pi * C ^ 2 * (d + 1)), by positivity, fun j => ?_⟩
  rw [ranada_b_initial_eq_rotation u v _ _ _ hd (initial_magnetic_circle_mem_fiber u v θ hd),
    hrotate]
  change (-2 / (Real.pi * C ^ 2 * (d + 1))) *
    (-(ρ * σ) * initialMagneticCircleTangent u v θ j) = _
  ring

end Qatlib.Papers.KnottedLight08.NullLinking
