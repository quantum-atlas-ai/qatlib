/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Papers.KnotLight13.TorusFamily.BatemanPoyntingRays
public import Qatlib.Papers.KnotLight13.TorusFamily.BatemanPotential

import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Ring

/-!
# Shear-free Bateman rays

[Kedia2013TyingKnots], page 150404-2,
[DOI](https://doi.org/10.1103/physrevlett.111.150404).
The symmetric part of the spatial derivative of the normalized
Poynting direction, restricted to the transverse plane, is a scalar
multiple of the Euclidean pairing.
-/

@[expose] public section
set_option autoImplicit false

namespace Qatlib.Papers.KnotLight13.TorusFamily

open Qatlib.Papers.KnottedLight08.HopfField (dot3)

local notation "Space" => ℝ × ℝ × ℝ
local notation "cartesian" => batemanCartesianCoordinates

/-- The normalized Poynting direction as a vector of physical space. -/
noncomputable def batemanRayDirection (t : ℝ) (s : Space) : Space :=
  batemanCartesianCoordinates.symm (poyntingFlow s.1 s.2.1 s.2.2 t)

/-- The direction whose shear is measured is the velocity of the
actual straight Bateman ray through the spatial point. -/
theorem hasDerivAt_batemanRay_direction (t : ℝ) (s : Space) :
    HasDerivAt (fun τ => batemanRay τ s) (batemanRayDirection t (batemanRay t s)) t := by
  obtain ⟨hx, hy, hz⟩ := batemanRay_hasDerivAt t s
  exact hx.prodMk (hy.prodMk hz)

/-- The numerator of the normalized Poynting direction, with retarded axial coordinate. -/
private noncomputable def directionNumerator (t : ℝ) (s : Space) : Space :=
  (2 * (s.2.1 - (s.2.2 - t) * s.1),
    -2 * (s.1 + (s.2.2 - t) * s.2.1),
    s.1 ^ 2 + s.2.1 ^ 2 - (s.2.2 - t) ^ 2 - 1)

/-- The positive quadratic denominator of the normalized Poynting direction. -/
private noncomputable def directionDenominator (t : ℝ) (s : Space) : ℝ :=
  s.1 ^ 2 + s.2.1 ^ 2 + (s.2.2 - t) ^ 2 + 1

/-- The normalized Poynting direction is the explicit rational numerator divided by its denominator. -/
private theorem rayDirection_eq (t : ℝ) (s : Space) :
    batemanRayDirection t s = (directionDenominator t s)⁻¹ • directionNumerator t s := by
  rcases s with ⟨x, y, z⟩
  have h : poyntingFlow x y z t = poyntingFlow x y (z - t) 0 := by
    have ha : alphaCommonFactor z t = alphaCommonFactor (z - t) 0 := by
      unfold alphaCommonFactor
      rw [show t - z = 0 - (z - t) by ring]
    rw [poyntingFlow_eq_spinorVelocity, poyntingFlow_eq_spinorVelocity, ha]
  unfold batemanRayDirection
  rw [h, poyntingFlow_initial]
  apply batemanCartesianCoordinates.injective
  rw [LinearEquiv.apply_symm_apply, map_smul]
  funext i
  fin_cases i <;>
    simp [directionDenominator, directionNumerator, batemanCartesianCoordinates, div_eq_mul_inv, mul_comm]

/-- The unnormalized vector is a smooth polynomial in the physical coordinates. -/
private theorem contDiff_directionNumerator (t : ℝ) : ContDiff ℝ ⊤ (directionNumerator t) := by
  unfold directionNumerator
  fun_prop

/-- The directional derivative of the polynomial numerator. -/
private theorem fderiv_directionNumerator (t : ℝ) (s v : Space) :
    fderiv ℝ (directionNumerator t) s v =
      (2 * (v.2.1 - (s.2.2 - t) * v.1 - v.2.2 * s.1),
        -2 * (v.1 + (s.2.2 - t) * v.2.1 + v.2.2 * s.2.1),
        2 * (s.1 * v.1 + s.2.1 * v.2.1 - (s.2.2 - t) * v.2.2)) := by
  rcases s with ⟨x, y, z⟩
  rcases v with ⟨a, b, c⟩
  let line : ℝ → Space := fun r => (x + r * a, y + r * b, z + r * c)
  have h0 : line 0 = (x, y, z) := by simp [line]
  have hx : HasDerivAt (fun r : ℝ => x + r * a) a 0 := by
    simpa only [id_eq, one_mul] using ((hasDerivAt_id 0).mul_const a).const_add x
  have hy : HasDerivAt (fun r : ℝ => y + r * b) b 0 := by
    simpa only [id_eq, one_mul] using ((hasDerivAt_id 0).mul_const b).const_add y
  have hz : HasDerivAt (fun r : ℝ => z + r * c) c 0 := by
    simpa only [id_eq, one_mul] using ((hasDerivAt_id 0).mul_const c).const_add z
  have hZ := hz.sub_const t
  have hL : HasDerivAt line (a, b, c) 0 := hx.prodMk (hy.prodMk hz)
  have hN := ((contDiff_directionNumerator t).differentiable (by simp) (line 0)).hasFDerivAt
  have h := (hN.comp_hasDerivAt 0 hL).deriv
  rw [h0] at h
  have h₁ := ((hy.sub (hZ.mul hx)).const_mul 2)
  have h₂ := ((hx.add (hZ.mul hy)).const_mul (-2))
  have h₃ := ((((hx.pow 2).add (hy.pow 2)).sub (hZ.pow 2)).sub_const 1)
  have hprod : HasDerivAt (directionNumerator t ∘ line) _ 0 := h₁.prodMk (h₂.prodMk h₃)
  rw [← h, hprod.deriv]
  refine Prod.ext ?_ (Prod.ext ?_ ?_) <;> norm_num <;> ring

/-- The symmetric derivative of the numerator is scalar on the entire spatial slice. -/
private theorem directionNumerator_symmetric (t : ℝ) (s u v : Space) :
    dot3 (cartesian u) (cartesian (fderiv ℝ (directionNumerator t) s v)) +
      dot3 (cartesian v) (cartesian (fderiv ℝ (directionNumerator t) s u)) =
    (-4 * (s.2.2 - t)) * dot3 (cartesian u) (cartesian v) := by
  rw [fderiv_directionNumerator, fderiv_directionNumerator]
  simp [dot3, batemanCartesianCoordinates]
  ring

/-- On the plane perpendicular to the normalized Poynting direction,
the symmetric derivative is proportional to the Euclidean pairing.
Thus the transverse trace-free shear tensor of the explicit Bateman
congruence vanishes at every space-time point. -/
theorem batemanRayDirection_shearFree (t : ℝ) (s u v : Space)
    (hu : dot3 (cartesian u) (cartesian (batemanRayDirection t s)) = 0)
    (hv : dot3 (cartesian v) (cartesian (batemanRayDirection t s)) = 0) :
    dot3 (cartesian u) (cartesian (fderiv ℝ (batemanRayDirection t) s v)) +
      dot3 (cartesian v) (cartesian (fderiv ℝ (batemanRayDirection t) s u)) =
    (-4 * (s.2.2 - t) / (s.1 ^ 2 + s.2.1 ^ 2 + (s.2.2 - t) ^ 2 + 1)) *
      dot3 (cartesian u) (cartesian v) := by
  let den := directionDenominator t
  let num := directionNumerator t
  have hden (x : Space) : den x ≠ 0 := by unfold den directionDenominator; positivity
  have hd : ContDiff ℝ ⊤ den := by unfold den directionDenominator; fun_prop
  have hn := contDiff_directionNumerator t
  have h := funext (rayDirection_eq t)
  rw [h] at hu hv ⊢
  have hpair (a b c : Space) (k l : ℝ) :
      dot3 (cartesian a) (cartesian (k • b + l • c)) =
        k * dot3 (cartesian a) (cartesian b) + l * dot3 (cartesian a) (cartesian c) := by
    simp only [map_add, map_smul, dot3, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    ring
  have horth (a : Space) (ha : dot3 (cartesian a) (cartesian ((den s)⁻¹ • num s)) = 0) :
      dot3 (cartesian a) (cartesian (num s)) = 0 := by
    have hm := hpair a (num s) 0 (den s)⁻¹ 0
    simp only [zero_smul, add_zero, zero_mul, ha] at hm
    exact (mul_eq_zero.mp hm.symm).resolve_left (inv_ne_zero (hden s))
  have hD (a : Space) :
      fderiv ℝ (fun x => (den x)⁻¹ • num x) s a =
        (fderiv ℝ (fun x => (den x)⁻¹) s a) • num s + (den s)⁻¹ • fderiv ℝ num s a := by
    have hi : DifferentiableAt ℝ (fun x => (den x)⁻¹) s := (hd.inv hden).differentiable (by simp) s
    rw [fderiv_fun_smul hi (hn.differentiable (by simp) s)]
    simpa only [add_apply, smul_apply, ContinuousLinearMap.smulRight_apply] using
      add_comm ((den s)⁻¹ • fderiv ℝ num s a)
        (fderiv ℝ (fun x => (den x)⁻¹) s a • num s)
  rw [hD, hD, hpair, hpair, horth _ hu, horth _ hv, mul_zero, mul_zero, zero_add, zero_add,
    ← mul_add, directionNumerator_symmetric]
  change (den s)⁻¹ * (-4 * (s.2.2 - t) * dot3 (cartesian u) (cartesian v)) = _
  rw [div_eq_mul_inv]
  dsimp only [den, directionDenominator]
  ring

end Qatlib.Papers.KnotLight13.TorusFamily
