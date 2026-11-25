/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Papers.KnotLight13.TorusFamily.BatemanEnergyTransport

import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring

/-!
# Stress-energy charges of the Bateman field

[Kedia2013TyingKnots], conserved quantities on page 150404-3,
[DOI](https://doi.org/10.1103/physrevlett.111.150404).
The physical momentum density is the electric–magnetic cross product.
For the powered field it equals the energy density times the straight-ray
velocity, including at zeros of the field. This gives an explicit
transport law for the Poincaré and conformal charge densities.
-/

@[expose] public section
set_option autoImplicit false

namespace Qatlib.Papers.KnotLight13.TorusFamily

open Qatlib.Papers.KnottedLight08.HopfField (cross3 dot3 squaredLength)
open Qatlib.Papers.KnotLight13.TorusFamily (rationalAlpha rationalBeta)
open scoped BigOperators

local notation "ChargeSpace" => ℝ × ℝ × ℝ

/-- The actual linear momentum density is the Poynting vector of the
powered electric and magnetic fields. -/
noncomputable def batemanFlux (p q : ℕ) (t : ℝ) (s : ChargeSpace) : Fin 3 → ℝ :=
  let f := rationalPowerField p q s.1 s.2.1 s.2.2 t
  cross3 (fun i => (f i).re) (fun i => (f i).im)

/-- The ray velocity in Cartesian components on a fixed time slice. -/
noncomputable def batemanVelocity (t : ℝ) (s : ChargeSpace) : Fin 3 → ℝ :=
  poyntingFlow s.1 s.2.1 s.2.2 t

/-- Half the squared magnitude of a scaled spinor field. -/
private theorem half_normSq_spinorField (k g h : ℂ) :
    (∑ j : Fin 3, Complex.normSq (k * spinorField g h j)) / 2 =
      Complex.normSq k * (Complex.normSq g + Complex.normSq h) ^ 2 := by
  simp [Fin.sum_univ_three, spinorField, Complex.normSq_apply, Complex.mul_re, Complex.mul_im,
    Complex.add_re, Complex.add_im, Complex.sub_re, Complex.sub_im, pow_two]
  ring

/-- Momentum density equals energy density times the actual normalized
ray velocity. The identity also holds at degeneracies of the powers. -/
theorem batemanFlux_eq_energy_smul_velocity (p q : ℕ) (t : ℝ) (s : ChargeSpace) :
    batemanFlux p q t s = batemanEnergyDensity p q t s • batemanVelocity t s := by
  rcases s with ⟨x, y, z⟩
  let g := alphaCommonFactor z t
  let h := betaReducedNumerator x y
  let k := rationalPowerFactor p q x y z t * (4 / complexDenominator x y z t ^ 3)
  have hf (j : Fin 3) : rationalPowerField p q x y z t j = k * spinorField g h j := by
    simp only [rationalPowerField_eq, rationalField_eq_spinorField]
    exact (mul_assoc _ _ _).symm
  have hg : g.re = 1 := by simp [g, alphaCommonFactor, Complex.mul_re]
  have hg₁ : g ≠ 0 := by
    intro hz
    simp only [hz, Complex.zero_re, zero_ne_one] at hg
  have hN := add_pos_of_pos_of_nonneg (Complex.normSq_pos.mpr hg₁) (Complex.normSq_nonneg h)
  funext j
  unfold batemanFlux batemanEnergyDensity batemanVelocity
  simp only [hf, poyntingFlow_eq_spinorVelocity, Pi.smul_apply, smul_eq_mul]
  rw [spinor_poynting, half_normSq_spinorField]
  change Complex.normSq k * (Complex.normSq g + Complex.normSq h) * spinorAxis g h j =
    Complex.normSq k * (Complex.normSq g + Complex.normSq h) ^ 2 *
      (spinorAxis g h j / (Complex.normSq g + Complex.normSq h))
  field_simp [hN.ne']

/-- Both scalar labels and thus the velocity stay fixed along each ray. -/
theorem batemanVelocity_batemanRay (t : ℝ) (s : ChargeSpace) :
    batemanVelocity t (batemanRay t s) = batemanVelocity 0 s := by
  have hα := congrArg Prod.fst (batemanPairAt_batemanRay t s)
  have hβ := congrArg Prod.snd (batemanPairAt_batemanRay t s)
  let r := batemanRay t s
  change rationalAlpha r.1 r.2.1 r.2.2 t = rationalAlpha s.1 s.2.1 s.2.2 0 at hα
  change rationalBeta r.1 r.2.1 r.2.2 t = rationalBeta s.1 s.2.1 s.2.2 0 at hβ
  unfold batemanVelocity
  rw [poyntingFlow_eq_batemanPair, poyntingFlow_eq_batemanPair, hα, hβ]

/-- The Cartesian ray position equals the initial position plus elapsed
time times the initial normalized velocity. -/
theorem batemanCartesianCoordinates_batemanRay (t : ℝ) (s : ChargeSpace) :
    batemanCartesianCoordinates (batemanRay t s) =
      batemanCartesianCoordinates s + t • batemanVelocity 0 s := by
  rcases s with ⟨x, y, z⟩
  have hd : x ^ 2 + y ^ 2 + z ^ 2 + 1 ≠ 0 := by positivity
  unfold batemanVelocity
  rw [poyntingFlow_initial]
  funext j
  fin_cases j <;>
    simp [batemanCartesianCoordinates, batemanRay, smul_eq_mul] <;> field_simp [hd] <;> ring

/-- The initial ray velocity is a unit vector. -/
theorem squaredLength_batemanVelocity_zero (s : ChargeSpace) :
    squaredLength (batemanVelocity 0 s) = 1 := by
  rcases s with ⟨x, y, z⟩
  have hd : x ^ 2 + y ^ 2 + z ^ 2 + 1 ≠ 0 := by positivity
  unfold batemanVelocity
  rw [poyntingFlow_initial]
  simp [squaredLength, dot3]
  field_simp [hd]
  ring

/-- The radial contraction of the initial ray velocity is minus the
initial vertical coordinate. -/
theorem dot3_position_batemanVelocity_zero (s : ChargeSpace) :
    dot3 (batemanCartesianCoordinates s) (batemanVelocity 0 s) = -s.2.2 := by
  rcases s with ⟨x, y, z⟩
  have hd : x ^ 2 + y ^ 2 + z ^ 2 + 1 ≠ 0 := by positivity
  unfold batemanVelocity
  rw [poyntingFlow_initial]
  simp [batemanCartesianCoordinates, dot3]
  field_simp [hd]
  ring

/-- The conserved quantities built from the energy and momentum densities
of a Maxwell field in Cartesian coordinates. -/
inductive BatemanChargeKind where
  | momentum (i : Fin 3)
  | angularMomentum (i : Fin 3)
  | boost (i : Fin 3)
  | dilation
  | conformalTime
  | conformalSpace (i : Fin 3)

/-- The local densities for the standard stress-energy charges with
angular momentum order of the published supplement. The conformal
currents use the conserved stress-energy convention. -/
noncomputable def maxwellChargeDensity (c : BatemanChargeKind) (t : ℝ)
    (x : Fin 3 → ℝ) (u : ℝ) (S : Fin 3 → ℝ) : ℝ :=
  match c with
  | .momentum i => S i
  | .angularMomentum i => cross3 S x i
  | .boost i => x i * u - t * S i
  | .dilation => dot3 x S - t * u
  | .conformalTime => (t ^ 2 + squaredLength x) * u - 2 * t * dot3 x S
  | .conformalSpace i => (t ^ 2 - squaredLength x) * S i + 2 * x i * (dot3 x S - t * u)

/-- The multiplier of the local energy in each charge density of the
powered Bateman field. -/
noncomputable def batemanChargeWeight (c : BatemanChargeKind) (t : ℝ) (s : ChargeSpace) : ℝ :=
  maxwellChargeDensity c t (batemanCartesianCoordinates s) 1 (batemanVelocity t s)

/-- The charge density formed from the actual electromagnetic energy
and momentum of the powered field. -/
noncomputable def batemanChargeDensity (c : BatemanChargeKind) (p q : ℕ) (t : ℝ)
    (s : ChargeSpace) : ℝ :=
  maxwellChargeDensity c t (batemanCartesianCoordinates s) (batemanEnergyDensity p q t s)
    (batemanFlux p q t s)

/-- A null stress-energy charge factors into the scalar energy density and
the charge weight at unit energy density. -/
private theorem maxwellChargeDensity_smul (c : BatemanChargeKind) (t : ℝ)
    (x v : Fin 3 → ℝ) (u : ℝ) :
    maxwellChargeDensity c t x u (u • v) = u * maxwellChargeDensity c t x 1 v := by
  cases c with
  | angularMomentum i =>
      fin_cases i <;> simp [maxwellChargeDensity, cross3, smul_eq_mul] <;> ring
  | momentum i => simp [maxwellChargeDensity, smul_eq_mul]
  | boost i => simp [maxwellChargeDensity, smul_eq_mul]; ring
  | dilation => simp [maxwellChargeDensity, dot3, smul_eq_mul]; ring
  | conformalTime => simp [maxwellChargeDensity, dot3, smul_eq_mul]; ring
  | conformalSpace i => simp [maxwellChargeDensity, dot3, smul_eq_mul]; ring

/-- The actual charge density equals the energy density times its
explicit ray weight. -/
theorem batemanChargeDensity_eq_energy_mul_weight (c : BatemanChargeKind) (p q : ℕ) (t : ℝ)
    (s : ChargeSpace) :
    batemanChargeDensity c p q t s = batemanEnergyDensity p q t s * batemanChargeWeight c t s := by
  unfold batemanChargeDensity batemanChargeWeight
  rw [batemanFlux_eq_energy_smul_velocity, maxwellChargeDensity_smul]

/-- Each standard charge weight is constant along a unit-speed straight
ray, including the quadratic special conformal weights. -/
private theorem maxwellChargeDensity_straight_ray (c : BatemanChargeKind) (t : ℝ)
    (x v : Fin 3 → ℝ) (hv : squaredLength v = 1) :
    maxwellChargeDensity c t (x + t • v) 1 v = maxwellChargeDensity c 0 x 1 v := by
  have hdot : dot3 (x + t • v) v = dot3 x v + t := by
    simp only [dot3, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    unfold squaredLength dot3 at hv
    linear_combination t * hv
  have hlen : squaredLength (x + t • v) = squaredLength x + 2 * t * dot3 x v + t ^ 2 := by
    simp only [squaredLength, dot3, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    unfold squaredLength dot3 at hv
    linear_combination t ^ 2 * hv
  cases c with
  | momentum i => rfl
  | angularMomentum i =>
      fin_cases i <;> simp [maxwellChargeDensity, cross3, smul_eq_mul] <;> ring
  | boost i => simp [maxwellChargeDensity, smul_eq_mul]
  | dilation => simp [maxwellChargeDensity, hdot]
  | conformalTime => simp [maxwellChargeDensity, hdot, hlen]; ring
  | conformalSpace i => simp [maxwellChargeDensity, hdot, hlen, smul_eq_mul]; ring

/-- The actual charge weight pulls back to its initial value. -/
theorem batemanChargeWeight_batemanRay (c : BatemanChargeKind) (t : ℝ) (s : ChargeSpace) :
    batemanChargeWeight c t (batemanRay t s) = batemanChargeWeight c 0 s := by
  unfold batemanChargeWeight
  rw [batemanVelocity_batemanRay, batemanCartesianCoordinates_batemanRay]
  exact maxwellChargeDensity_straight_ray c t (batemanCartesianCoordinates s) (batemanVelocity 0 s)
    (squaredLength_batemanVelocity_zero s)

/-- Each of the actual electromagnetic charge densities is transported
with the physical ray Jacobian. -/
theorem batemanChargeDensity_jacobian (c : BatemanChargeKind) (p q : ℕ) (t : ℝ) (s : ChargeSpace) :
    LinearMap.det (fderiv ℝ (batemanRay t) s).toLinearMap *
      batemanChargeDensity c p q t (batemanRay t s) = batemanChargeDensity c p q 0 s := by
  rw [batemanChargeDensity_eq_energy_mul_weight, batemanChargeDensity_eq_energy_mul_weight,
    batemanChargeWeight_batemanRay, ← mul_assoc, batemanEnergyDensity_jacobian]

end Qatlib.Papers.KnotLight13.TorusFamily
