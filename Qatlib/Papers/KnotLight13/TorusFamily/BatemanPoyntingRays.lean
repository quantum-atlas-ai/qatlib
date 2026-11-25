/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Papers.KnotLight13.TorusFamily.BatemanTimeSlices
public import Qatlib.Papers.KnotLight13.TorusFamily.RationalPower
public import Qatlib.Papers.KnotLight13.TorusFamily.RationalTransport

import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-!
# The explicit Poynting rays of the Bateman field

[Kedia2013TyingKnots], Eq. (5) and Fig. 3,
[DOI](https://doi.org/10.1103/physrevlett.111.150404).
The rational Maxwell field has a quadratic spinor numerator. Its normalized
Poynting vector depends only on the projective spinor, hence only on the
two Bateman potentials. This identifies the straight rays transporting
the potentials with the actual normalized Poynting flow of the field.
-/

@[expose] public section
set_option autoImplicit false

namespace Qatlib.Papers.KnotLight13.TorusFamily

open Qatlib.Papers.KnotLight13.TorusFamily
  (radialAux rationalAlpha rationalBeta complex_rational_pair_unit torusPolynomial)
open Qatlib.Papers.KnottedLight08.HopfField (cross3 dot3 squaredLength)
open scoped ComplexConjugate

/-- The quadratic complex null vector associated to the two spinor coordinates. -/
noncomputable def spinorField (g h : ℂ) : Fin 3 → ℂ :=
  ![-(g ^ 2 + h ^ 2), Complex.I * (g ^ 2 - h ^ 2), -2 * Complex.I * g * h]

/-- The unnormalized real direction of the Poynting vector in spinor coordinates. -/
noncomputable def spinorAxis (g h : ℂ) : Fin 3 → ℝ :=
  ![-2 * (h * conj g).im, -2 * (h * conj g).re, Complex.normSq h - Complex.normSq g]

/-- The spinor direction normalized by the total squared spinor norm. -/
noncomputable def spinorVelocity (g h : ℂ) : Fin 3 → ℝ :=
  fun j => spinorAxis g h j / (Complex.normSq g + Complex.normSq h)

/-- The electric squared length of the scaled spinor field is the squared
total spinor norm times the scalar's squared norm. -/
private theorem spinor_electric_length (k g h : ℂ) :
    squaredLength (fun j => (k * spinorField g h j).re) =
      Complex.normSq k * (Complex.normSq g + Complex.normSq h) ^ 2 := by
  simp [squaredLength, dot3, spinorField, pow_two, Complex.normSq_apply,
    Complex.mul_re, Complex.mul_im]
  ring

/-- The Poynting vector of the scaled spinor field is the spinor axis
times the total squared spinor norm and the scalar's squared norm. -/
theorem spinor_poynting (k g h : ℂ) (j : Fin 3) :
    cross3 (fun j => (k * spinorField g h j).re) (fun j => (k * spinorField g h j).im) j =
      Complex.normSq k * (Complex.normSq g + Complex.normSq h) * spinorAxis g h j := by
  unfold cross3 spinorField spinorAxis
  fin_cases j <;>
    simp [pow_two, Complex.normSq_apply, Complex.mul_re, Complex.mul_im] <;> ring

/-- The field numerator factors into its denominator and the spinor field
of the reduced Bateman numerators. -/
private theorem crossNumerators_eq_spinor (x y z t : ℝ) (j : Fin 3) :
    cross3 (alphaGradientNumerators x y z t) (betaGradientNumerators x y z t) j =
      4 * complexDenominator x y z t *
        spinorField (alphaCommonFactor z t) (betaReducedNumerator x y) j := by
  unfold cross3 alphaGradientNumerators betaGradientNumerators spinorField
    alphaXNumerator alphaYNumerator alphaZNumerator betaXNumerator betaYNumerator
    betaZNumerator alphaCommonFactor betaReducedNumerator complexDenominator radialAux
  fin_cases j <;> apply Complex.ext <;>
    simp [pow_two, Complex.mul_re, Complex.mul_im] <;> ring

/-- The actual differentiated Maxwell field equals the spinor field times
four over the cube of the common denominator. -/
theorem rationalField_eq_spinorField (x y z t : ℝ) (j : Fin 3) :
    rationalField x y z t j =
      (4 / complexDenominator x y z t ^ 3) *
        spinorField (alphaCommonFactor z t) (betaReducedNumerator x y) j := by
  rw [rationalField_eq_cross_div, crossNumerators_eq_spinor]
  field_simp [complex_denominator_ne_zero]

/-- The first reduced numerator never vanishes because its real part is one. -/
private theorem alphaCommonFactor_ne_zero (z t : ℝ) : alphaCommonFactor z t ≠ 0 := by
  intro h
  have hre := congrArg Complex.re h
  norm_num [alphaCommonFactor, Complex.mul_re] at hre

/-- The rational electric field has strictly positive pointwise energy. -/
theorem rational_electric_length_pos (x y z t : ℝ) :
    0 < squaredLength (electricField x y z t) := by
  unfold electricField
  simp_rw [rationalField_eq_spinorField]
  rw [spinor_electric_length]
  refine mul_pos (Complex.normSq_pos.mpr ?_) (pow_pos (add_pos_of_pos_of_nonneg
    (Complex.normSq_pos.mpr (alphaCommonFactor_ne_zero z t))
    (Complex.normSq_nonneg _)) 2)
  exact div_ne_zero (by norm_num) (pow_ne_zero _ (complex_denominator_ne_zero x y z t))

/-- The normalized flux depends on the spinor and is unchanged by a
nonzero complex multiplier of the field. -/
private theorem normalized_spinor_flux (k g h : ℂ) (hk : k ≠ 0) (hg : g ≠ 0) (j : Fin 3) :
    cross3 (fun j => (k * spinorField g h j).re) (fun j => (k * spinorField g h j).im) j /
      squaredLength (fun j => (k * spinorField g h j).re) = spinorVelocity g h j := by
  have hd : 0 < Complex.normSq g + Complex.normSq h :=
    add_pos_of_pos_of_nonneg (Complex.normSq_pos.mpr hg) (Complex.normSq_nonneg _)
  rw [spinor_poynting, spinor_electric_length]
  unfold spinorVelocity
  field_simp [hd.ne', (Complex.normSq_pos.mpr hk).ne']

/-- The normalized Poynting field equals the normalized direction of the
reduced Bateman numerators. -/
theorem poyntingFlow_eq_spinorVelocity (x y z t : ℝ) :
    poyntingFlow x y z t = spinorVelocity (alphaCommonFactor z t) (betaReducedNumerator x y) := by
  have hk : (4 : ℂ) / complexDenominator x y z t ^ 3 ≠ 0 :=
    div_ne_zero (by norm_num) (pow_ne_zero _ (complex_denominator_ne_zero x y z t))
  unfold poyntingFlow electricField magneticField
  simp_rw [rationalField_eq_spinorField]
  funext j
  exact normalized_spinor_flux _ _ _ hk (alphaCommonFactor_ne_zero z t) j

/-- Scaling both coordinates by the same nonzero complex number preserves
the normalized spinor direction. -/
theorem spinorVelocity_mul (m g h : ℂ) (hm : m ≠ 0) :
    spinorVelocity (m * g) (m * h) = spinorVelocity g h := by
  have he : (m * h) * conj (m * g) = (Complex.normSq m : ℂ) * (h * conj g) := by
    rw [map_mul]
    calc
      _ = (m * conj m) * (h * conj g) := by ring
      _ = _ := by rw [Complex.mul_conj]
  have haxis (j : Fin 3) :
      spinorAxis (m * g) (m * h) j = Complex.normSq m * spinorAxis g h j := by
    unfold spinorAxis
    fin_cases j
    · change -2 * ((m * h) * conj (m * g)).im = Complex.normSq m * (-2 * (h * conj g).im)
      rw [he, Complex.mul_im]
      simp only [Complex.ofReal_im, Complex.ofReal_re, zero_mul, add_zero]
      ring
    · change -2 * ((m * h) * conj (m * g)).re = Complex.normSq m * (-2 * (h * conj g).re)
      rw [he, Complex.mul_re]
      simp only [Complex.ofReal_im, Complex.ofReal_re, zero_mul, sub_zero]
      ring
    · change Complex.normSq (m * h) - Complex.normSq (m * g) =
        Complex.normSq m * (Complex.normSq h - Complex.normSq g)
      rw [Complex.normSq_mul, Complex.normSq_mul, mul_sub]
  funext j
  simp only [spinorVelocity, haxis, Complex.normSq_mul, ← mul_add]
  exact mul_div_mul_left _ _ (Complex.normSq_pos.mpr hm).ne'

/-- The normalized Poynting vector is a function of the two Bateman
potentials, so it is constant along their straight rays. -/
theorem poyntingFlow_eq_batemanPair (x y z t : ℝ) :
    poyntingFlow x y z t = spinorVelocity (1 - rationalAlpha x y z t) (rationalBeta x y z t) := by
  rw [poyntingFlow_eq_spinorVelocity, one_sub_rationalAlpha, rationalBeta_eq_reduced]
  have hw (u : ℂ) : 2 * u / complexDenominator x y z t =
      (2 / complexDenominator x y z t) * u := by ring
  rw [hw, hw, spinorVelocity_mul _ _ _
    (div_ne_zero (by norm_num) (complex_denominator_ne_zero x y z t))]

/-- The explicit velocity on the initial slice agrees with the three slopes
of its straight ray. -/
theorem poyntingFlow_initial (x y z : ℝ) :
    poyntingFlow x y z 0 = fun j =>
      ![2 * (y - z * x), -2 * (x + z * y), x ^ 2 + y ^ 2 - z ^ 2 - 1] j /
        (x ^ 2 + y ^ 2 + z ^ 2 + 1) := by
  rw [poyntingFlow_eq_spinorVelocity]
  funext j
  unfold spinorVelocity spinorAxis alphaCommonFactor betaReducedNumerator
  fin_cases j <;>
    simp [Complex.normSq_apply, Complex.mul_re, Complex.mul_im, pow_two] <;> congr 1 <;> ring

/-- The coordinatewise derivative of the straight ray at any time is the
normalized Poynting velocity of the rational Maxwell field at that point. -/
theorem batemanRay_hasDerivAt (t : ℝ) (s : ℝ × ℝ × ℝ) :
    let v := poyntingFlow (batemanRay t s).1 (batemanRay t s).2.1 (batemanRay t s).2.2 t
    HasDerivAt (fun τ => (batemanRay τ s).1) (v 0) t ∧
      HasDerivAt (fun τ => (batemanRay τ s).2.1) (v 1) t ∧
      HasDerivAt (fun τ => (batemanRay τ s).2.2) (v 2) t := by
  rcases s with ⟨x, y, z⟩
  let d := x ^ 2 + y ^ 2 + z ^ 2 + 1
  have hd : d ≠ 0 := by positivity
  have ha : rationalAlpha (batemanRay t (x, y, z)).1 (batemanRay t (x, y, z)).2.1
      (batemanRay t (x, y, z)).2.2 t = rationalAlpha x y z 0 :=
    congrArg Prod.fst (batemanPairAt_batemanRay t (x, y, z))
  have hb : rationalBeta (batemanRay t (x, y, z)).1 (batemanRay t (x, y, z)).2.1
      (batemanRay t (x, y, z)).2.2 t = rationalBeta x y z 0 :=
    congrArg Prod.snd (batemanPairAt_batemanRay t (x, y, z))
  have hv : poyntingFlow (batemanRay t (x, y, z)).1 (batemanRay t (x, y, z)).2.1
      (batemanRay t (x, y, z)).2.2 t = poyntingFlow x y z 0 := by
    rw [poyntingFlow_eq_batemanPair, poyntingFlow_eq_batemanPair, ha, hb]
  dsimp only
  rw [hv, poyntingFlow_initial]
  have hscale : HasDerivAt (fun τ : ℝ => 2 * τ / d) (2 / d) t := by
    simpa only [id_eq, mul_one] using (((hasDerivAt_id t).const_mul 2).div_const d)
  refine ⟨?_, ?_, ?_⟩
  · exact ((hasDerivAt_const t x).add (hscale.mul_const (y - z * x))).congr_deriv (by
      change 0 + 2 / d * (y - z * x) = 2 * (y - z * x) / d
      ring)
  · exact ((hasDerivAt_const t y).sub (hscale.mul_const (x + z * y))).congr_deriv (by
      change 0 - 2 / d * (x + z * y) = -2 * (x + z * y) / d
      ring)
  · exact (((hasDerivAt_const t z).add (hasDerivAt_id t)).sub
      (hscale.mul_const (z ^ 2 + 1))).congr_deriv (by
    change 0 + 1 - 2 / d * (z ^ 2 + 1) = (x ^ 2 + y ^ 2 - z ^ 2 - 1) / d
    field_simp [hd]
    unfold d
    ring)

/-- The normalized Poynting velocity of the actual powered field. -/
noncomputable def poyntingPowerFlow (p q : ℕ) (x y z t : ℝ) : Fin 3 → ℝ :=
  let e := fun j => (rationalPowerField p q x y z t j).re
  let b := fun j => (rationalPowerField p q x y z t j).im
  fun j => cross3 e b j / squaredLength e

/-- The base and powered fields have the same normalized velocity wherever
the powered field's reparametrization factor is nonzero. -/
theorem poyntingPowerFlow_eq (p q : ℕ) (x y z t : ℝ)
    (h : rationalPowerFactor p q x y z t ≠ 0) :
    poyntingPowerFlow p q x y z t = poyntingFlow x y z t := by
  rw [poyntingFlow_eq_spinorVelocity]
  unfold poyntingPowerFlow
  simp_rw [rationalPowerField_eq, rationalField_eq_spinorField, ← mul_assoc]
  funext j
  refine normalized_spinor_flux _ _ _ (mul_ne_zero h ?_) (alphaCommonFactor_ne_zero z t) j
  exact div_ne_zero (by norm_num) (pow_ne_zero _ (complex_denominator_ne_zero x y z t))

/-- For positive exponents, neither potential vanishes on the torus zero
locus and the power reparametrization factor is nonzero there. -/
theorem rationalPowerFactor_ne_zero_on_locus {p q : ℕ} (hp : 0 < p) (hq : 0 < q)
    (x y z t : ℝ)
    (h : torusPolynomial p q (rationalAlpha x y z t) (rationalBeta x y z t) = 0) :
    rationalPowerFactor p q x y z t ≠ 0 := by
  rw [torusPolynomial, sub_eq_zero] at h
  have hu := complex_rational_pair_unit x y z t
  have ha : rationalAlpha x y z t ≠ 0 := by
    intro ha
    have hb : rationalBeta x y z t = 0 := by
      by_contra hb
      exact pow_ne_zero q hb (by rw [← h, ha, zero_pow hp.ne'])
    simp [ha, hb] at hu
  have hb : rationalBeta x y z t ≠ 0 := by
    intro hb
    exact pow_ne_zero p ha (by rw [h, hb, zero_pow hq.ne'])
  have hp' : (p : ℂ) ≠ 0 := by exact_mod_cast hp.ne'
  have hq' : (q : ℂ) ≠ 0 := by exact_mod_cast hq.ne'
  exact mul_ne_zero (mul_ne_zero hp' (pow_ne_zero _ ha)) (mul_ne_zero hq' (pow_ne_zero _ hb))

/-- An initial torus-locus point follows the actual Poynting flow of its
powered Maxwell field at every real time. -/
theorem batemanRay_hasDerivAt_power {p q : ℕ} (hp : 0 < p) (hq : 0 < q)
    (t : ℝ) {s : ℝ × ℝ × ℝ} (hs : s ∈ initialSpatialKnot p q) :
    let r := batemanRay t s
    let v := poyntingPowerFlow p q r.1 r.2.1 r.2.2 t
    HasDerivAt (fun τ => (batemanRay τ s).1) (v 0) t ∧
      HasDerivAt (fun τ => (batemanRay τ s).2.1) (v 1) t ∧
      HasDerivAt (fun τ => (batemanRay τ s).2.2) (v 2) t := by
  let r := batemanRay t s
  have hr : torusPolynomial p q (batemanPairAt t (batemanRay t s)).1
      (batemanPairAt t (batemanRay t s)).2 = 0 := by
    rw [batemanPairAt_batemanRay]
    exact hs
  have hne := rationalPowerFactor_ne_zero_on_locus hp hq r.1 r.2.1 r.2.2 t hr
  dsimp only
  rw [poyntingPowerFlow_eq _ _ _ _ _ _ hne]
  exact batemanRay_hasDerivAt t s

end Qatlib.Papers.KnotLight13.TorusFamily
