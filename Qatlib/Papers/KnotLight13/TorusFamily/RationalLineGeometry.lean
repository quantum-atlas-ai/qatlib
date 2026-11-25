/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Papers.KnotLight13.TorusFamily.RationalRegularity
public import Mathlib.Analysis.Calculus.Deriv.Mul

/-!
# Field-line geometry of the rational Bateman field

[Kedia2013TyingKnots], p150404-3 (field lines on level surfaces),
[DOI](https://doi.org/10.1103/physrevlett.111.150404).
For the base pair of the paper's construction, the magnetic field lines lie
on the level surfaces of `Re (α * β)` and the electric field lines lie on the
level surfaces of `Im (α * β)`. This module proves the analytic content of
that statement for the explicit rational pair: with `F = ∇α × ∇β` the actual
Riemann–Silberstein field and `∇(α * β)` the actual spatial gradient of the
product (both identified through `HasDerivAt` derivative bridges), the
orthogonality relations `Im F · ∇Re(αβ) = 0` and `Re F · ∇Im(αβ) = 0` hold at
every space-time point.

The proof has two legs. First, `dot3 (∇α × ∇β) (∇(αβ)) = 0` exactly, because
the cross product is perpendicular to its factors and the gradient of the
product is `β ∇α + α ∇β`. Second, the scaled reality identity
`dot3 U (conj W) = w * R` with `U` the cross-numerator vector, `W` the
product-gradient numerator, `w` the common denominator and `R` an explicit
real polynomial; it implies that `dot3 F (conj ∇(αβ))` is real. The two legs
combine linearly into both orthogonality relations. No torus-knot structure
of the core curves, no periodicity statement, and no `(p, q)` power family is
claimed here.
-/

@[expose] public section
set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace Qatlib.Papers.KnotLight13.TorusFamily

open Qatlib.Papers.KnotLight13.TorusFamily (radialAux rationalAlpha rationalBeta
  pairDenominator pair_denominator_pos)
open Qatlib.Papers.KnottedLight08.HopfField (cross3 dot3)

/-! ### Algebraic preliminaries -/

/-- The oriented cross product is perpendicular to its first factor. -/
theorem cross3_dot3_left (u v : Fin 3 → ℂ) : dot3 (cross3 u v) u = 0 := by
  show (u 1 * v 2 - u 2 * v 1) * u 0 + (u 2 * v 0 - u 0 * v 2) * u 1 +
      (u 0 * v 1 - u 1 * v 0) * u 2 = 0
  ring

/-- The oriented cross product is perpendicular to its second factor. -/
theorem cross3_dot3_right (u v : Fin 3 → ℂ) : dot3 (cross3 u v) v = 0 := by
  show (u 1 * v 2 - u 2 * v 1) * v 0 + (u 2 * v 0 - u 0 * v 2) * v 1 +
      (u 0 * v 1 - u 1 * v 0) * v 2 = 0
  ring

/-- Bilinearity of the dot product in the second argument, additive form. -/
theorem dot3_add_right (a b c : Fin 3 → ℂ) :
    dot3 a (fun j => b j + c j) = dot3 a b + dot3 a c := by
  simp only [dot3]
  ring

/-- Bilinearity of the dot product in the second argument, scalar form. -/
theorem dot3_smul_right (k : ℂ) (a b : Fin 3 → ℂ) :
    dot3 a (fun j => k * b j) = k * dot3 a b := by
  simp only [dot3]
  ring

/-- Imaginary part of a dot product against a conjugated vector. -/
theorem dot3_conj_im (a b : Fin 3 → ℂ) :
    (dot3 a (fun j => (starRingEnd ℂ) (b j))).im =
      dot3 (fun j => (a j).im) (fun j => (b j).re) -
      dot3 (fun j => (a j).re) (fun j => (b j).im) := by
  show ((a 0) * (starRingEnd ℂ) (b 0)).im + ((a 1) * (starRingEnd ℂ) (b 1)).im +
      ((a 2) * (starRingEnd ℂ) (b 2)).im =
    ((a 0).im * (b 0).re + (a 1).im * (b 1).re + (a 2).im * (b 2).re) -
      ((a 0).re * (b 0).im + (a 1).re * (b 1).im + (a 2).re * (b 2).im)
  rw [Complex.mul_im, Complex.mul_im, Complex.mul_im,
    Complex.conj_re, Complex.conj_im, Complex.conj_re, Complex.conj_im,
    Complex.conj_re, Complex.conj_im]
  ring

/-- Imaginary part of a plain dot product. -/
theorem dot3_im (a b : Fin 3 → ℂ) :
    (dot3 a b).im =
      dot3 (fun j => (a j).im) (fun j => (b j).re) +
      dot3 (fun j => (a j).re) (fun j => (b j).im) := by
  show ((a 0) * (b 0)).im + ((a 1) * (b 1)).im + ((a 2) * (b 2)).im =
    ((a 0).im * (b 0).re + (a 1).im * (b 1).re + (a 2).im * (b 2).re) +
      ((a 0).re * (b 0).im + (a 1).re * (b 1).im + (a 2).re * (b 2).im)
  rw [Complex.mul_im, Complex.mul_im, Complex.mul_im]
  ring

/-- Complex conjugation, as the standard ring endomorphism, preserves
division. -/
theorem star_div (a b : ℂ) :
    (starRingEnd ℂ) (a / b) = (starRingEnd ℂ) a / (starRingEnd ℂ) b :=
  map_div₀ _ _ _

/-- Complex conjugation, as the standard ring endomorphism, preserves
powers. -/
theorem star_pow (z : ℂ) (n : ℕ) :
    (starRingEnd ℂ) (z ^ n) = ((starRingEnd ℂ) z) ^ n :=
  map_pow _ _ _

/-- Complex conjugation, as the standard ring endomorphism, is additive. -/
theorem star_add (a b : ℂ) :
    (starRingEnd ℂ) (a + b) = (starRingEnd ℂ) a + (starRingEnd ℂ) b :=
  map_add _ _ _

/-- Complex conjugation, as the standard ring endomorphism, subtracts. -/
theorem star_sub (a b : ℂ) :
    (starRingEnd ℂ) (a - b) = (starRingEnd ℂ) a - (starRingEnd ℂ) b :=
  map_sub _ _ _

/-- Complex conjugation, as the standard ring endomorphism, is odd. -/
theorem star_neg (a : ℂ) :
    (starRingEnd ℂ) (-a) = -((starRingEnd ℂ) a) :=
  map_neg _ _

/-- Complex conjugation, as the standard ring endomorphism, is
multiplicative. -/
theorem star_mul (a b : ℂ) :
    (starRingEnd ℂ) (a * b) = (starRingEnd ℂ) a * (starRingEnd ℂ) b :=
  map_mul _ _ _

/-- Complex conjugation, as the standard ring endomorphism, fixes one. -/
theorem star_one : (starRingEnd ℂ) (1 : ℂ) = 1 := map_one _

/-- Complex conjugation, as the standard ring endomorphism, fixes two. -/
theorem star_two : (starRingEnd ℂ) (2 : ℂ) = 2 := map_ofNat _ 2

/-- Complex conjugation, as the standard ring endomorphism, fixes four. -/
theorem star_four : (starRingEnd ℂ) (4 : ℂ) = 4 := map_ofNat _ 4

/-- Real part of a product with a conjugated factor. -/
theorem mul_conj_re (z w : ℂ) :
    (z * (starRingEnd ℂ) w).re = z.re * w.re + z.im * w.im := by
  rw [Complex.mul_re, Complex.conj_re, Complex.conj_im]
  ring

/-- Imaginary part of a product with a conjugated factor. -/
theorem mul_conj_im (z w : ℂ) :
    (z * (starRingEnd ℂ) w).im = z.im * w.re - z.re * w.im := by
  rw [Complex.mul_im, Complex.conj_re, Complex.conj_im]
  ring

/-! ### The product gradient and its derivative bridges -/

/-- The full complex numerator of β, twice the reduced numerator. -/
noncomputable def betaNumerator (x y : ℝ) : ℂ := 2 * betaReducedNumerator x y

/-- The numerator of `w ^ 3 • ∇(α * β)`: the product rule combines
`β ∇α + α ∇β` over the common denominator `w ^ 3`. -/
noncomputable def productGradientNumerators (x y z t : ℝ) : Fin 3 → ℂ :=
  fun j => betaNumerator x y * alphaGradientNumerators x y z t j
    + alphaNumerator x y z t * betaGradientNumerators x y z t j

/-- The actual spatial gradient of the product `α * β`. -/
noncomputable def productGradient (x y z t : ℝ) : Fin 3 → ℂ :=
  fun j => productGradientNumerators x y z t j / complexDenominator x y z t ^ 3

/-- The β numerator bridge: the public rational β equals its full numerator
over the common denominator. -/
theorem rationalBeta_eq (x y z t : ℝ) :
    rationalBeta x y z t = betaNumerator x y / complexDenominator x y z t := by
  simp only [rationalBeta, betaNumerator, betaReducedNumerator, complexDenominator]
  push_cast
  ring

/-- The x-partial of the product `α * β` is its numerator over `w ^ 3`. -/
theorem hasDerivAt_rationalAB_x (x y z t : ℝ) :
    HasDerivAt (fun x' => rationalAlpha x' y z t * rationalBeta x' y z t)
      (productGradientNumerators x y z t 0 / complexDenominator x y z t ^ 3) x := by
  have h := (hasDerivAt_rationalAlpha_x x y z t).mul
    (hasDerivAt_rationalBeta_x x y z t)
  have hval : alphaGradient x y z t 0 * rationalBeta x y z t +
      rationalAlpha x y z t * betaGradient x y z t 0 =
      productGradientNumerators x y z t 0 / complexDenominator x y z t ^ 3 := by
    unfold alphaGradient betaGradient productGradientNumerators
    rw [rationalBeta_eq x y z t,
      show rationalAlpha x y z t = alphaNumerator x y z t / complexDenominator x y z t from rfl]
    have hw : complexDenominator x y z t ≠ 0 := complex_denominator_ne_zero x y z t
    field_simp
  rw [hval] at h
  exact h

/-- The y-partial of the product `α * β` is its numerator over `w ^ 3`. -/
theorem hasDerivAt_rationalAB_y (x y z t : ℝ) :
    HasDerivAt (fun y' => rationalAlpha x y' z t * rationalBeta x y' z t)
      (productGradientNumerators x y z t 1 / complexDenominator x y z t ^ 3) y := by
  have h := (hasDerivAt_rationalAlpha_y x y z t).mul
    (hasDerivAt_rationalBeta_y x y z t)
  have hval : alphaGradient x y z t 1 * rationalBeta x y z t +
      rationalAlpha x y z t * betaGradient x y z t 1 =
      productGradientNumerators x y z t 1 / complexDenominator x y z t ^ 3 := by
    unfold alphaGradient betaGradient productGradientNumerators
    rw [rationalBeta_eq x y z t,
      show rationalAlpha x y z t = alphaNumerator x y z t / complexDenominator x y z t from rfl]
    have hw : complexDenominator x y z t ≠ 0 := complex_denominator_ne_zero x y z t
    field_simp
  rw [hval] at h
  exact h

/-- The z-partial of the product `α * β` is its numerator over `w ^ 3`. -/
theorem hasDerivAt_rationalAB_z (x y z t : ℝ) :
    HasDerivAt (fun z' => rationalAlpha x y z' t * rationalBeta x y z' t)
      (productGradientNumerators x y z t 2 / complexDenominator x y z t ^ 3) z := by
  have h := (hasDerivAt_rationalAlpha_z x y z t).mul
    (hasDerivAt_rationalBeta_z x y z t)
  have hval : alphaGradient x y z t 2 * rationalBeta x y z t +
      rationalAlpha x y z t * betaGradient x y z t 2 =
      productGradientNumerators x y z t 2 / complexDenominator x y z t ^ 3 := by
    unfold alphaGradient betaGradient productGradientNumerators
    rw [rationalBeta_eq x y z t,
      show rationalAlpha x y z t = alphaNumerator x y z t / complexDenominator x y z t from rfl]
    have hw : complexDenominator x y z t ≠ 0 := complex_denominator_ne_zero x y z t
    field_simp
  rw [hval] at h
  exact h

/-! ### First leg: orthogonality to the product gradient -/

/-- First leg, numerator form: the cross-numerator vector is orthogonal to
the product-gradient numerator, exactly, because the cross product is
perpendicular to both of its factors. -/
theorem dot3_cross_productGradientNumerators (x y z t : ℝ) :
    dot3 (cross3 (alphaGradientNumerators x y z t)
        (betaGradientNumerators x y z t)) (productGradientNumerators x y z t) = 0 := by
  have e1 := cross3_dot3_left (alphaGradientNumerators x y z t)
    (betaGradientNumerators x y z t)
  have e2 := cross3_dot3_right (alphaGradientNumerators x y z t)
    (betaGradientNumerators x y z t)
  show dot3 (cross3 (alphaGradientNumerators x y z t)
      (betaGradientNumerators x y z t))
      (fun j => betaNumerator x y * alphaGradientNumerators x y z t j +
        alphaNumerator x y z t * betaGradientNumerators x y z t j) = 0
  rw [dot3_add_right, dot3_smul_right, dot3_smul_right, e1, e2]
  ring

/-- The dot product of the field with the product gradient is the scaled dot
product of the numerators over `w ^ 7`. -/
theorem dot3_field_productGradient_scale (x y z t : ℝ) :
    dot3 (rationalField x y z t) (productGradient x y z t) =
      dot3 (cross3 (alphaGradientNumerators x y z t) (betaGradientNumerators x y z t))
        (productGradientNumerators x y z t) / complexDenominator x y z t ^ 7 := by
  simp only [dot3, rationalField_eq_cross_div, productGradient]
  rw [div_mul_div_comm, div_mul_div_comm, div_mul_div_comm,
    show complexDenominator x y z t ^ 4 * complexDenominator x y z t ^ 3 =
      complexDenominator x y z t ^ 7 from by rw [← pow_add],
    ← add_div, ← add_div]

/-- First leg: the field is orthogonal to the product gradient, exactly. -/
theorem field_dot_productGradient (x y z t : ℝ) :
    dot3 (rationalField x y z t) (productGradient x y z t) = 0 := by
  rw [dot3_field_productGradient_scale,
    dot3_cross_productGradientNumerators, zero_div]

/-! ### Second leg: the conjugate dot product is real -/

/-- The real profile polynomial through which the conjugate dot product
factors; found by exact polynomial division and verified coefficientwise. -/
noncomputable def lineGeometryProfile (x y z t : ℝ) : ℝ :=
  16 + (48 * t ^ 2 - 32 * z * t + 48 * z ^ 2 - 80 * x ^ 2 - 80 * y ^ 2)
    + (48 * t ^ 4 - 64 * z * t ^ 3 + 32 * z ^ 2 * t ^ 2 - 64 * z ^ 3 * t
      + 48 * z ^ 4 - 96 * x ^ 2 * t ^ 2 + 192 * x ^ 2 * z * t - 32 * x ^ 2 * z ^ 2
      - 96 * y ^ 2 * t ^ 2 + 192 * y ^ 2 * z * t - 32 * y ^ 2 * z ^ 2
      - 160 * x ^ 2 * y ^ 2 - 80 * x ^ 4 - 80 * y ^ 4)
    + (16 * t ^ 6 - 32 * z * t ^ 5 - 16 * z ^ 2 * t ^ 4 + 64 * z ^ 3 * t ^ 3
      - 16 * z ^ 4 * t ^ 2 - 32 * z ^ 5 * t + 16 * z ^ 6
      - 16 * x ^ 2 * t ^ 4 + 64 * x ^ 2 * z * t ^ 3 - 32 * x ^ 2 * z ^ 2 * t ^ 2
      - 64 * x ^ 2 * z ^ 3 * t + 48 * x ^ 2 * z ^ 4
      - 16 * y ^ 2 * t ^ 4 + 64 * y ^ 2 * z * t ^ 3 - 32 * y ^ 2 * z ^ 2 * t ^ 2
      - 64 * y ^ 2 * z ^ 3 * t + 48 * y ^ 2 * z ^ 4
      - 32 * x ^ 2 * y ^ 2 * t ^ 2 - 64 * x ^ 2 * y ^ 2 * z * t
      + 96 * x ^ 2 * y ^ 2 * z ^ 2 + 48 * x ^ 2 * y ^ 4 + 48 * x ^ 4 * y ^ 2
      - 16 * x ^ 4 * t ^ 2 - 32 * x ^ 4 * z * t + 48 * x ^ 4 * z ^ 2
      - 16 * y ^ 4 * t ^ 2 - 32 * y ^ 4 * z * t + 48 * y ^ 4 * z ^ 2
      + 16 * x ^ 6 + 16 * y ^ 6)

/-- Second leg, scaled form: the conjugate dot product of the cross-numerator
with the product-gradient numerator equals the denominator times a real
polynomial. -/
theorem dot3_cross_conj_productGradientNumerators (x y z t : ℝ) :
    dot3 (cross3 (alphaGradientNumerators x y z t) (betaGradientNumerators x y z t))
        (fun j => (starRingEnd ℂ) (productGradientNumerators x y z t j)) =
      complexDenominator x y z t * ((lineGeometryProfile x y z t : ℝ) : ℂ) := by
  have hre : Complex.re
      (dot3 (cross3 (alphaGradientNumerators x y z t) (betaGradientNumerators x y z t))
        (fun j => (starRingEnd ℂ) (productGradientNumerators x y z t j))) =
      Complex.re (complexDenominator x y z t * ((lineGeometryProfile x y z t : ℝ) : ℂ)) := by
    show Complex.re ((alphaYNumerator x y z t * betaZNumerator x y z t
          - alphaZNumerator x y z t * betaYNumerator x y z t)
        * (starRingEnd ℂ) (betaNumerator x y * alphaXNumerator x y z t
          + alphaNumerator x y z t * betaXNumerator x y z t)
      + (alphaZNumerator x y z t * betaXNumerator x y z t
          - alphaXNumerator x y z t * betaZNumerator x y z t)
        * (starRingEnd ℂ) (betaNumerator x y * alphaYNumerator x y z t
          + alphaNumerator x y z t * betaYNumerator x y z t)
      + (alphaXNumerator x y z t * betaYNumerator x y z t
          - alphaYNumerator x y z t * betaXNumerator x y z t)
        * (starRingEnd ℂ) (betaNumerator x y * alphaZNumerator x y z t
          + alphaNumerator x y z t * betaZNumerator x y z t))
      = Complex.re (complexDenominator x y z t * ((lineGeometryProfile x y z t : ℝ) : ℂ))
    simp only [star_add, star_sub, star_neg, star_mul, Complex.conj_ofReal,
      Complex.conj_I, star_one, star_two, star_four,
      alphaXNumerator, alphaYNumerator, alphaZNumerator,
      betaXNumerator, betaYNumerator, betaZNumerator, alphaNumerator, betaNumerator,
      betaReducedNumerator, alphaCommonFactor, complexDenominator, radialAux,
      lineGeometryProfile, Complex.add_re, Complex.add_im, Complex.sub_re,
      Complex.sub_im, Complex.neg_re, Complex.neg_im, Complex.mul_re,
      Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re,
      Complex.I_im, show (1 : ℂ).re = 1 from rfl, show (1 : ℂ).im = 0 from rfl,
      show (2 : ℂ).re = 2 from rfl, show (2 : ℂ).im = 0 from rfl,
      show (4 : ℂ).re = 4 from rfl, show (4 : ℂ).im = 0 from rfl]
    ring
  have him : Complex.im
      (dot3 (cross3 (alphaGradientNumerators x y z t) (betaGradientNumerators x y z t))
        (fun j => (starRingEnd ℂ) (productGradientNumerators x y z t j))) =
      Complex.im (complexDenominator x y z t * ((lineGeometryProfile x y z t : ℝ) : ℂ)) := by
    show Complex.im ((alphaYNumerator x y z t * betaZNumerator x y z t
          - alphaZNumerator x y z t * betaYNumerator x y z t)
        * (starRingEnd ℂ) (betaNumerator x y * alphaXNumerator x y z t
          + alphaNumerator x y z t * betaXNumerator x y z t)
      + (alphaZNumerator x y z t * betaXNumerator x y z t
          - alphaXNumerator x y z t * betaZNumerator x y z t)
        * (starRingEnd ℂ) (betaNumerator x y * alphaYNumerator x y z t
          + alphaNumerator x y z t * betaYNumerator x y z t)
      + (alphaXNumerator x y z t * betaYNumerator x y z t
          - alphaYNumerator x y z t * betaXNumerator x y z t)
        * (starRingEnd ℂ) (betaNumerator x y * alphaZNumerator x y z t
          + alphaNumerator x y z t * betaZNumerator x y z t))
      = Complex.im (complexDenominator x y z t * ((lineGeometryProfile x y z t : ℝ) : ℂ))
    simp only [star_add, star_sub, star_neg, star_mul, Complex.conj_ofReal,
      Complex.conj_I, star_one, star_two, star_four,
      alphaXNumerator, alphaYNumerator, alphaZNumerator,
      betaXNumerator, betaYNumerator, betaZNumerator, alphaNumerator, betaNumerator,
      betaReducedNumerator, alphaCommonFactor, complexDenominator, radialAux,
      lineGeometryProfile, Complex.add_re, Complex.add_im, Complex.sub_re,
      Complex.sub_im, Complex.neg_re, Complex.neg_im, Complex.mul_re,
      Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re,
      Complex.I_im, show (1 : ℂ).re = 1 from rfl, show (1 : ℂ).im = 0 from rfl,
      show (2 : ℂ).re = 2 from rfl, show (2 : ℂ).im = 0 from rfl,
      show (4 : ℂ).re = 4 from rfl, show (4 : ℂ).im = 0 from rfl]
    ring
  exact Complex.ext hre him

/-- The common denominator times its conjugate is the pair denominator. -/
theorem complexDenominator_mul_conj (x y z t : ℝ) :
    complexDenominator x y z t * (starRingEnd ℂ) (complexDenominator x y z t) =
      ((pairDenominator x y z t : ℝ) : ℂ) := by
  rw [Complex.ext_iff]
  constructor
  · simp only [complexDenominator, pairDenominator, radialAux, Complex.conj_re,
      Complex.conj_im, Complex.mul_re, Complex.add_re, Complex.add_im,
      Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re,
      Complex.I_im]
    ring
  · simp only [complexDenominator, pairDenominator, radialAux, Complex.conj_re,
      Complex.conj_im, Complex.mul_re, Complex.add_re, Complex.add_im,
      Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re,
      Complex.I_im]
    ring

/-- Any power of the common denominator times its conjugate is the same power
of the pair denominator. -/
theorem complexDenominator_pow_mul_conj (x y z t : ℝ) (n : ℕ) :
    complexDenominator x y z t ^ n * (starRingEnd ℂ) (complexDenominator x y z t ^ n) =
      ((pairDenominator x y z t ^ n : ℝ) : ℂ) := by
  rw [star_pow, ← mul_pow, complexDenominator_mul_conj, ← Complex.ofReal_pow]

/-- Second leg, scaled form: the conjugate dot product of the field with the
product gradient is the conjugate dot product of the numerators over the
mixed denominator `w ^ 4 * conj (w ^ 3)`. -/
theorem dot3_field_conj_productGradient_scale (x y z t : ℝ) :
    dot3 (rationalField x y z t)
        (fun j => (starRingEnd ℂ) (productGradient x y z t j)) =
      dot3 (cross3 (alphaGradientNumerators x y z t) (betaGradientNumerators x y z t))
        (fun j => (starRingEnd ℂ) (productGradientNumerators x y z t j)) /
        (complexDenominator x y z t ^ 4 * (starRingEnd ℂ) (complexDenominator x y z t ^ 3)) := by
  simp only [dot3, rationalField_eq_cross_div, productGradient, star_div]
  rw [div_mul_div_comm, div_mul_div_comm, div_mul_div_comm, ← add_div, ← add_div]

/-- Second leg: the dot product of the field with the conjugate product
gradient is real, namely the real profile over the cube of the pair
denominator. -/
theorem field_dot_conj_productGradient (x y z t : ℝ) :
    dot3 (rationalField x y z t)
        (fun j => (starRingEnd ℂ) (productGradient x y z t j)) =
      ((lineGeometryProfile x y z t / pairDenominator x y z t ^ 3 : ℝ) : ℂ) := by
  rw [dot3_field_conj_productGradient_scale,
    dot3_cross_conj_productGradientNumerators, Complex.ofReal_div,
    show complexDenominator x y z t ^ 4 * (starRingEnd ℂ) (complexDenominator x y z t ^ 3) =
      complexDenominator x y z t * ((pairDenominator x y z t ^ 3 : ℝ) : ℂ) from by
      rw [show complexDenominator x y z t ^ 4 *
          (starRingEnd ℂ) (complexDenominator x y z t ^ 3) =
          complexDenominator x y z t * (complexDenominator x y z t ^ 3 *
            (starRingEnd ℂ) (complexDenominator x y z t ^ 3)) from by
          rw [show complexDenominator x y z t ^ 4 =
              complexDenominator x y z t * complexDenominator x y z t ^ 3 from by
              rw [mul_comm, ← pow_succ],
            mul_assoc],
        complexDenominator_pow_mul_conj]]
  have hwne : complexDenominator x y z t ≠ 0 := complex_denominator_ne_zero x y z t
  field_simp

/-! ### The field-line level-surface theorems -/

/-- The magnetic part of the field is orthogonal to the gradient of the real
part of `α * β`: magnetic field lines lie on its level surfaces. -/
theorem magnetic_field_line_level (x y z t : ℝ) :
    dot3 (fun j => (rationalField x y z t j).im)
        (fun j => (productGradient x y z t j).re) = 0 := by
  have h1 := dot3_im (rationalField x y z t) (productGradient x y z t)
  have h2 := dot3_conj_im (rationalField x y z t) (productGradient x y z t)
  have e1 : (dot3 (rationalField x y z t) (productGradient x y z t)).im = 0 := by
    rw [field_dot_productGradient x y z t]
    rfl
  have e2 : (dot3 (rationalField x y z t)
      (fun j => (starRingEnd ℂ) (productGradient x y z t j))).im = 0 := by
    rw [field_dot_conj_productGradient x y z t]
    exact Complex.ofReal_im _
  linarith [h1, h2, e1, e2]

/-- The electric part of the field is orthogonal to the gradient of the
imaginary part of `α * β`: electric field lines lie on its level surfaces. -/
theorem electric_field_line_level (x y z t : ℝ) :
    dot3 (fun j => (rationalField x y z t j).re)
        (fun j => (productGradient x y z t j).im) = 0 := by
  have h1 := dot3_im (rationalField x y z t) (productGradient x y z t)
  have h2 := dot3_conj_im (rationalField x y z t) (productGradient x y z t)
  have e1 : (dot3 (rationalField x y z t) (productGradient x y z t)).im = 0 := by
    rw [field_dot_productGradient x y z t]
    rfl
  have e2 : (dot3 (rationalField x y z t)
      (fun j => (starRingEnd ℂ) (productGradient x y z t j))).im = 0 := by
    rw [field_dot_conj_productGradient x y z t]
    exact Complex.ofReal_im _
  linarith [h1, h2, e1, e2]
