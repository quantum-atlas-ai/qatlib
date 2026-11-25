/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Papers.KnotLight13.TorusFamily.RationalLineGeometry
public import Qatlib.Papers.KnotLight13.TorusFamily.RationalPower
public import Qatlib.Papers.KnotLight13.TorusFamily.BatemanTimeSlices

/-!
# Field-line first integrals for the powered Bateman pair

[Kedia2013TyingKnots], page 150404-2, uses the real and imaginary parts
of the product of the powered pair as field-line labels.
The two summands of the product gradient have separately real
conjugate contractions with the original Riemann–Silberstein field.
-/

@[expose] public section
set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace Qatlib.Papers.KnotLight13.TorusFamily

open Qatlib.Papers.KnotLight13.TorusFamily (radialAux rationalAlpha rationalBeta
  pairDenominator)
open Qatlib.Papers.KnottedLight08.HopfField (cross3 dot3)
open scoped ComplexConjugate

/-- The first summand of the conjugate gradient has a real contraction.
Clearing the common denominator reduces its imaginary part to a polynomial. -/
private theorem beta_alpha_numerator_im_zero (x y z t : ℝ) :
    (dot3 (cross3 (alphaGradientNumerators x y z t) (betaGradientNumerators x y z t))
        (fun j => conj (betaNumerator x y * alphaGradientNumerators x y z t j)) *
      conj (complexDenominator x y z t)).im = 0 := by
  change (((alphaYNumerator x y z t * betaZNumerator x y z t -
      alphaZNumerator x y z t * betaYNumerator x y z t) *
      conj (betaNumerator x y * alphaXNumerator x y z t) +
      (alphaZNumerator x y z t * betaXNumerator x y z t -
        alphaXNumerator x y z t * betaZNumerator x y z t) *
      conj (betaNumerator x y * alphaYNumerator x y z t) +
      (alphaXNumerator x y z t * betaYNumerator x y z t -
        alphaYNumerator x y z t * betaXNumerator x y z t) *
      conj (betaNumerator x y * alphaZNumerator x y z t)) *
      conj (complexDenominator x y z t)).im = 0
  simp only [star_add, star_sub, star_mul, Complex.conj_ofReal, Complex.conj_I,
    star_one, star_two, star_four,
    alphaXNumerator, alphaYNumerator, alphaZNumerator,
    betaXNumerator, betaYNumerator, betaZNumerator,
    betaNumerator, betaReducedNumerator, alphaCommonFactor, complexDenominator, radialAux,
    Complex.add_re, Complex.add_im, Complex.sub_re, Complex.sub_im, Complex.mul_re,
    Complex.mul_im, Complex.neg_re, Complex.neg_im, Complex.ofReal_re, Complex.ofReal_im,
    Complex.I_re, Complex.I_im, show (1 : ℂ).re = 1 from rfl, show (1 : ℂ).im = 0 from rfl,
    show (2 : ℂ).re = 2 from rfl, show (2 : ℂ).im = 0 from rfl,
    show (4 : ℂ).re = 4 from rfl, show (4 : ℂ).im = 0 from rfl]
  ring

/-- Multiplying the alpha gradient by beta gives a separately real
conjugate contraction with the physical field. -/
theorem field_dot_conj_beta_alphaGradient_im_zero (x y z t : ℝ) :
    (dot3 (rationalField x y z t)
      (fun j => conj (rationalBeta x y z t * alphaGradient x y z t j))).im = 0 := by
  let w := complexDenominator x y z t
  have hw : w ≠ 0 := complex_denominator_ne_zero _ _ _ _
  let Z := dot3 (cross3 (alphaGradientNumerators x y z t) (betaGradientNumerators x y z t))
    (fun j => conj (betaNumerator x y * alphaGradientNumerators x y z t j))
  have h (j : Fin 3) :
      rationalBeta x y z t * alphaGradient x y z t j =
        (betaNumerator x y * alphaGradientNumerators x y z t j) / w ^ 3 := by
    simp only [rationalBeta_eq, alphaGradient, div_mul_div_comm]
    congr 1
    dsimp only [w]
    ring
  have hZ : dot3 (rationalField x y z t)
      (fun j => conj (rationalBeta x y z t * alphaGradient x y z t j)) =
      Z / (w ^ 4 * conj (w ^ 3)) := by
    simp only [dot3, rationalField_eq_cross_div, h, star_div, Z, w,
      div_mul_div_comm, ← add_div]
  rw [hZ]
  have hswap : Z / (w ^ 4 * conj (w ^ 3)) =
      Z * conj w / ((pairDenominator x y z t ^ 4 : ℝ) : ℂ) := by
    rw [show ((pairDenominator x y z t ^ 4 : ℝ) : ℂ) = w ^ 4 * conj (w ^ 4) from
      (complexDenominator_pow_mul_conj _ _ _ _ 4).symm]
    rw [pow_succ (a := w) 3, star_mul]
    have hc : conj w ≠ 0 := star_ne_zero.2 hw
    field_simp [hw, hc]
  rw [hswap, Complex.div_ofReal_im, beta_alpha_numerator_im_zero, zero_div]

/-- The unpowered product gradient is the sum of the two weighted gradients. -/
private theorem productGradient_eq_weighted (x y z t : ℝ) (j : Fin 3) :
    productGradient x y z t j =
      rationalBeta x y z t * alphaGradient x y z t j +
        rationalAlpha x y z t * betaGradient x y z t j := by
  rw [productGradient, productGradientNumerators, rationalBeta_eq, alphaGradient, betaGradient,
    show rationalAlpha x y z t = alphaNumerator x y z t / complexDenominator x y z t from rfl]
  field_simp [complex_denominator_ne_zero x y z t]

/-- The other weighted gradient also has a real conjugate contraction. -/
theorem field_dot_conj_alpha_betaGradient_im_zero (x y z t : ℝ) :
    (dot3 (rationalField x y z t)
      (fun j => conj (rationalAlpha x y z t * betaGradient x y z t j))).im = 0 := by
  have h := congrArg Complex.im (field_dot_conj_productGradient x y z t)
  simp only [productGradient_eq_weighted, map_add, dot3_add_right, Complex.add_im,
    Complex.ofReal_im, field_dot_conj_beta_alphaGradient_im_zero, zero_add] at h
  exact h

/-- The complex first-integral label of the powered field. -/
noncomputable def poweredProductLabel (p q : ℕ) (x y z t : ℝ) : ℂ :=
  rationalAlpha x y z t ^ p * rationalBeta x y z t ^ q

/-- The product rule for the two actual powered spatial gradients. -/
noncomputable def poweredProductGradient (p q : ℕ) (x y z t : ℝ) : Fin 3 → ℂ :=
  fun j => rationalBeta x y z t ^ q * alphaPowerGradient p x y z t j +
    rationalAlpha x y z t ^ p * betaPowerGradient q x y z t j

/-- The product-rule vector consists of the three spatial derivatives of
the physical complex label. -/
theorem poweredProductGradient_eq_deriv (p q : ℕ) (x y z t : ℝ) :
    poweredProductGradient p q x y z t =
      ![deriv (fun a => poweredProductLabel p q a y z t) x,
        deriv (fun a => poweredProductLabel p q x a z t) y,
        deriv (fun a => poweredProductLabel p q x y a t) z] := by
  open Qatlib.Papers.KnotLight13.Bateman (power_derivative) in
  have hmul {a b : ℝ → ℂ} {da db : ℂ} {s : ℝ}
      (ha : HasDerivAt a da s) (hb : HasDerivAt b db s) :
      b s ^ q * deriv (fun x => a x ^ p) s + a s ^ p * deriv (fun x => b x ^ q) s =
        deriv (fun x => a x ^ p * b x ^ q) s := by
    have h₁ := power_derivative a da s p ha
    have h₂ := power_derivative b db s q hb
    have hab := (h₁.mul h₂).deriv
    change deriv (fun x => a x ^ p * b x ^ q) s = _ at hab
    rw [h₁.deriv, h₂.deriv, hab]
    ring
  funext j
  fin_cases j
  · exact hmul (hasDerivAt_rationalAlpha_x x y z t) (hasDerivAt_rationalBeta_x x y z t)
  · exact hmul (hasDerivAt_rationalAlpha_y x y z t) (hasDerivAt_rationalBeta_y x y z t)
  · exact hmul (hasDerivAt_rationalAlpha_z x y z t) (hasDerivAt_rationalBeta_z x y z t)

/-- The bilinear contraction of the physical powered field with the
label gradient vanishes by cross-product orthogonality. -/
private theorem poweredField_dot_gradient (p q : ℕ) (x y z t : ℝ) :
    dot3 (rationalPowerField p q x y z t) (poweredProductGradient p q x y z t) = 0 := by
  unfold rationalPowerField poweredProductGradient
  simp only [dot3_add_right, dot3_smul_right,
    cross3_dot3_left, cross3_dot3_right, mul_zero, add_zero]

/-- Complex bilinearity of the field contraction in its first argument. -/
private theorem dot3_smul_field (m : ℂ) (u v : Fin 3 → ℂ) :
    dot3 (fun j => m * u j) v = m * dot3 u v := by
  unfold dot3
  ring

/-- The Hermitian contraction of the physical field with the complex
label gradient is real for every pair of powers. -/
theorem poweredField_dot_conj_gradient_im_zero (p q : ℕ) (x y z t : ℝ) :
    (dot3 (rationalPowerField p q x y z t)
      (fun j => conj (poweredProductGradient p q x y z t j))).im = 0 := by
  cases p with
  | zero => simp [rationalPowerField_eq, rationalPowerFactor, dot3]
  | succ p =>
    cases q with
    | zero => simp [rationalPowerField_eq, rationalPowerFactor, dot3]
    | succ q =>
      let α := rationalAlpha x y z t
      let β := rationalBeta x y z t
      let m := α ^ p * β ^ q
      let a : ℂ := (p + 1 : ℕ)
      let b : ℂ := (q + 1 : ℕ)
      let F := rationalField x y z t
      let U := fun j => β * alphaGradient x y z t j
      let V := fun j => α * betaGradient x y z t j
      have hF : rationalPowerField (p + 1) (q + 1) x y z t =
          fun j => a * b * m * F j := by
        rw [rationalPowerField_eq]
        funext j
        simp only [rationalPowerFactor, Nat.add_sub_cancel]
        change a * α ^ p * (b * β ^ q) * F j = _
        unfold m
        ring
      have hG : poweredProductGradient (p + 1) (q + 1) x y z t =
          fun j => m * (a * U j + b * V j) := by
        funext j
        unfold poweredProductGradient
        rw [alphaPowerGradient_eq, betaPowerGradient_eq]
        simp only [Nat.add_sub_cancel]
        change β ^ (q + 1) * (a * α ^ p * alphaGradient x y z t j) +
          α ^ (p + 1) * (b * β ^ q * betaGradient x y z t j) = _
        simp only [pow_succ, m, U, V]
        ring
      have hU : (dot3 F (fun j => conj (U j))).im = 0 :=
        field_dot_conj_beta_alphaGradient_im_zero x y z t
      have hV : (dot3 F (fun j => conj (V j))).im = 0 :=
        field_dot_conj_alpha_betaGradient_im_zero x y z t
      have ha : conj a = a := map_natCast _ _
      have hb : conj b = b := map_natCast _ _
      rw [hF, hG]
      simp only [map_mul, map_add, ha, hb, dot3_smul_field, dot3_add_right, dot3_smul_right]
      rw [show conj m *
          (a * (a * b * m * dot3 F (fun j => conj (U j))) +
            b * (a * b * m * dot3 F (fun j => conj (V j)))) =
          (a * b * (m * conj m)) *
          (a * dot3 F (fun j => conj (U j)) + b * dot3 F (fun j => conj (V j))) by ring,
        Complex.mul_conj]
      simp only [a, b, Complex.mul_im, Complex.add_im, Complex.natCast_re, Complex.natCast_im,
        Complex.ofReal_im, Complex.ofReal_re, hU, hV, mul_zero, zero_mul, add_zero]

/-- For all powers and every real time, the magnetic field is tangent
to the levels of the real label and the electric field to the levels
of its imaginary part, in the pointwise gradient sense. -/
theorem powered_field_line_levels (p q : ℕ) (x y z t : ℝ) :
    dot3 (fun j => (rationalPowerField p q x y z t j).im)
        (fun j => (poweredProductGradient p q x y z t j).re) = 0 ∧
      dot3 (fun j => (rationalPowerField p q x y z t j).re)
        (fun j => (poweredProductGradient p q x y z t j).im) = 0 := by
  let F := rationalPowerField p q x y z t
  let G := poweredProductGradient p q x y z t
  have h₁ := dot3_im F G
  have h₂ := dot3_conj_im F G
  have h₃ : (dot3 F G).im = 0 := by
    change (dot3 (rationalPowerField p q x y z t) (poweredProductGradient p q x y z t)).im = 0
    rw [poweredField_dot_gradient, Complex.zero_im]
  have h₄ : (dot3 F (fun j => conj (G j))).im = 0 :=
    poweredField_dot_conj_gradient_im_zero p q x y z t
  change dot3 (fun j => (F j).im) (fun j => (G j).re) = 0 ∧
    dot3 (fun j => (F j).re) (fun j => (G j).im) = 0
  constructor <;> linarith

/-- The physical ray map transports the full complex label from the
initial slice. In particular it transports both level surfaces. -/
theorem poweredProductLabel_batemanRay (p q : ℕ) (t : ℝ) (s : ℝ × ℝ × ℝ) :
    let r := batemanRay t s
    poweredProductLabel p q r.1 r.2.1 r.2.2 t = poweredProductLabel p q s.1 s.2.1 s.2.2 0 := by
  let r := batemanRay t s
  have h := batemanPairAt_batemanRay t s
  change (rationalAlpha r.1 r.2.1 r.2.2 t, rationalBeta r.1 r.2.1 r.2.2 t) =
    (rationalAlpha s.1 s.2.1 s.2.2 0, rationalBeta s.1 s.2.1 s.2.2 0) at h
  exact congrArg (fun z : ℂ × ℂ => z.1 ^ p * z.2 ^ q) h

end Qatlib.Papers.KnotLight13.TorusFamily
