/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Papers.KnotLight13.TorusFamily.PolynomialFamily
public import Qatlib.Papers.KnotLight13.Bateman.Construction
public import Qatlib.Papers.KnottedLight08.HopfField.NullAlgebra
public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.Analysis.Calculus.Deriv.Add
public import Mathlib.Analysis.Calculus.Deriv.Mul
public import Mathlib.Analysis.Calculus.Deriv.Inv
public import Mathlib.Analysis.Calculus.Deriv.Pow
public import Mathlib.Analysis.Complex.RealDeriv

/-!
# Actual spacetime partials and Bateman compatibility of the rational pair

[Kedia2013TyingKnots], equations (2) and (5),
[DOI](https://doi.org/10.1103/PhysRevLett.111.150404).
The published rational scalars `rationalAlpha`/`rationalBeta` share the complex
denominator `w = A + 2it`, where `A` is the auxiliary radius `radialAux`.
This module identifies the polynomial numerators of `w ^ 2 * ∂α` and
`w ^ 2 * ∂β` with the actual partial derivatives of the rational scalars in all
four spacetime coordinates, and proves that the true spatial gradients and time
partials satisfy the Bateman compatibility relation of equation (2) in all three
components. Consequently the actual Riemann–Silberstein field `∇α × ∇β` is
algebraically null, with perpendicular real electric and magnetic parts of equal
squared magnitude, by the public lemmas
`Qatlib.Papers.KnotLight13.Bateman.bateman_null` and
`Qatlib.Papers.KnotLight13.Bateman.bateman_real_invariants`.
The `t = 0` specialization of the pair to the standard stereographic coordinates
on the unit three-sphere is recorded as well. No Maxwell equation, field-line
geometry, energy integral, or topological statement is claimed here.
-/

@[expose] public section
set_option autoImplicit false

namespace Qatlib.Papers.KnotLight13.TorusFamily

open Qatlib.Papers.KnotLight13.TorusFamily (radialAux rationalAlpha rationalBeta
  pairDenominator pair_denominator_pos)
open Qatlib.Papers.KnotLight13.Bateman (bateman_null bateman_real_invariants)
open Qatlib.Papers.KnottedLight08.HopfField (cross3 dot3 squaredLength)

/-! ### The common denominator and the polynomial numerators -/

/-- The complex denominator `w = A + 2it` shared by both rational scalars. -/
noncomputable def complexDenominator (x y z t : ℝ) : ℂ :=
  (radialAux x y z t : ℝ) + Complex.I * (2 * t : ℝ)

/-- The common factor `g = 1 + i(t − z)`; the denominator minus the α numerator is `2g`. -/
noncomputable def alphaCommonFactor (z t : ℝ) : ℂ := 1 + Complex.I * ((t - z : ℝ))

/-- The complex numerator of α, exactly as it appears in `rationalAlpha`. -/
noncomputable def alphaNumerator (x y z t : ℝ) : ℂ :=
  ((radialAux x y z t - 2 : ℝ)) + Complex.I * (2 * z : ℝ)

/-- The reduced numerator `x − iy` of β; its full numerator is twice this. -/
noncomputable def betaReducedNumerator (x y : ℝ) : ℂ :=
  (x : ℂ) - Complex.I * (y : ℝ)

/-- Numerator of `w²·∂ₓα` for the rational pair. -/
noncomputable def alphaXNumerator (x _y z t : ℝ) : ℂ :=
  4 * (x : ℂ) * alphaCommonFactor z t

/-- Numerator of `w²·∂_yα` for the rational pair. -/
noncomputable def alphaYNumerator (_x y z t : ℝ) : ℂ :=
  4 * (y : ℂ) * alphaCommonFactor z t

/-- Numerator of `w²·∂_zα` for the rational pair. -/
noncomputable def alphaZNumerator (x y z t : ℝ) : ℂ :=
  4 * (z : ℂ) * alphaCommonFactor z t
    + 2 * Complex.I * complexDenominator x y z t

/-- Numerator of `w²·∂_tα` for the rational pair. -/
noncomputable def alphaTNumerator (x y z t : ℝ) : ℂ :=
  -(4 * (t : ℂ) * alphaCommonFactor z t)
    - 2 * Complex.I * alphaNumerator x y z t

/-- Numerator of `w²·∂ₓβ` for the rational pair. -/
noncomputable def betaXNumerator (x y z t : ℝ) : ℂ :=
  2 * complexDenominator x y z t
    - 4 * (x : ℂ) * betaReducedNumerator x y

/-- Numerator of `w²·∂_yβ` for the rational pair. -/
noncomputable def betaYNumerator (x y z t : ℝ) : ℂ :=
  -(2 * Complex.I * complexDenominator x y z t)
    - 4 * (y : ℂ) * betaReducedNumerator x y

/-- Numerator of `w²·∂_zβ` for the rational pair. -/
noncomputable def betaZNumerator (x y z _t : ℝ) : ℂ :=
  -(4 * (z : ℂ) * betaReducedNumerator x y)

/-- Numerator of `w²·∂_tβ` for the rational pair. -/
noncomputable def betaTNumerator (x y _z t : ℝ) : ℂ :=
  4 * ((t : ℂ) - Complex.I) * betaReducedNumerator x y

/-- The spatial gradient of α scaled by `w²`, as an explicit complex 3-vector. -/
noncomputable def alphaGradientNumerators (x y z t : ℝ) : Fin 3 → ℂ :=
  ![alphaXNumerator x y z t, alphaYNumerator x y z t, alphaZNumerator x y z t]

/-- The spatial gradient of β scaled by `w²`, as an explicit complex 3-vector. -/
noncomputable def betaGradientNumerators (x y z t : ℝ) : Fin 3 → ℂ :=
  ![betaXNumerator x y z t, betaYNumerator x y z t, betaZNumerator x y z t]

/-- The actual spatial gradient of α, that is, its numerator vector over `w²`. -/
noncomputable def alphaGradient (x y z t : ℝ) : Fin 3 → ℂ :=
  fun j => alphaGradientNumerators x y z t j / complexDenominator x y z t ^ 2

/-- The actual spatial gradient of β, that is, its numerator vector over `w²`. -/
noncomputable def betaGradient (x y z t : ℝ) : Fin 3 → ℂ :=
  fun j => betaGradientNumerators x y z t j / complexDenominator x y z t ^ 2

/-- The actual time partial of α, that is, its numerator over `w²`. -/
noncomputable def alphaTimePartial (x y z t : ℝ) : ℂ :=
  alphaTNumerator x y z t / complexDenominator x y z t ^ 2

/-- The actual time partial of β, that is, its numerator over `w²`. -/
noncomputable def betaTimePartial (x y z t : ℝ) : ℂ :=
  betaTNumerator x y z t / complexDenominator x y z t ^ 2

/-- The Bateman field `F = ∇α × ∇β` of the rational pair. -/
noncomputable def rationalField (x y z t : ℝ) : Fin 3 → ℂ :=
  cross3 (alphaGradient x y z t) (betaGradient x y z t)

/-- The complex denominator of the pair never vanishes in real space-time. -/
theorem complex_denominator_ne_zero (x y z t : ℝ) :
    complexDenominator x y z t ≠ 0 := by
  intro h
  have hn : Complex.normSq (complexDenominator x y z t) = 0 := by
    rw [h, Complex.normSq_zero]
  rw [show Complex.normSq (complexDenominator x y z t) = pairDenominator x y z t from by
      simp [complexDenominator, pairDenominator, Complex.normSq_apply]; ring] at hn
  exact (ne_of_gt (pair_denominator_pos x y z t)) hn

/-! ### A thin layer of lambda-form derivative combinators -/

/-- The real-to-complex coercion has complex derivative one everywhere. -/
theorem hasDerivAt_complex_ofReal (v : ℝ) :
    HasDerivAt (fun s : ℝ => (s : ℂ)) 1 v :=
  (hasDerivAt_id v).ofReal_comp

/-- A real differentiable section followed by the coercion stays differentiable. -/
theorem hasDerivAt_complex_ofReal_comp {f : ℝ → ℝ} {f' : ℝ} {v : ℝ}
    (h : HasDerivAt f f' v) :
    HasDerivAt (fun s : ℝ => ((f s : ℝ) : ℂ)) ((f' : ℝ) : ℂ) v :=
  h.ofReal_comp

/-- The square section has derivative twice the base point. -/
theorem hasDerivAt_sq (v : ℝ) : HasDerivAt (fun s : ℝ => s ^ 2) (2 * v) v :=
  ((hasDerivAt_id v).pow 2).congr_deriv (by simp)

/-- Doubling a real section has derivative two. -/
theorem hasDerivAt_two_mul_real (v : ℝ) : HasDerivAt (fun s : ℝ => 2 * s) (2 : ℝ) v :=
  (HasDerivAt.mul (hasDerivAt_const v 2) (hasDerivAt_id v)).congr_deriv (by ring)

/-- A constant real section has derivative zero. -/
theorem hasDerivAt_const_real (c v : ℝ) : HasDerivAt (fun _ : ℝ => c) 0 v :=
  hasDerivAt_const v c

/-- Adding a real constant to a real section preserves the derivative. -/
theorem hasDerivAt_add_const_real {f : ℝ → ℝ} {f' c v : ℝ} (h : HasDerivAt f f' v) :
    HasDerivAt (fun s => f s + c) f' v := by
  refine ((h.add (hasDerivAt_const v c)).congr_of_eventuallyEq ?_).congr_deriv (by ring)
  filter_upwards with s
  rfl

/-- Subtracting a real constant from a real section preserves the derivative. -/
theorem hasDerivAt_sub_const_real {f : ℝ → ℝ} {f' v : ℝ} (h : HasDerivAt f f' v) (c : ℝ) :
    HasDerivAt (fun s => f s - c) f' v := by
  refine ((h.sub (hasDerivAt_const v c)).congr_of_eventuallyEq ?_).congr_deriv (by ring)
  filter_upwards with s
  rfl

/-- Adding a real constant in front of a real section preserves the derivative. -/
theorem hasDerivAt_const_add_real (c : ℝ) {f : ℝ → ℝ} {f' v : ℝ} (h : HasDerivAt f f' v) :
    HasDerivAt (fun s => c + f s) f' v := by
  refine (((hasDerivAt_const v c).add h).congr_of_eventuallyEq ?_).congr_deriv (by ring)
  filter_upwards with s
  rfl

/-- Negating a real section negates the derivative. -/
theorem hasDerivAt_neg_real {f : ℝ → ℝ} {f' v : ℝ} (h : HasDerivAt f f' v) :
    HasDerivAt (fun s => -(f s)) (-f') v :=
  h.neg

/-- A constant complex section has derivative zero. -/
theorem hasDerivAt_const_complex (c : ℂ) (v : ℝ) : HasDerivAt (fun _ : ℝ => c) 0 v :=
  hasDerivAt_const v c

/-- The sum of complex sections has the sum of derivatives. -/
theorem hasDerivAt_add_complex {f g : ℝ → ℂ} {f' g' : ℂ} {v : ℝ}
    (h1 : HasDerivAt f f' v) (h2 : HasDerivAt g g' v) :
    HasDerivAt (fun s => f s + g s) (f' + g') v := h1.add h2

/-- The difference of complex sections has the difference of derivatives. -/
theorem hasDerivAt_sub_complex {f g : ℝ → ℂ} {f' g' : ℂ} {v : ℝ}
    (h1 : HasDerivAt f f' v) (h2 : HasDerivAt g g' v) :
    HasDerivAt (fun s => f s - g s) (f' - g') v := h1.sub h2

/-- Adding a complex constant to a complex section preserves the derivative. -/
theorem hasDerivAt_add_const_complex {f : ℝ → ℂ} {f' c : ℂ} {v : ℝ} (h : HasDerivAt f f' v) :
    HasDerivAt (fun s => f s + c) f' v := by
  refine ((h.add (hasDerivAt_const v c)).congr_of_eventuallyEq ?_).congr_deriv (by ring)
  filter_upwards with s
  rfl

/-- Subtracting a complex constant from a complex section preserves the derivative. -/
theorem hasDerivAt_sub_const_complex {f : ℝ → ℂ} {f' : ℂ} {v : ℝ} (h : HasDerivAt f f' v)
    (c : ℂ) : HasDerivAt (fun s => f s - c) f' v := by
  refine ((h.sub (hasDerivAt_const v c)).congr_of_eventuallyEq ?_).congr_deriv (by ring)
  filter_upwards with s
  rfl

/-- Left multiplication by a complex constant multiplies the derivative. -/
theorem hasDerivAt_const_mul_complex (c : ℂ) {f : ℝ → ℂ} {f' : ℂ} {v : ℝ}
    (h : HasDerivAt f f' v) :
    HasDerivAt (fun s => c * f s) (c * f') v :=
  HasDerivAt.const_mul c h

/-! ### Section derivatives of the radius -/

/-- The auxiliary radius has partial derivative `2x` in the x coordinate. -/
theorem hasDerivAt_radialAux_x (x y z t : ℝ) :
    HasDerivAt (fun x' => radialAux x' y z t) (2 * x) x := by
  have h : HasDerivAt (fun s : ℝ => s ^ 2 + (y ^ 2 + z ^ 2 - t ^ 2 + 1)) (2 * x) x :=
    hasDerivAt_add_const_real (hasDerivAt_sq x)
  exact h.congr_of_eventuallyEq (by
    filter_upwards with s
    show radialAux s y z t = s ^ 2 + (y ^ 2 + z ^ 2 - t ^ 2 + 1)
    unfold radialAux
    ring)

/-- The auxiliary radius has partial derivative `2y` in the y coordinate. -/
theorem hasDerivAt_radialAux_y (x y z t : ℝ) :
    HasDerivAt (fun y' => radialAux x y' z t) (2 * y) y := by
  have h : HasDerivAt (fun s : ℝ => s ^ 2 + (x ^ 2 + z ^ 2 - t ^ 2 + 1)) (2 * y) y :=
    hasDerivAt_add_const_real (hasDerivAt_sq y)
  exact h.congr_of_eventuallyEq (by
    filter_upwards with s
    show radialAux x s z t = s ^ 2 + (x ^ 2 + z ^ 2 - t ^ 2 + 1)
    unfold radialAux
    ring)

/-- The auxiliary radius has partial derivative `2z` in the z coordinate. -/
theorem hasDerivAt_radialAux_z (x y z t : ℝ) :
    HasDerivAt (fun z' => radialAux x y z' t) (2 * z) z := by
  have h : HasDerivAt (fun s : ℝ => s ^ 2 + (x ^ 2 + y ^ 2 - t ^ 2 + 1)) (2 * z) z :=
    hasDerivAt_add_const_real (hasDerivAt_sq z)
  exact h.congr_of_eventuallyEq (by
    filter_upwards with s
    show radialAux x y s t = s ^ 2 + (x ^ 2 + y ^ 2 - t ^ 2 + 1)
    unfold radialAux
    ring)

/-- The auxiliary radius has partial derivative `−2t` in the t coordinate. -/
theorem hasDerivAt_radialAux_t (x y z t : ℝ) :
    HasDerivAt (fun t' => radialAux x y z t') (-(2 * t)) t := by
  have h : HasDerivAt (fun s : ℝ => x ^ 2 + y ^ 2 + z ^ 2 + 1 + -(s ^ 2)) (-(2 * t)) t :=
    hasDerivAt_const_add_real (x ^ 2 + y ^ 2 + z ^ 2 + 1)
      (hasDerivAt_neg_real (hasDerivAt_sq t))
  exact h.congr_of_eventuallyEq (by
    filter_upwards with s
    show radialAux x y z s = x ^ 2 + y ^ 2 + z ^ 2 + 1 + -(s ^ 2)
    unfold radialAux
    ring)

/-! ### Section derivatives of the denominator and the two numerators -/

/-- The denominator section in x has complex derivative `2x`. -/
theorem hasDerivAt_complexDenominator_x (x y z t : ℝ) :
    HasDerivAt (fun x' => complexDenominator x' y z t) ((2 * x : ℝ) : ℂ) x :=
  hasDerivAt_add_const_complex
    (hasDerivAt_complex_ofReal_comp (hasDerivAt_radialAux_x x y z t))

/-- The denominator section in y has complex derivative `2y`. -/
theorem hasDerivAt_complexDenominator_y (x y z t : ℝ) :
    HasDerivAt (fun y' => complexDenominator x y' z t) ((2 * y : ℝ) : ℂ) y :=
  hasDerivAt_add_const_complex
    (hasDerivAt_complex_ofReal_comp (hasDerivAt_radialAux_y x y z t))

/-- The denominator section in z has complex derivative `2z`. -/
theorem hasDerivAt_complexDenominator_z (x y z t : ℝ) :
    HasDerivAt (fun z' => complexDenominator x y z' t) ((2 * z : ℝ) : ℂ) z :=
  hasDerivAt_add_const_complex
    (hasDerivAt_complex_ofReal_comp (hasDerivAt_radialAux_z x y z t))

/-- The denominator section in t has complex derivative `−2t + 2i`. -/
theorem hasDerivAt_complexDenominator_t (x y z t : ℝ) :
    HasDerivAt (fun t' => complexDenominator x y z t')
      ((-(2 * t : ℝ) : ℂ) + Complex.I * ((2 : ℝ) : ℂ)) t := by
  have hre := hasDerivAt_complex_ofReal_comp (hasDerivAt_radialAux_t x y z t)
  exact hasDerivAt_add_complex (hre.congr_deriv (by push_cast; ring))
    (hasDerivAt_const_mul_complex Complex.I
      (hasDerivAt_complex_ofReal_comp (hasDerivAt_two_mul_real t)))

/-- The α numerator section in x has complex derivative `2x`. -/
theorem hasDerivAt_alphaNumerator_x (x y z t : ℝ) :
    HasDerivAt (fun x' => ((radialAux x' y z t - 2 : ℝ) : ℂ)
      + Complex.I * ((2 * z : ℝ) : ℂ)) ((2 * x : ℝ) : ℂ) x :=
  hasDerivAt_add_const_complex
    (hasDerivAt_complex_ofReal_comp
      (hasDerivAt_sub_const_real (hasDerivAt_radialAux_x x y z t) 2))

/-- The α numerator section in y has complex derivative `2y`. -/
theorem hasDerivAt_alphaNumerator_y (x y z t : ℝ) :
    HasDerivAt (fun y' => ((radialAux x y' z t - 2 : ℝ) : ℂ)
      + Complex.I * ((2 * z : ℝ) : ℂ)) ((2 * y : ℝ) : ℂ) y :=
  hasDerivAt_add_const_complex
    (hasDerivAt_complex_ofReal_comp
      (hasDerivAt_sub_const_real (hasDerivAt_radialAux_y x y z t) 2))

/-- The α numerator section in z has complex derivative `2z + 2i`. -/
theorem hasDerivAt_alphaNumerator_z (x y z t : ℝ) :
    HasDerivAt (fun z' => ((radialAux x y z' t - 2 : ℝ) : ℂ)
      + Complex.I * ((2 * z' : ℝ) : ℂ))
      (((2 * z : ℝ) : ℂ) + Complex.I * ((2 : ℝ) : ℂ)) z :=
  hasDerivAt_add_complex
    (hasDerivAt_complex_ofReal_comp
      (hasDerivAt_sub_const_real (hasDerivAt_radialAux_z x y z t) 2))
    (hasDerivAt_const_mul_complex Complex.I
      (hasDerivAt_complex_ofReal_comp (hasDerivAt_two_mul_real z)))

/-- The α numerator section in t has complex derivative `−2t`. -/
theorem hasDerivAt_alphaNumerator_t (x y z t : ℝ) :
    HasDerivAt (fun t' => ((radialAux x y z t' - 2 : ℝ) : ℂ)
      + Complex.I * ((2 * z : ℝ) : ℂ)) ((-(2 * t : ℝ)) : ℂ) t := by
  have hre := hasDerivAt_complex_ofReal_comp
    (hasDerivAt_sub_const_real (hasDerivAt_radialAux_t x y z t) 2)
  exact hasDerivAt_add_const_complex (hre.congr_deriv (by push_cast; ring))

/-- The β numerator section in x has complex derivative `2`. -/
theorem hasDerivAt_betaNumerator_x (x y _z _t : ℝ) :
    HasDerivAt (fun x' => 2 * ((x' : ℝ) : ℂ) - Complex.I * ((2 * y : ℝ) : ℂ))
      (2 : ℂ) x := by
  refine hasDerivAt_sub_const_complex
    (HasDerivAt.const_mul (2 : ℂ) (hasDerivAt_complex_ofReal x)) _ |>.congr_deriv (by ring)

/-- The β numerator section in y has complex derivative `−2i`. -/
theorem hasDerivAt_betaNumerator_y (x y _z _t : ℝ) :
    HasDerivAt (fun y' => 2 * ((x : ℝ) : ℂ) - Complex.I * ((2 * y' : ℝ) : ℂ))
      (-(Complex.I * ((2 : ℝ) : ℂ))) y := by
  refine hasDerivAt_sub_complex
    (hasDerivAt_const_complex (2 * ((x : ℝ) : ℂ)) y)
    (hasDerivAt_const_mul_complex Complex.I
      (hasDerivAt_complex_ofReal_comp (hasDerivAt_two_mul_real y))) |>.congr_deriv (by norm_num)

/-- The β numerator section in z is constant, with derivative `0`. -/
theorem hasDerivAt_betaNumerator_z (x y z _t : ℝ) :
    HasDerivAt (fun _z' => 2 * ((x : ℝ) : ℂ) - Complex.I * ((2 * y : ℝ) : ℂ)) 0 z :=
  hasDerivAt_const_complex (2 * ((x : ℝ) : ℂ) - Complex.I * ((2 * y : ℝ) : ℂ)) z

/-- The β numerator section in t is constant, with derivative `0`. -/
theorem hasDerivAt_betaNumerator_t (x y _z t : ℝ) :
    HasDerivAt (fun _t' => 2 * ((x : ℝ) : ℂ) - Complex.I * ((2 * y : ℝ) : ℂ)) 0 t :=
  hasDerivAt_const_complex (2 * ((x : ℝ) : ℂ) - Complex.I * ((2 * y : ℝ) : ℂ)) t

/-! ### The eight actual spacetime partials of the rational pair -/

/-- The x partial of α is `4x·g / w²`: the derivative bridge for `∂ₓα`. -/
theorem hasDerivAt_rationalAlpha_x (x y z t : ℝ) :
    HasDerivAt (fun x' => rationalAlpha x' y z t) (alphaGradient x y z t 0) x := by
  have hw := complex_denominator_ne_zero x y z t
  have hw2 : complexDenominator x y z t ^ 2 ≠ 0 := pow_ne_zero 2 hw
  refine (hasDerivAt_alphaNumerator_x x y z t).fun_div
    (hasDerivAt_complexDenominator_x x y z t) hw |>.congr_deriv ?_
  show _ = alphaXNumerator x y z t / complexDenominator x y z t ^ 2
  rw [div_eq_div_iff hw2 hw2]
  apply Complex.ext <;>
    simp [alphaXNumerator, alphaCommonFactor, complexDenominator,
      Complex.mul_re, Complex.mul_im, pow_two] <;>
    ring

/-- The y partial of α is `4y·g / w²`: the derivative bridge for `∂_yα`. -/
theorem hasDerivAt_rationalAlpha_y (x y z t : ℝ) :
    HasDerivAt (fun y' => rationalAlpha x y' z t) (alphaGradient x y z t 1) y := by
  have hw := complex_denominator_ne_zero x y z t
  have hw2 : complexDenominator x y z t ^ 2 ≠ 0 := pow_ne_zero 2 hw
  refine (hasDerivAt_alphaNumerator_y x y z t).fun_div
    (hasDerivAt_complexDenominator_y x y z t) hw |>.congr_deriv ?_
  show _ = alphaYNumerator x y z t / complexDenominator x y z t ^ 2
  rw [div_eq_div_iff hw2 hw2]
  apply Complex.ext <;>
    simp [alphaYNumerator, alphaCommonFactor, complexDenominator,
      Complex.mul_re, Complex.mul_im, pow_two] <;>
    ring

/-- The z partial of α is `(4z·g + 2iw) / w²`: the derivative bridge for `∂_zα`. -/
theorem hasDerivAt_rationalAlpha_z (x y z t : ℝ) :
    HasDerivAt (fun z' => rationalAlpha x y z' t) (alphaGradient x y z t 2) z := by
  have hw := complex_denominator_ne_zero x y z t
  have hw2 : complexDenominator x y z t ^ 2 ≠ 0 := pow_ne_zero 2 hw
  refine (hasDerivAt_alphaNumerator_z x y z t).fun_div
    (hasDerivAt_complexDenominator_z x y z t) hw |>.congr_deriv ?_
  show _ = alphaZNumerator x y z t / complexDenominator x y z t ^ 2
  rw [div_eq_div_iff hw2 hw2]
  apply Complex.ext <;>
    simp [alphaZNumerator, alphaCommonFactor, complexDenominator,
      Complex.mul_re, Complex.mul_im, pow_two] <;>
    ring

/-- The t partial of α is `(−4t·g − 2i·n) / w²`: the derivative bridge for `∂_tα`. -/
theorem hasDerivAt_rationalAlpha_t (x y z t : ℝ) :
    HasDerivAt (fun t' => rationalAlpha x y z t') (alphaTimePartial x y z t) t := by
  have hw := complex_denominator_ne_zero x y z t
  have hw2 : complexDenominator x y z t ^ 2 ≠ 0 := pow_ne_zero 2 hw
  refine (hasDerivAt_alphaNumerator_t x y z t).fun_div
    (hasDerivAt_complexDenominator_t x y z t) hw |>.congr_deriv ?_
  show _ = alphaTNumerator x y z t / complexDenominator x y z t ^ 2
  rw [div_eq_div_iff hw2 hw2]
  apply Complex.ext <;>
    simp [alphaTNumerator, alphaCommonFactor, alphaNumerator, complexDenominator,
      Complex.mul_re, Complex.mul_im, pow_two] <;>
    ring

/-- The x partial of β is `(2w − 4xr) / w²`: the derivative bridge for `∂ₓβ`. -/
theorem hasDerivAt_rationalBeta_x (x y z t : ℝ) :
    HasDerivAt (fun x' => rationalBeta x' y z t) (betaGradient x y z t 0) x := by
  have hw := complex_denominator_ne_zero x y z t
  have hw2 : complexDenominator x y z t ^ 2 ≠ 0 := pow_ne_zero 2 hw
  refine (hasDerivAt_betaNumerator_x x y z t).fun_div
    (hasDerivAt_complexDenominator_x x y z t) hw |>.congr_deriv ?_
  show _ = betaXNumerator x y z t / complexDenominator x y z t ^ 2
  rw [div_eq_div_iff hw2 hw2]
  apply Complex.ext <;>
    simp [betaXNumerator, betaReducedNumerator, complexDenominator,
      Complex.mul_re, Complex.mul_im, pow_two] <;>
    ring

/-- The y partial of β is `(−2iw − 4yr) / w²`: the derivative bridge for `∂_yβ`. -/
theorem hasDerivAt_rationalBeta_y (x y z t : ℝ) :
    HasDerivAt (fun y' => rationalBeta x y' z t) (betaGradient x y z t 1) y := by
  have hw := complex_denominator_ne_zero x y z t
  have hw2 : complexDenominator x y z t ^ 2 ≠ 0 := pow_ne_zero 2 hw
  refine (hasDerivAt_betaNumerator_y x y z t).fun_div
    (hasDerivAt_complexDenominator_y x y z t) hw |>.congr_deriv ?_
  show _ = betaYNumerator x y z t / complexDenominator x y z t ^ 2
  rw [div_eq_div_iff hw2 hw2]
  apply Complex.ext <;>
    simp [betaYNumerator, betaReducedNumerator, complexDenominator,
      Complex.mul_re, Complex.mul_im, pow_two] <;>
    ring

/-- The z partial of β is `−4zr / w²`: the derivative bridge for `∂_zβ`. -/
theorem hasDerivAt_rationalBeta_z (x y z t : ℝ) :
    HasDerivAt (fun z' => rationalBeta x y z' t) (betaGradient x y z t 2) z := by
  have hw := complex_denominator_ne_zero x y z t
  have hw2 : complexDenominator x y z t ^ 2 ≠ 0 := pow_ne_zero 2 hw
  refine (hasDerivAt_betaNumerator_z x y z t).fun_div
    (hasDerivAt_complexDenominator_z x y z t) hw |>.congr_deriv ?_
  show _ = betaZNumerator x y z t / complexDenominator x y z t ^ 2
  rw [div_eq_div_iff hw2 hw2]
  apply Complex.ext <;>
    simp [betaZNumerator, betaReducedNumerator, complexDenominator,
      Complex.mul_re, Complex.mul_im, pow_two] <;>
    ring

/-- The t partial of β is `4(t − i)r / w²`: the derivative bridge for `∂_tβ`. -/
theorem hasDerivAt_rationalBeta_t (x y z t : ℝ) :
    HasDerivAt (fun t' => rationalBeta x y z t') (betaTimePartial x y z t) t := by
  have hw := complex_denominator_ne_zero x y z t
  have hw2 : complexDenominator x y z t ^ 2 ≠ 0 := pow_ne_zero 2 hw
  refine (hasDerivAt_betaNumerator_t x y z t).fun_div
    (hasDerivAt_complexDenominator_t x y z t) hw |>.congr_deriv ?_
  show _ = betaTNumerator x y z t / complexDenominator x y z t ^ 2
  rw [div_eq_div_iff hw2 hw2]
  apply Complex.ext <;>
    simp [betaTNumerator, betaReducedNumerator, complexDenominator,
      Complex.mul_re, Complex.mul_im, pow_two] <;>
    ring

/-! ### Bateman compatibility in all three components -/

/-- Bateman compatibility of the `w²`-scaled gradients holds in each component as
an exact complex polynomial identity in the real variables `x, y, z,t`. -/
theorem bateman_component_scaled (x y z t : ℝ) (j : Fin 3) :
    cross3 (alphaGradientNumerators x y z t) (betaGradientNumerators x y z t) j =
      Complex.I * (alphaTNumerator x y z t * betaGradientNumerators x y z t j
        - betaTNumerator x y z t * alphaGradientNumerators x y z t j) := by
  fin_cases j <;>
    apply Complex.ext <;>
    simp [cross3, alphaGradientNumerators, betaGradientNumerators,
      alphaXNumerator, alphaYNumerator, alphaZNumerator, alphaTNumerator,
      betaXNumerator, betaYNumerator, betaZNumerator, betaTNumerator,
      alphaCommonFactor, alphaNumerator, betaReducedNumerator, complexDenominator,
      radialAux, Complex.mul_re, Complex.mul_im, Complex.add_re, Complex.add_im,
      Complex.sub_re, Complex.sub_im, Complex.neg_re, Complex.neg_im,
      Complex.ofReal_re, Complex.ofReal_im,
      -Complex.ofReal_pow, -Complex.ofReal_mul, -Complex.ofReal_add,
      -Complex.ofReal_sub, -Complex.ofReal_neg] <;>
    ring

/-- Entrywise division of both arguments scales the cross product by `1/(cd)`. -/
theorem cross3_div (u v : Fin 3 → ℂ) (c d : ℂ) (hc : c ≠ 0) (hd : d ≠ 0) (j : Fin 3) :
    cross3 (fun k => u k / c) (fun k => v k / d) j = cross3 u v j / (c * d) := by
  fin_cases j <;> simp [cross3] <;> field_simp [hc, hd]

/-- The true gradients and time partials of the rational pair satisfy the Bateman
relation of [Kedia2013TyingKnots], equation (2), in each component. -/
theorem bateman_rational_component (x y z t : ℝ) (j : Fin 3) :
    cross3 (alphaGradient x y z t) (betaGradient x y z t) j =
      Complex.I * (alphaTimePartial x y z t * betaGradient x y z t j
        - betaTimePartial x y z t * alphaGradient x y z t j) := by
  have hw := complex_denominator_ne_zero x y z t
  have hw2 : complexDenominator x y z t ^ 2 ≠ 0 := pow_ne_zero 2 hw
  unfold alphaGradient betaGradient alphaTimePartial betaTimePartial
  rw [cross3_div _ _ _ _ hw2 hw2 j, bateman_component_scaled x y z t j]
  field_simp [hw2]

/-- The explicit rational pair satisfies the full Bateman compatibility equation
`∇α × ∇β = i(∂ₜα ∇β − ∂ₜβ ∇α)` of [Kedia2013TyingKnots], equation (2). -/
theorem bateman_rational_pair (x y z t : ℝ) :
    cross3 (alphaGradient x y z t) (betaGradient x y z t) =
      fun j => Complex.I * (alphaTimePartial x y z t * betaGradient x y z t j
        - betaTimePartial x y z t * alphaGradient x y z t j) := by
  funext j
  exact bateman_rational_component x y z t j

/-- The actual Riemann–Silberstein field `∇α × ∇β` of the rational pair is
algebraically null: its complex bilinear square vanishes identically. -/
theorem rational_field_null (x y z t : ℝ) :
    dot3 (rationalField x y z t) (rationalField x y z t) = 0 :=
  bateman_null _ _ _ _ (bateman_rational_pair x y z t)

/-- The real electric and magnetic parts of the actual field `∇α × ∇β` are
perpendicular and have equal squared magnitude at every space-time point. -/
theorem rational_field_real_invariants (x y z t : ℝ) :
    dot3 (fun j => (rationalField x y z t j).re) (fun j => (rationalField x y z t j).im) = 0 ∧
      squaredLength (fun j => (rationalField x y z t j).re) =
        squaredLength (fun j => (rationalField x y z t j).im) :=
  bateman_real_invariants _ _ _ _ (bateman_rational_pair x y z t)

/-! ### The zero-time stereographic specialization -/

/-- At `t = 0` the scalar α reduces to the first standard stereographic
coordinate `u = ((r² − 1) + 2iz)/(r² + 1)` on the unit three-sphere. -/
theorem rational_alpha_stereographic_zero_time (x y z : ℝ) :
    rationalAlpha x y z 0 =
      ((x ^ 2 + y ^ 2 + z ^ 2 - 1 : ℝ) + Complex.I * (2 * z : ℝ)) /
        ((x ^ 2 + y ^ 2 + z ^ 2 + 1 : ℝ) : ℂ) := by
  simp only [rationalAlpha, radialAux]
  congr 1 <;> push_cast <;> ring

/-- At `t = 0` the scalar β reduces to the second standard stereographic
coordinate `v = 2(x − iy)/(r² + 1)` on the unit three-sphere. -/
theorem rational_beta_stereographic_zero_time (x y z : ℝ) :
    rationalBeta x y z 0 =
      (2 * (x : ℂ) - Complex.I * (2 * y : ℝ)) /
        ((x ^ 2 + y ^ 2 + z ^ 2 + 1 : ℝ) : ℂ) := by
  simp only [rationalBeta, radialAux]
  norm_num

end Qatlib.Papers.KnotLight13.TorusFamily
