/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Papers.KnotLight13.TorusFamily.RationalDerivatives

/-!
# Source-free Maxwell equations for the rational Bateman field

[Kedia2013TyingKnots], equations (1)–(3) and (6),
[DOI](https://doi.org/10.1103/PhysRevLett.111.150404).
The Riemann–Silberstein field `F = ∇α × ∇β` of the rational pair is proved to be
a source-free Maxwell solution: its curl equals `i` times its time derivative in
every component, and its divergence vanishes, at every real space-time point.
This is the PDE content of the paper's statement that the Bateman construction
solves the free Maxwell equations. The proof identifies the exact rational
partial derivatives of the field entries through a second layer of section
derivatives (the partials of the cross-product numerators), each verified by the
quotient rule over the never-vanishing common denominator. No smoothness class,
energy estimate, or topological statement is claimed here.
-/

@[expose] public section
set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace Qatlib.Papers.KnotLight13.TorusFamily

open Qatlib.Papers.KnotLight13.TorusFamily (radialAux rationalAlpha rationalBeta)
open Qatlib.Papers.KnottedLight08.HopfField (cross3 dot3)
open Qatlib.Papers.KnotLight13.TorusFamily (complexDenominator alphaCommonFactor
  alphaNumerator betaReducedNumerator alphaXNumerator alphaYNumerator alphaZNumerator
  alphaTNumerator betaXNumerator betaYNumerator betaZNumerator betaTNumerator
  alphaGradientNumerators betaGradientNumerators alphaGradient betaGradient
  rationalField complex_denominator_ne_zero hasDerivAt_complex_ofReal
  hasDerivAt_complex_ofReal_comp hasDerivAt_const_complex hasDerivAt_add_complex
  hasDerivAt_sub_complex hasDerivAt_add_const_complex hasDerivAt_const_mul_complex
  hasDerivAt_complexDenominator_x hasDerivAt_complexDenominator_y
  hasDerivAt_complexDenominator_z hasDerivAt_complexDenominator_t
  hasDerivAt_alphaNumerator_x hasDerivAt_alphaNumerator_y hasDerivAt_alphaNumerator_z
  hasDerivAt_alphaNumerator_t)

/-! ### Additional lambda-form derivative combinators and atomic sections -/

/-- The product rule for complex-valued sections, in lambda form. -/
theorem hasDerivAt_mul_complex {f g : ℝ → ℂ} {f' g' : ℂ} {v : ℝ}
    (h1 : HasDerivAt f f' v) (h2 : HasDerivAt g g' v) :
    HasDerivAt (fun s => f s * g s) (f' * g v + f v * g') v :=
  h1.mul h2

/-- Negating a complex section negates the derivative. -/
theorem hasDerivAt_neg_complex {f : ℝ → ℂ} {f' : ℂ} {v : ℝ} (h : HasDerivAt f f' v) :
    HasDerivAt (fun s => -(f s)) (-f') v :=
  h.neg

/-- The common factor section in z has complex derivative `−i`. -/
theorem hasDerivAt_alphaCommonFactor_z (z t : ℝ) :
    HasDerivAt (fun z' => alphaCommonFactor z' t) (-(Complex.I)) z := by
  have hlin : HasDerivAt (fun z' : ℝ => (t : ℝ) - z') (-(1 : ℝ)) z := by
    refine (hasDerivAt_const z t).sub (hasDerivAt_id z) |>.congr_deriv ?_
    ring
  exact hasDerivAt_add_complex (hasDerivAt_const_complex 1 z)
    (hasDerivAt_const_mul_complex Complex.I (hasDerivAt_complex_ofReal_comp hlin)) |>.congr_deriv
    (by push_cast; ring)

/-- The common factor section in t has complex derivative `i`. -/
theorem hasDerivAt_alphaCommonFactor_t (z t : ℝ) :
    HasDerivAt (fun t' => alphaCommonFactor z t') (Complex.I) t := by
  have hlin : HasDerivAt (fun t' : ℝ => (t' : ℝ) - z) (1 : ℝ) t := by
    refine (hasDerivAt_id t).sub (hasDerivAt_const t z) |>.congr_deriv ?_
    ring
  exact hasDerivAt_add_complex (hasDerivAt_const_complex 1 t)
    (hasDerivAt_const_mul_complex Complex.I (hasDerivAt_complex_ofReal_comp hlin)) |>.congr_deriv
    (by push_cast; ring)

/-- The reduced β numerator section in x has complex derivative one. -/
theorem hasDerivAt_betaReducedNumerator_x (x y : ℝ) :
    HasDerivAt (fun x' => betaReducedNumerator x' y) 1 x :=
  hasDerivAt_sub_complex (hasDerivAt_complex_ofReal x)
    (hasDerivAt_const_complex (Complex.I * (y : ℝ)) x) |>.congr_deriv (by ring)

/-- The reduced β numerator section in y has complex derivative `−i`. -/
theorem hasDerivAt_betaReducedNumerator_y (x y : ℝ) :
    HasDerivAt (fun y' => betaReducedNumerator x y') (-(Complex.I)) y :=
  hasDerivAt_sub_complex (hasDerivAt_const_complex ((x : ℝ) : ℂ) y)
    (hasDerivAt_const_mul_complex Complex.I (hasDerivAt_complex_ofReal y)) |>.congr_deriv (by ring)

/-- The reduced β numerator section in z is constant. -/
theorem hasDerivAt_betaReducedNumerator_z (x y z : ℝ) :
    HasDerivAt (fun _z' => betaReducedNumerator x y) 0 z :=
  hasDerivAt_const_complex (betaReducedNumerator x y) z

/-- The reduced β numerator section in t is constant. -/
theorem hasDerivAt_betaReducedNumerator_t (x y t : ℝ) :
    HasDerivAt (fun _t' => betaReducedNumerator x y) 0 t :=
  hasDerivAt_const_complex (betaReducedNumerator x y) t

/-! ### Section derivatives of the eight first-level numerators -/

/-- `w²·∂ₓα` numerator section in x: derivative `4g`. -/
theorem hasDerivAt_alphaXNumerator_x (x y z t : ℝ) :
    HasDerivAt (fun x' => alphaXNumerator x' y z t)
      (4 * alphaCommonFactor z t) x :=
  hasDerivAt_mul_complex (hasDerivAt_const_mul_complex (4 : ℂ) (hasDerivAt_complex_ofReal x))
    (hasDerivAt_const_complex (alphaCommonFactor z t) x) |>.congr_deriv (by ring)

/-- `w²·∂ₓα` numerator section in y: derivative `0`. -/
theorem hasDerivAt_alphaXNumerator_y (x y z t : ℝ) :
    HasDerivAt (fun y' => alphaXNumerator x y' z t) 0 y :=
  hasDerivAt_const_complex (4 * ((x : ℝ) : ℂ) * alphaCommonFactor z t) y

/-- `w²·∂ₓα` numerator section in z: derivative `−4ix`. -/
theorem hasDerivAt_alphaXNumerator_z (x y z t : ℝ) :
    HasDerivAt (fun z' => alphaXNumerator x y z' t)
      (-(4 * Complex.I * (x : ℂ))) z :=
  hasDerivAt_const_mul_complex (4 * ((x : ℝ) : ℂ)) (hasDerivAt_alphaCommonFactor_z z t) |>.congr_deriv
    (by ring)

/-- `w²·∂ₓα` numerator section in t: derivative `4ix`. -/
theorem hasDerivAt_alphaXNumerator_t (x y z t : ℝ) :
    HasDerivAt (fun t' => alphaXNumerator x y z t')
      (4 * Complex.I * (x : ℂ)) t :=
  hasDerivAt_const_mul_complex (4 * ((x : ℝ) : ℂ)) (hasDerivAt_alphaCommonFactor_t z t) |>.congr_deriv
    (by ring)

/-- `w²·∂_yα` numerator section in x: derivative `0`. -/
theorem hasDerivAt_alphaYNumerator_x (x y z t : ℝ) :
    HasDerivAt (fun x' => alphaYNumerator x' y z t) 0 x :=
  hasDerivAt_const_complex (4 * ((y : ℝ) : ℂ) * alphaCommonFactor z t) x

/-- `w²·∂_yα` numerator section in y: derivative `4g`. -/
theorem hasDerivAt_alphaYNumerator_y (x y z t : ℝ) :
    HasDerivAt (fun y' => alphaYNumerator x y' z t)
      (4 * alphaCommonFactor z t) y :=
  hasDerivAt_mul_complex (hasDerivAt_const_mul_complex (4 : ℂ) (hasDerivAt_complex_ofReal y))
    (hasDerivAt_const_complex (alphaCommonFactor z t) y) |>.congr_deriv (by ring)

/-- `w²·∂_yα` numerator section in z: derivative `−4iy`. -/
theorem hasDerivAt_alphaYNumerator_z (x y z t : ℝ) :
    HasDerivAt (fun z' => alphaYNumerator x y z' t)
      (-(4 * Complex.I * (y : ℂ))) z :=
  hasDerivAt_const_mul_complex (4 * ((y : ℝ) : ℂ)) (hasDerivAt_alphaCommonFactor_z z t) |>.congr_deriv
    (by ring)

/-- `w²·∂_yα` numerator section in t: derivative `4iy`. -/
theorem hasDerivAt_alphaYNumerator_t (x y z t : ℝ) :
    HasDerivAt (fun t' => alphaYNumerator x y z t')
      (4 * Complex.I * (y : ℂ)) t :=
  hasDerivAt_const_mul_complex (4 * ((y : ℝ) : ℂ)) (hasDerivAt_alphaCommonFactor_t z t) |>.congr_deriv
    (by ring)

/-- `w²·∂_zα` numerator section in x: derivative `4ix`. -/
theorem hasDerivAt_alphaZNumerator_x (x y z t : ℝ) :
    HasDerivAt (fun x' => alphaZNumerator x' y z t)
      (4 * Complex.I * (x : ℂ)) x :=
  hasDerivAt_add_complex
    (hasDerivAt_const_complex (4 * ((z : ℝ) : ℂ) * alphaCommonFactor z t) x)
    (hasDerivAt_const_mul_complex (2 * Complex.I)
      (hasDerivAt_complexDenominator_x x y z t)) |>.congr_deriv (by push_cast; ring)

/-- `w²·∂_zα` numerator section in y: derivative `4iy`. -/
theorem hasDerivAt_alphaZNumerator_y (x y z t : ℝ) :
    HasDerivAt (fun y' => alphaZNumerator x y' z t)
      (4 * Complex.I * (y : ℂ)) y :=
  hasDerivAt_add_complex
    (hasDerivAt_const_complex (4 * ((z : ℝ) : ℂ) * alphaCommonFactor z t) y)
    (hasDerivAt_const_mul_complex (2 * Complex.I)
      (hasDerivAt_complexDenominator_y x y z t)) |>.congr_deriv (by push_cast; ring)

/-- `w²·∂_zα` numerator section in z: derivative `4g`. -/
theorem hasDerivAt_alphaZNumerator_z (x y z t : ℝ) :
    HasDerivAt (fun z' => alphaZNumerator x y z' t)
      (4 * alphaCommonFactor z t) z :=
  hasDerivAt_add_complex
    (hasDerivAt_mul_complex (hasDerivAt_const_mul_complex (4 : ℂ) (hasDerivAt_complex_ofReal z))
      (hasDerivAt_alphaCommonFactor_z z t))
    (hasDerivAt_const_mul_complex (2 * Complex.I)
      (hasDerivAt_complexDenominator_z x y z t)) |>.congr_deriv (by push_cast; ring)

/-- `w²·∂_zα` numerator section in t: derivative `4i(z − t) − 4`. -/
theorem hasDerivAt_alphaZNumerator_t (x y z t : ℝ) :
    HasDerivAt (fun t' => alphaZNumerator x y z t')
      (4 * Complex.I * ((z : ℂ) - (t : ℂ)) - 4) t :=
  hasDerivAt_add_complex
    (hasDerivAt_const_mul_complex (4 * ((z : ℝ) : ℂ)) (hasDerivAt_alphaCommonFactor_t z t))
    (hasDerivAt_const_mul_complex (2 * Complex.I)
      (hasDerivAt_complexDenominator_t x y z t)) |>.congr_deriv
    (by apply Complex.ext <;>
      simp [Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
        Complex.I_re, Complex.I_im] <;>
      linarith)

/-- `w²·∂_tα` numerator section in x: derivative `−4ix`. -/
theorem hasDerivAt_alphaTNumerator_x (x y z t : ℝ) :
    HasDerivAt (fun x' => alphaTNumerator x' y z t)
      (-(4 * Complex.I * (x : ℂ))) x :=
  hasDerivAt_sub_complex
    (hasDerivAt_neg_complex (hasDerivAt_const_mul_complex (4 * (t : ℝ) : ℂ)
      (hasDerivAt_const_complex (alphaCommonFactor z t) x)))
    (hasDerivAt_const_mul_complex (2 * Complex.I)
      (hasDerivAt_alphaNumerator_x x y z t)) |>.congr_deriv (by push_cast; ring)

/-- `w²·∂_tα` numerator section in y: derivative `−4iy`. -/
theorem hasDerivAt_alphaTNumerator_y (x y z t : ℝ) :
    HasDerivAt (fun y' => alphaTNumerator x y' z t)
      (-(4 * Complex.I * (y : ℂ))) y :=
  hasDerivAt_sub_complex
    (hasDerivAt_neg_complex (hasDerivAt_const_mul_complex (4 * (t : ℝ) : ℂ)
      (hasDerivAt_const_complex (alphaCommonFactor z t) y)))
    (hasDerivAt_const_mul_complex (2 * Complex.I)
      (hasDerivAt_alphaNumerator_y x y z t)) |>.congr_deriv (by push_cast; ring)

/-- `w²·∂_tα` numerator section in z: derivative `4i(t − z) + 4`. -/
theorem hasDerivAt_alphaTNumerator_z (x y z t : ℝ) :
    HasDerivAt (fun z' => alphaTNumerator x y z' t)
      (4 * Complex.I * ((t : ℂ) - (z : ℂ)) + 4) z :=
  hasDerivAt_sub_complex
    (hasDerivAt_neg_complex (hasDerivAt_const_mul_complex (4 * (t : ℝ) : ℂ)
      (hasDerivAt_alphaCommonFactor_z z t)))
    (hasDerivAt_const_mul_complex (2 * Complex.I)
      (hasDerivAt_alphaNumerator_z x y z t)) |>.congr_deriv
    (by apply Complex.ext <;>
      simp [Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
        Complex.I_re, Complex.I_im] <;>
      linarith)

/-- `w²·∂_tα` numerator section in t: derivative `−4g`. -/
theorem hasDerivAt_alphaTNumerator_t (x y z t : ℝ) :
    HasDerivAt (fun t' => alphaTNumerator x y z t')
      (-(4 * alphaCommonFactor z t)) t :=
  hasDerivAt_sub_complex
    (hasDerivAt_neg_complex (hasDerivAt_mul_complex
      (hasDerivAt_const_mul_complex (4 : ℂ) (hasDerivAt_complex_ofReal t))
      (hasDerivAt_alphaCommonFactor_t z t)))
    (hasDerivAt_const_mul_complex (2 * Complex.I)
      (hasDerivAt_alphaNumerator_t x y z t)) |>.congr_deriv (by push_cast; ring)

/-- `w²·∂ₓβ` numerator section in x: derivative `−4r`. -/
theorem hasDerivAt_betaXNumerator_x (x y z t : ℝ) :
    HasDerivAt (fun x' => betaXNumerator x' y z t)
      (-(4 * betaReducedNumerator x y)) x :=
  hasDerivAt_sub_complex
    (hasDerivAt_const_mul_complex (2 : ℂ) (hasDerivAt_complexDenominator_x x y z t))
    (hasDerivAt_mul_complex (hasDerivAt_const_mul_complex (4 : ℂ) (hasDerivAt_complex_ofReal x))
      (hasDerivAt_betaReducedNumerator_x x y)) |>.congr_deriv (by push_cast; ring)

/-- `w²·∂ₓβ` numerator section in y: derivative `4y + 4ix`. -/
theorem hasDerivAt_betaXNumerator_y (x y z t : ℝ) :
    HasDerivAt (fun y' => betaXNumerator x y' z t)
      (4 * ((y : ℝ) : ℂ) + 4 * Complex.I * (x : ℂ)) y :=
  hasDerivAt_sub_complex
    (hasDerivAt_const_mul_complex (2 : ℂ) (hasDerivAt_complexDenominator_y x y z t))
    (hasDerivAt_const_mul_complex (4 * ((x : ℝ) : ℂ))
      (hasDerivAt_betaReducedNumerator_y x y)) |>.congr_deriv (by push_cast; ring)

/-- `w²·∂ₓβ` numerator section in z: derivative `4z`. -/
theorem hasDerivAt_betaXNumerator_z (x y z t : ℝ) :
    HasDerivAt (fun z' => betaXNumerator x y z' t)
      (4 * ((z : ℝ) : ℂ)) z :=
  hasDerivAt_sub_complex
    (hasDerivAt_const_mul_complex (2 : ℂ) (hasDerivAt_complexDenominator_z x y z t))
    (hasDerivAt_const_complex (4 * ((x : ℝ) : ℂ) * betaReducedNumerator x y) z) |>.congr_deriv
    (by push_cast; ring)

/-- `w²·∂ₓβ` numerator section in t: derivative `−4t + 4i`. -/
theorem hasDerivAt_betaXNumerator_t (x y z t : ℝ) :
    HasDerivAt (fun t' => betaXNumerator x y z t')
      (-(4 * (t : ℂ)) + 4 * Complex.I) t :=
  hasDerivAt_sub_complex
    (hasDerivAt_const_mul_complex (2 : ℂ) (hasDerivAt_complexDenominator_t x y z t))
    (hasDerivAt_const_complex (4 * ((x : ℝ) : ℂ) * betaReducedNumerator x y) t) |>.congr_deriv
    (by push_cast; ring)

/-- `w²·∂_yβ` numerator section in x: derivative `−4y − 4ix`. -/
theorem hasDerivAt_betaYNumerator_x (x y z t : ℝ) :
    HasDerivAt (fun x' => betaYNumerator x' y z t)
      (-(4 * ((y : ℝ) : ℂ)) - 4 * Complex.I * (x : ℂ)) x :=
  hasDerivAt_sub_complex
    (hasDerivAt_neg_complex (hasDerivAt_const_mul_complex (2 * Complex.I)
      (hasDerivAt_complexDenominator_x x y z t)))
    (hasDerivAt_mul_complex (hasDerivAt_const_complex (4 * ((y : ℝ) : ℂ)) x)
      (hasDerivAt_betaReducedNumerator_x x y)) |>.congr_deriv (by push_cast; ring)

/-- `w²·∂_yβ` numerator section in y: derivative `−4r`. -/
theorem hasDerivAt_betaYNumerator_y (x y z t : ℝ) :
    HasDerivAt (fun y' => betaYNumerator x y' z t)
      (-(4 * betaReducedNumerator x y)) y :=
  hasDerivAt_sub_complex
    (hasDerivAt_neg_complex (hasDerivAt_const_mul_complex (2 * Complex.I)
      (hasDerivAt_complexDenominator_y x y z t)))
    (hasDerivAt_mul_complex (hasDerivAt_const_mul_complex (4 : ℂ) (hasDerivAt_complex_ofReal y))
      (hasDerivAt_betaReducedNumerator_y x y)) |>.congr_deriv (by push_cast; ring)

/-- `w²·∂_yβ` numerator section in z: derivative `−4iz`. -/
theorem hasDerivAt_betaYNumerator_z (x y z t : ℝ) :
    HasDerivAt (fun z' => betaYNumerator x y z' t)
      (-(4 * Complex.I * (z : ℂ))) z :=
  hasDerivAt_sub_complex
    (hasDerivAt_neg_complex (hasDerivAt_const_mul_complex (2 * Complex.I)
      (hasDerivAt_complexDenominator_z x y z t)))
    (hasDerivAt_const_complex (4 * ((y : ℝ) : ℂ) * betaReducedNumerator x y) z) |>.congr_deriv
    (by push_cast; ring)

/-- `w²·∂_yβ` numerator section in t: derivative `4it + 4`. -/
theorem hasDerivAt_betaYNumerator_t (x y z t : ℝ) :
    HasDerivAt (fun t' => betaYNumerator x y z t')
      (4 * Complex.I * (t : ℂ) + 4) t :=
  hasDerivAt_sub_complex
    (hasDerivAt_neg_complex (hasDerivAt_const_mul_complex (2 * Complex.I)
      (hasDerivAt_complexDenominator_t x y z t)))
    (hasDerivAt_const_complex (4 * ((y : ℝ) : ℂ) * betaReducedNumerator x y) t) |>.congr_deriv
    (by apply Complex.ext <;>
      simp [Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
        Complex.I_re, Complex.I_im] <;>
      linarith)

/-- `w²·∂_zβ` numerator section in x: derivative `−4z`. -/
theorem hasDerivAt_betaZNumerator_x (x y z t : ℝ) :
    HasDerivAt (fun x' => betaZNumerator x' y z t)
      (-(4 * ((z : ℝ) : ℂ))) x :=
  hasDerivAt_neg_complex (hasDerivAt_mul_complex
    (hasDerivAt_const_complex (4 * ((z : ℝ) : ℂ)) x)
    (hasDerivAt_betaReducedNumerator_x x y)) |>.congr_deriv (by ring)

/-- `w²·∂_zβ` numerator section in y: derivative `4iz`. -/
theorem hasDerivAt_betaZNumerator_y (x y z t : ℝ) :
    HasDerivAt (fun y' => betaZNumerator x y' z t)
      (4 * Complex.I * (z : ℂ)) y :=
  hasDerivAt_neg_complex (hasDerivAt_const_mul_complex (4 * ((z : ℝ) : ℂ))
    (hasDerivAt_betaReducedNumerator_y x y)) |>.congr_deriv (by ring)

/-- `w²·∂_zβ` numerator section in z: derivative `−4r`. -/
theorem hasDerivAt_betaZNumerator_z (x y z t : ℝ) :
    HasDerivAt (fun z' => betaZNumerator x y z' t)
      (-(4 * betaReducedNumerator x y)) z :=
  hasDerivAt_neg_complex (hasDerivAt_mul_complex
    (hasDerivAt_const_mul_complex (4 : ℂ) (hasDerivAt_complex_ofReal z))
    (hasDerivAt_betaReducedNumerator_z x y z)) |>.congr_deriv (by ring)

/-- `w²·∂_zβ` numerator section in t: derivative `0`. -/
theorem hasDerivAt_betaZNumerator_t (x y z t : ℝ) :
    HasDerivAt (fun _t' => betaZNumerator x y z t) 0 t :=
  hasDerivAt_const_complex (-(4 * ((z : ℝ) : ℂ) * betaReducedNumerator x y)) t

/-- `w²·∂_tβ` numerator section in x: derivative `4(t − i)`. -/
theorem hasDerivAt_betaTNumerator_x (x y z t : ℝ) :
    HasDerivAt (fun x' => betaTNumerator x' y z t)
      (4 * ((t : ℂ) - Complex.I)) x :=
  hasDerivAt_const_mul_complex (4 * (((t : ℝ) : ℂ) - Complex.I))
    (hasDerivAt_betaReducedNumerator_x x y) |>.congr_deriv (by ring)

/-- `w²·∂_tβ` numerator section in y: derivative `−4i(t − i)`. -/
theorem hasDerivAt_betaTNumerator_y (x y z t : ℝ) :
    HasDerivAt (fun y' => betaTNumerator x y' z t)
      (-(4 * Complex.I * ((t : ℂ) - Complex.I))) y :=
  hasDerivAt_const_mul_complex (4 * (((t : ℝ) : ℂ) - Complex.I))
    (hasDerivAt_betaReducedNumerator_y x y) |>.congr_deriv (by ring)

/-- `w²·∂_tβ` numerator section in z: derivative `0`. -/
theorem hasDerivAt_betaTNumerator_z (x y z t : ℝ) :
    HasDerivAt (fun z' => betaTNumerator x y z' t) 0 z :=
  hasDerivAt_mul_complex
    (hasDerivAt_const_complex (4 * (((t : ℝ) : ℂ) - Complex.I)) z)
    (hasDerivAt_betaReducedNumerator_z x y z) |>.congr_deriv (by ring)

/-- `w²·∂_tβ` numerator section in t: derivative `4r`. -/
theorem hasDerivAt_betaTNumerator_t (x y z t : ℝ) :
    HasDerivAt (fun t' => betaTNumerator x y z t')
      (4 * betaReducedNumerator x y) t :=
  hasDerivAt_mul_complex
    (hasDerivAt_const_mul_complex (4 : ℂ)
      (hasDerivAt_sub_complex (hasDerivAt_complex_ofReal t)
        (hasDerivAt_const_complex (Complex.I) t)))
    (hasDerivAt_betaReducedNumerator_t x y t) |>.congr_deriv (by ring)

/-! ### Section derivatives of the cross-product numerators -/

/-- The first cross numerator entry `w⁴·F₀ = ∇α×∇β entry 0`, in x: exact value. -/
theorem hasDerivAt_crossNumerators_x_zero (x y z t : ℝ) :
    HasDerivAt (fun x' => cross3 (alphaGradientNumerators x' y z t)
        (betaGradientNumerators x' y z t) 0)
      (0 * betaZNumerator x y z t + alphaYNumerator x y z t * (-(4 * ((z : ℝ) : ℂ))) -
        (4 * Complex.I * ((x : ℝ) : ℂ) * betaYNumerator x y z t +
          alphaZNumerator x y z t * (-(4 * ((y : ℝ) : ℂ)) -
            4 * Complex.I * ((x : ℝ) : ℂ)))) x :=
  hasDerivAt_sub_complex
    (hasDerivAt_mul_complex (hasDerivAt_alphaYNumerator_x x y z t)
      (hasDerivAt_betaZNumerator_x x y z t))
    (hasDerivAt_mul_complex (hasDerivAt_alphaZNumerator_x x y z t)
      (hasDerivAt_betaYNumerator_x x y z t))

/-- The second cross numerator entry, in x. -/
theorem hasDerivAt_crossNumerators_x_one (x y z t : ℝ) :
    HasDerivAt (fun x' => cross3 (alphaGradientNumerators x' y z t)
        (betaGradientNumerators x' y z t) 1)
      (4 * Complex.I * ((x : ℝ) : ℂ) * betaXNumerator x y z t +
          alphaZNumerator x y z t * (-(4 * betaReducedNumerator x y)) -
        (4 * alphaCommonFactor z t * betaZNumerator x y z t +
          alphaXNumerator x y z t * (-(4 * ((z : ℝ) : ℂ))))) x :=
  hasDerivAt_sub_complex
    (hasDerivAt_mul_complex (hasDerivAt_alphaZNumerator_x x y z t)
      (hasDerivAt_betaXNumerator_x x y z t))
    (hasDerivAt_mul_complex (hasDerivAt_alphaXNumerator_x x y z t)
      (hasDerivAt_betaZNumerator_x x y z t))

/-- The third cross numerator entry, in x. -/
theorem hasDerivAt_crossNumerators_x_two (x y z t : ℝ) :
    HasDerivAt (fun x' => cross3 (alphaGradientNumerators x' y z t)
        (betaGradientNumerators x' y z t) 2)
      (4 * alphaCommonFactor z t * betaYNumerator x y z t +
          alphaXNumerator x y z t * (-(4 * ((y : ℝ) : ℂ)) -
            4 * Complex.I * ((x : ℝ) : ℂ)) -
        (0 * betaXNumerator x y z t +
          alphaYNumerator x y z t * (-(4 * betaReducedNumerator x y)))) x :=
  hasDerivAt_sub_complex
    (hasDerivAt_mul_complex (hasDerivAt_alphaXNumerator_x x y z t)
      (hasDerivAt_betaYNumerator_x x y z t))
    (hasDerivAt_mul_complex (hasDerivAt_alphaYNumerator_x x y z t)
      (hasDerivAt_betaXNumerator_x x y z t))

/-- The first cross numerator entry, in y. -/
theorem hasDerivAt_crossNumerators_y_zero (x y z t : ℝ) :
    HasDerivAt (fun y' => cross3 (alphaGradientNumerators x y' z t)
        (betaGradientNumerators x y' z t) 0)
      (4 * alphaCommonFactor z t * betaZNumerator x y z t +
          alphaYNumerator x y z t * (4 * Complex.I * ((z : ℝ) : ℂ)) -
        (4 * Complex.I * ((y : ℝ) : ℂ) * betaYNumerator x y z t +
          alphaZNumerator x y z t * (-(4 * betaReducedNumerator x y)))) y :=
  hasDerivAt_sub_complex
    (hasDerivAt_mul_complex (hasDerivAt_alphaYNumerator_y x y z t)
      (hasDerivAt_betaZNumerator_y x y z t))
    (hasDerivAt_mul_complex (hasDerivAt_alphaZNumerator_y x y z t)
      (hasDerivAt_betaYNumerator_y x y z t))

/-- The second cross numerator entry, in y. -/
theorem hasDerivAt_crossNumerators_y_one (x y z t : ℝ) :
    HasDerivAt (fun y' => cross3 (alphaGradientNumerators x y' z t)
        (betaGradientNumerators x y' z t) 1)
      (4 * Complex.I * ((y : ℝ) : ℂ) * betaXNumerator x y z t +
          alphaZNumerator x y z t * (4 * ((y : ℝ) : ℂ) +
            4 * Complex.I * ((x : ℝ) : ℂ)) -
        (0 * betaZNumerator x y z t +
          alphaXNumerator x y z t * (4 * Complex.I * ((z : ℝ) : ℂ)))) y :=
  hasDerivAt_sub_complex
    (hasDerivAt_mul_complex (hasDerivAt_alphaZNumerator_y x y z t)
      (hasDerivAt_betaXNumerator_y x y z t))
    (hasDerivAt_mul_complex (hasDerivAt_alphaXNumerator_y x y z t)
      (hasDerivAt_betaZNumerator_y x y z t))

/-- The third cross numerator entry, in y. -/
theorem hasDerivAt_crossNumerators_y_two (x y z t : ℝ) :
    HasDerivAt (fun y' => cross3 (alphaGradientNumerators x y' z t)
        (betaGradientNumerators x y' z t) 2)
      (0 * betaYNumerator x y z t +
          alphaXNumerator x y z t * (-(4 * betaReducedNumerator x y)) -
        (4 * alphaCommonFactor z t * betaXNumerator x y z t +
          alphaYNumerator x y z t * (4 * ((y : ℝ) : ℂ) +
            4 * Complex.I * ((x : ℝ) : ℂ)))) y :=
  hasDerivAt_sub_complex
    (hasDerivAt_mul_complex (hasDerivAt_alphaXNumerator_y x y z t)
      (hasDerivAt_betaYNumerator_y x y z t))
    (hasDerivAt_mul_complex (hasDerivAt_alphaYNumerator_y x y z t)
      (hasDerivAt_betaXNumerator_y x y z t))

/-- The first cross numerator entry, in z. -/
theorem hasDerivAt_crossNumerators_z_zero (x y z t : ℝ) :
    HasDerivAt (fun z' => cross3 (alphaGradientNumerators x y z' t)
        (betaGradientNumerators x y z' t) 0)
      (-(4 * Complex.I * ((y : ℝ) : ℂ)) * betaZNumerator x y z t +
          alphaYNumerator x y z t * (-(4 * betaReducedNumerator x y)) -
        (4 * alphaCommonFactor z t * betaYNumerator x y z t +
          alphaZNumerator x y z t * (-(4 * Complex.I * ((z : ℝ) : ℂ))))) z :=
  hasDerivAt_sub_complex
    (hasDerivAt_mul_complex (hasDerivAt_alphaYNumerator_z x y z t)
      (hasDerivAt_betaZNumerator_z x y z t))
    (hasDerivAt_mul_complex (hasDerivAt_alphaZNumerator_z x y z t)
      (hasDerivAt_betaYNumerator_z x y z t))

/-- The second cross numerator entry, in z. -/
theorem hasDerivAt_crossNumerators_z_one (x y z t : ℝ) :
    HasDerivAt (fun z' => cross3 (alphaGradientNumerators x y z' t)
        (betaGradientNumerators x y z' t) 1)
      (4 * alphaCommonFactor z t * betaXNumerator x y z t +
          alphaZNumerator x y z t * (4 * ((z : ℝ) : ℂ)) -
        (-(4 * Complex.I * ((x : ℝ) : ℂ)) * betaZNumerator x y z t +
          alphaXNumerator x y z t * (-(4 * betaReducedNumerator x y)))) z :=
  hasDerivAt_sub_complex
    (hasDerivAt_mul_complex (hasDerivAt_alphaZNumerator_z x y z t)
      (hasDerivAt_betaXNumerator_z x y z t))
    (hasDerivAt_mul_complex (hasDerivAt_alphaXNumerator_z x y z t)
      (hasDerivAt_betaZNumerator_z x y z t))

/-- The third cross numerator entry, in z. -/
theorem hasDerivAt_crossNumerators_z_two (x y z t : ℝ) :
    HasDerivAt (fun z' => cross3 (alphaGradientNumerators x y z' t)
        (betaGradientNumerators x y z' t) 2)
      (-(4 * Complex.I * ((x : ℝ) : ℂ)) * betaYNumerator x y z t +
          alphaXNumerator x y z t * (-(4 * Complex.I * ((z : ℝ) : ℂ))) -
        (-(4 * Complex.I * ((y : ℝ) : ℂ)) * betaXNumerator x y z t +
          alphaYNumerator x y z t * (4 * ((z : ℝ) : ℂ)))) z :=
  hasDerivAt_sub_complex
    (hasDerivAt_mul_complex (hasDerivAt_alphaXNumerator_z x y z t)
      (hasDerivAt_betaYNumerator_z x y z t))
    (hasDerivAt_mul_complex (hasDerivAt_alphaYNumerator_z x y z t)
      (hasDerivAt_betaXNumerator_z x y z t))

/-- The first cross numerator entry, in t. -/
theorem hasDerivAt_crossNumerators_t_zero (x y z t : ℝ) :
    HasDerivAt (fun t' => cross3 (alphaGradientNumerators x y z t')
        (betaGradientNumerators x y z t') 0)
      ((4 * Complex.I * (y : ℂ) * betaZNumerator x y z t +
          alphaYNumerator x y z t * 0) -
        ((4 * Complex.I * ((z : ℂ) - (t : ℂ)) - 4) * betaYNumerator x y z t +
          alphaZNumerator x y z t * (4 * Complex.I * (t : ℂ) + 4))) t :=
  hasDerivAt_sub_complex
    (hasDerivAt_mul_complex (hasDerivAt_alphaYNumerator_t x y z t)
      (hasDerivAt_betaZNumerator_t x y z t))
    (hasDerivAt_mul_complex (hasDerivAt_alphaZNumerator_t x y z t)
      (hasDerivAt_betaYNumerator_t x y z t))

/-- The second cross numerator entry, in t. -/
theorem hasDerivAt_crossNumerators_t_one (x y z t : ℝ) :
    HasDerivAt (fun t' => cross3 (alphaGradientNumerators x y z t')
        (betaGradientNumerators x y z t') 1)
      (((4 * Complex.I * ((z : ℂ) - (t : ℂ)) - 4) * betaXNumerator x y z t +
          alphaZNumerator x y z t * (-(4 * (t : ℂ)) + 4 * Complex.I)) -
        (4 * Complex.I * (x : ℂ) * betaZNumerator x y z t +
          alphaXNumerator x y z t * 0)) t :=
  hasDerivAt_sub_complex
    (hasDerivAt_mul_complex (hasDerivAt_alphaZNumerator_t x y z t)
      (hasDerivAt_betaXNumerator_t x y z t))
    (hasDerivAt_mul_complex (hasDerivAt_alphaXNumerator_t x y z t)
      (hasDerivAt_betaZNumerator_t x y z t))

/-- The third cross numerator entry, in t. -/
theorem hasDerivAt_crossNumerators_t_two (x y z t : ℝ) :
    HasDerivAt (fun t' => cross3 (alphaGradientNumerators x y z t')
        (betaGradientNumerators x y z t') 2)
      ((4 * Complex.I * (x : ℂ) * betaYNumerator x y z t +
          alphaXNumerator x y z t * (4 * Complex.I * (t : ℂ) + 4)) -
        (4 * Complex.I * (y : ℂ) * betaXNumerator x y z t +
          alphaYNumerator x y z t * (-(4 * (t : ℂ)) + 4 * Complex.I))) t :=
  hasDerivAt_sub_complex
    (hasDerivAt_mul_complex (hasDerivAt_alphaXNumerator_t x y z t)
      (hasDerivAt_betaYNumerator_t x y z t))
    (hasDerivAt_mul_complex (hasDerivAt_alphaYNumerator_t x y z t)
      (hasDerivAt_betaXNumerator_t x y z t))

/-! ### Exact spacetime partials of the field entries -/

/-- Every rational field entry is the cross-numerator entry over the fourth power
of the never-vanishing common denominator. -/
theorem rationalField_eq_cross_div (x y z t : ℝ) (j : Fin 3) :
    rationalField x y z t j =
      cross3 (alphaGradientNumerators x y z t) (betaGradientNumerators x y z t) j /
        complexDenominator x y z t ^ 4 := by
  unfold rationalField alphaGradient betaGradient
  rw [cross3_div _ _ _ _
    (pow_ne_zero 2 (complex_denominator_ne_zero x y z t))
    (pow_ne_zero 2 (complex_denominator_ne_zero x y z t))]
  congr 1
  ring

/-- The quotient-rule bridge from cross-numerator and denominator sections to a
field entry: the entry `f / g⁴` has derivative `(V·g − 4W·f v)/g⁵`. -/
theorem hasDerivAt_field_of_sections {f g : ℝ → ℂ} {V W : ℂ} {v : ℝ}
    (hN : HasDerivAt f V v) (hW : HasDerivAt g W v) (hg : g v ≠ 0) :
    HasDerivAt (fun v' => f v' / g v' ^ 4)
      ((V * g v - 4 * W * f v) / g v ^ 5) v := by
  have h4 : g v ^ 4 ≠ 0 := pow_ne_zero 4 hg
  refine (hN.fun_div (hW.pow 4) h4).congr_deriv ?_
  simp only [Pi.pow_apply]
  field_simp [hg]
  norm_num
  ring

/-- The x partial of the first field entry. -/
theorem hasDerivAt_rationalField_x_zero (x y z t : ℝ) :
    HasDerivAt (fun x' => rationalField x' y z t 0)
      ((((0 * betaZNumerator x y z t + alphaYNumerator x y z t * (-(4 * ((z : ℝ) : ℂ))) - (4 * Complex.I * ((x : ℝ) : ℂ) * betaYNumerator x y z t + alphaZNumerator x y z t * (-(4 * ((y : ℝ) : ℂ)) - 4 * Complex.I * ((x : ℝ) : ℂ))))) * complexDenominator x y z t -
        4 * ((2 * x : ℝ) : ℂ) *
          cross3 (alphaGradientNumerators x y z t) (betaGradientNumerators x y z t) 0) /
        complexDenominator x y z t ^ 5) x := by
  have h := hasDerivAt_field_of_sections (hasDerivAt_crossNumerators_x_zero x y z t)
    (hasDerivAt_complexDenominator_x x y z t) (complex_denominator_ne_zero x y z t)
  exact h.congr_of_eventuallyEq (by
    filter_upwards with x'
    rw [rationalField_eq_cross_div])

/-- The y partial of the first field entry. -/
theorem hasDerivAt_rationalField_y_zero (x y z t : ℝ) :
    HasDerivAt (fun y' => rationalField x y' z t 0)
      ((((4 * alphaCommonFactor z t * betaZNumerator x y z t + alphaYNumerator x y z t * (4 * Complex.I * ((z : ℝ) : ℂ)) - (4 * Complex.I * ((y : ℝ) : ℂ) * betaYNumerator x y z t + alphaZNumerator x y z t * (-(4 * betaReducedNumerator x y))))) * complexDenominator x y z t -
        4 * ((2 * y : ℝ) : ℂ) *
          cross3 (alphaGradientNumerators x y z t) (betaGradientNumerators x y z t) 0) /
        complexDenominator x y z t ^ 5) y := by
  have h := hasDerivAt_field_of_sections (hasDerivAt_crossNumerators_y_zero x y z t)
    (hasDerivAt_complexDenominator_y x y z t) (complex_denominator_ne_zero x y z t)
  exact h.congr_of_eventuallyEq (by
    filter_upwards with y'
    rw [rationalField_eq_cross_div])

/-- The z partial of the first field entry. -/
theorem hasDerivAt_rationalField_z_zero (x y z t : ℝ) :
    HasDerivAt (fun z' => rationalField x y z' t 0)
      ((((-(4 * Complex.I * ((y : ℝ) : ℂ)) * betaZNumerator x y z t + alphaYNumerator x y z t * (-(4 * betaReducedNumerator x y)) - (4 * alphaCommonFactor z t * betaYNumerator x y z t + alphaZNumerator x y z t * (-(4 * Complex.I * ((z : ℝ) : ℂ)))))) * complexDenominator x y z t -
        4 * ((2 * z : ℝ) : ℂ) *
          cross3 (alphaGradientNumerators x y z t) (betaGradientNumerators x y z t) 0) /
        complexDenominator x y z t ^ 5) z := by
  have h := hasDerivAt_field_of_sections (hasDerivAt_crossNumerators_z_zero x y z t)
    (hasDerivAt_complexDenominator_z x y z t) (complex_denominator_ne_zero x y z t)
  exact h.congr_of_eventuallyEq (by
    filter_upwards with z'
    rw [rationalField_eq_cross_div])

/-- The t partial of the first field entry. -/
theorem hasDerivAt_rationalField_t_zero (x y z t : ℝ) :
    HasDerivAt (fun t' => rationalField x y z t' 0)
      (((((4 * Complex.I * (y : ℂ) * betaZNumerator x y z t + alphaYNumerator x y z t * 0) - ((4 * Complex.I * ((z : ℂ) - (t : ℂ)) - 4) * betaYNumerator x y z t + alphaZNumerator x y z t * (4 * Complex.I * (t : ℂ) + 4)))) * complexDenominator x y z t -
        4 * ((-(2 * t : ℝ) : ℂ) + Complex.I * ((2 : ℝ) : ℂ)) *
          cross3 (alphaGradientNumerators x y z t) (betaGradientNumerators x y z t) 0) /
        complexDenominator x y z t ^ 5) t := by
  have h := hasDerivAt_field_of_sections (hasDerivAt_crossNumerators_t_zero x y z t)
    (hasDerivAt_complexDenominator_t x y z t) (complex_denominator_ne_zero x y z t)
  exact h.congr_of_eventuallyEq (by
    filter_upwards with t'
    rw [rationalField_eq_cross_div])

/-- The x partial of the second field entry. -/
theorem hasDerivAt_rationalField_x_one (x y z t : ℝ) :
    HasDerivAt (fun x' => rationalField x' y z t 1)
      ((((4 * Complex.I * ((x : ℝ) : ℂ) * betaXNumerator x y z t + alphaZNumerator x y z t * (-(4 * betaReducedNumerator x y)) - (4 * alphaCommonFactor z t * betaZNumerator x y z t + alphaXNumerator x y z t * (-(4 * ((z : ℝ) : ℂ)))))) * complexDenominator x y z t -
        4 * ((2 * x : ℝ) : ℂ) *
          cross3 (alphaGradientNumerators x y z t) (betaGradientNumerators x y z t) 1) /
        complexDenominator x y z t ^ 5) x := by
  have h := hasDerivAt_field_of_sections (hasDerivAt_crossNumerators_x_one x y z t)
    (hasDerivAt_complexDenominator_x x y z t) (complex_denominator_ne_zero x y z t)
  exact h.congr_of_eventuallyEq (by
    filter_upwards with x'
    rw [rationalField_eq_cross_div])

/-- The y partial of the second field entry. -/
theorem hasDerivAt_rationalField_y_one (x y z t : ℝ) :
    HasDerivAt (fun y' => rationalField x y' z t 1)
      ((((4 * Complex.I * ((y : ℝ) : ℂ) * betaXNumerator x y z t + alphaZNumerator x y z t * (4 * ((y : ℝ) : ℂ) + 4 * Complex.I * ((x : ℝ) : ℂ)) - (0 * betaZNumerator x y z t + alphaXNumerator x y z t * (4 * Complex.I * ((z : ℝ) : ℂ))))) * complexDenominator x y z t -
        4 * ((2 * y : ℝ) : ℂ) *
          cross3 (alphaGradientNumerators x y z t) (betaGradientNumerators x y z t) 1) /
        complexDenominator x y z t ^ 5) y := by
  have h := hasDerivAt_field_of_sections (hasDerivAt_crossNumerators_y_one x y z t)
    (hasDerivAt_complexDenominator_y x y z t) (complex_denominator_ne_zero x y z t)
  exact h.congr_of_eventuallyEq (by
    filter_upwards with y'
    rw [rationalField_eq_cross_div])

/-- The z partial of the second field entry. -/
theorem hasDerivAt_rationalField_z_one (x y z t : ℝ) :
    HasDerivAt (fun z' => rationalField x y z' t 1)
      ((((4 * alphaCommonFactor z t * betaXNumerator x y z t + alphaZNumerator x y z t * (4 * ((z : ℝ) : ℂ)) - (-(4 * Complex.I * ((x : ℝ) : ℂ)) * betaZNumerator x y z t + alphaXNumerator x y z t * (-(4 * betaReducedNumerator x y))))) * complexDenominator x y z t -
        4 * ((2 * z : ℝ) : ℂ) *
          cross3 (alphaGradientNumerators x y z t) (betaGradientNumerators x y z t) 1) /
        complexDenominator x y z t ^ 5) z := by
  have h := hasDerivAt_field_of_sections (hasDerivAt_crossNumerators_z_one x y z t)
    (hasDerivAt_complexDenominator_z x y z t) (complex_denominator_ne_zero x y z t)
  exact h.congr_of_eventuallyEq (by
    filter_upwards with z'
    rw [rationalField_eq_cross_div])

/-- The t partial of the second field entry. -/
theorem hasDerivAt_rationalField_t_one (x y z t : ℝ) :
    HasDerivAt (fun t' => rationalField x y z t' 1)
      ((((((4 * Complex.I * ((z : ℂ) - (t : ℂ)) - 4) * betaXNumerator x y z t + alphaZNumerator x y z t * (-(4 * (t : ℂ)) + 4 * Complex.I)) - (4 * Complex.I * (x : ℂ) * betaZNumerator x y z t + alphaXNumerator x y z t * 0))) * complexDenominator x y z t -
        4 * ((-(2 * t : ℝ) : ℂ) + Complex.I * ((2 : ℝ) : ℂ)) *
          cross3 (alphaGradientNumerators x y z t) (betaGradientNumerators x y z t) 1) /
        complexDenominator x y z t ^ 5) t := by
  have h := hasDerivAt_field_of_sections (hasDerivAt_crossNumerators_t_one x y z t)
    (hasDerivAt_complexDenominator_t x y z t) (complex_denominator_ne_zero x y z t)
  exact h.congr_of_eventuallyEq (by
    filter_upwards with t'
    rw [rationalField_eq_cross_div])

/-- The x partial of the third field entry. -/
theorem hasDerivAt_rationalField_x_two (x y z t : ℝ) :
    HasDerivAt (fun x' => rationalField x' y z t 2)
      ((((4 * alphaCommonFactor z t * betaYNumerator x y z t + alphaXNumerator x y z t * (-(4 * ((y : ℝ) : ℂ)) - 4 * Complex.I * ((x : ℝ) : ℂ)) - (0 * betaXNumerator x y z t + alphaYNumerator x y z t * (-(4 * betaReducedNumerator x y))))) * complexDenominator x y z t -
        4 * ((2 * x : ℝ) : ℂ) *
          cross3 (alphaGradientNumerators x y z t) (betaGradientNumerators x y z t) 2) /
        complexDenominator x y z t ^ 5) x := by
  have h := hasDerivAt_field_of_sections (hasDerivAt_crossNumerators_x_two x y z t)
    (hasDerivAt_complexDenominator_x x y z t) (complex_denominator_ne_zero x y z t)
  exact h.congr_of_eventuallyEq (by
    filter_upwards with x'
    rw [rationalField_eq_cross_div])

/-- The y partial of the third field entry. -/
theorem hasDerivAt_rationalField_y_two (x y z t : ℝ) :
    HasDerivAt (fun y' => rationalField x y' z t 2)
      ((((0 * betaYNumerator x y z t + alphaXNumerator x y z t * (-(4 * betaReducedNumerator x y)) - (4 * alphaCommonFactor z t * betaXNumerator x y z t + alphaYNumerator x y z t * (4 * ((y : ℝ) : ℂ) + 4 * Complex.I * ((x : ℝ) : ℂ))))) * complexDenominator x y z t -
        4 * ((2 * y : ℝ) : ℂ) *
          cross3 (alphaGradientNumerators x y z t) (betaGradientNumerators x y z t) 2) /
        complexDenominator x y z t ^ 5) y := by
  have h := hasDerivAt_field_of_sections (hasDerivAt_crossNumerators_y_two x y z t)
    (hasDerivAt_complexDenominator_y x y z t) (complex_denominator_ne_zero x y z t)
  exact h.congr_of_eventuallyEq (by
    filter_upwards with y'
    rw [rationalField_eq_cross_div])

/-- The z partial of the third field entry. -/
theorem hasDerivAt_rationalField_z_two (x y z t : ℝ) :
    HasDerivAt (fun z' => rationalField x y z' t 2)
      ((((-(4 * Complex.I * ((x : ℝ) : ℂ)) * betaYNumerator x y z t + alphaXNumerator x y z t * (-(4 * Complex.I * ((z : ℝ) : ℂ))) - (-(4 * Complex.I * ((y : ℝ) : ℂ)) * betaXNumerator x y z t + alphaYNumerator x y z t * (4 * ((z : ℝ) : ℂ))))) * complexDenominator x y z t -
        4 * ((2 * z : ℝ) : ℂ) *
          cross3 (alphaGradientNumerators x y z t) (betaGradientNumerators x y z t) 2) /
        complexDenominator x y z t ^ 5) z := by
  have h := hasDerivAt_field_of_sections (hasDerivAt_crossNumerators_z_two x y z t)
    (hasDerivAt_complexDenominator_z x y z t) (complex_denominator_ne_zero x y z t)
  exact h.congr_of_eventuallyEq (by
    filter_upwards with z'
    rw [rationalField_eq_cross_div])

/-- The t partial of the third field entry. -/
theorem hasDerivAt_rationalField_t_two (x y z t : ℝ) :
    HasDerivAt (fun t' => rationalField x y z t' 2)
      (((((4 * Complex.I * (x : ℂ) * betaYNumerator x y z t + alphaXNumerator x y z t * (4 * Complex.I * (t : ℂ) + 4)) - (4 * Complex.I * (y : ℂ) * betaXNumerator x y z t + alphaYNumerator x y z t * (-(4 * (t : ℂ)) + 4 * Complex.I)))) * complexDenominator x y z t -
        4 * ((-(2 * t : ℝ) : ℂ) + Complex.I * ((2 : ℝ) : ℂ)) *
          cross3 (alphaGradientNumerators x y z t) (betaGradientNumerators x y z t) 2) /
        complexDenominator x y z t ^ 5) t := by
  have h := hasDerivAt_field_of_sections (hasDerivAt_crossNumerators_t_two x y z t)
    (hasDerivAt_complexDenominator_t x y z t) (complex_denominator_ne_zero x y z t)
  exact h.congr_of_eventuallyEq (by
    filter_upwards with t'
    rw [rationalField_eq_cross_div])

/-! ### The source-free Maxwell equations -/

/-- The curl of the rational field, entrywise as true derivative values. -/
noncomputable def fieldCurl (x y z t : ℝ) : Fin 3 → ℂ :=
  ![deriv (fun y' => rationalField x y' z t 2) y - deriv (fun z' => rationalField x y z' t 1) z,
    deriv (fun z' => rationalField x y z' t 0) z - deriv (fun x' => rationalField x' y z t 2) x,
    deriv (fun x' => rationalField x' y z t 1) x - deriv (fun y' => rationalField x y' z t 0) y]

/-- The time derivative of the rational field. -/
noncomputable def fieldTimeDeriv (x y z t : ℝ) : Fin 3 → ℂ :=
  fun j => deriv (fun t' => rationalField x y z t' j) t

/-- Source-free Maxwell equations in Riemann–Silberstein form: the curl of the
rational Bateman field equals `i` times its time derivative in every component. -/
theorem maxwell_rational_field (x y z t : ℝ) (j : Fin 3) :
    fieldCurl x y z t j = Complex.I * fieldTimeDeriv x y z t j := by
  have hw := complex_denominator_ne_zero x y z t
  have hw5 : complexDenominator x y z t ^ 5 ≠ 0 := pow_ne_zero 5 hw
  fin_cases j
  · show deriv (fun y' => rationalField x y' z t 2) y -
        deriv (fun z' => rationalField x y z' t 1) z =
      Complex.I * deriv (fun t' => rationalField x y z t' 0) t
    rw [(hasDerivAt_rationalField_y_two x y z t).deriv,
      (hasDerivAt_rationalField_z_one x y z t).deriv,
      (hasDerivAt_rationalField_t_zero x y z t).deriv]
    field_simp [hw5]
    apply Complex.ext <;>
      simp [alphaGradientNumerators, betaGradientNumerators,
        alphaXNumerator, alphaYNumerator, alphaZNumerator, betaXNumerator,
        betaYNumerator, betaZNumerator, alphaCommonFactor,
        betaReducedNumerator, complexDenominator, radialAux, cross3,
        Complex.mul_re, Complex.mul_im, Complex.add_re, Complex.add_im,
        Complex.sub_re, Complex.sub_im, Complex.neg_re, Complex.neg_im,
        Complex.ofReal_re, Complex.ofReal_im, -Complex.ofReal_pow,
        -Complex.ofReal_mul, -Complex.ofReal_add,
        ← Complex.ofReal_sub,
        ← Complex.ofReal_neg] <;>
      ring
  · show deriv (fun z' => rationalField x y z' t 0) z -
        deriv (fun x' => rationalField x' y z t 2) x =
      Complex.I * deriv (fun t' => rationalField x y z t' 1) t
    rw [(hasDerivAt_rationalField_z_zero x y z t).deriv,
      (hasDerivAt_rationalField_x_two x y z t).deriv,
      (hasDerivAt_rationalField_t_one x y z t).deriv]
    field_simp [hw5]
    apply Complex.ext <;>
      simp [alphaGradientNumerators, betaGradientNumerators,
        alphaXNumerator, alphaYNumerator, alphaZNumerator, betaXNumerator,
        betaYNumerator, betaZNumerator, alphaCommonFactor,
        betaReducedNumerator, complexDenominator, radialAux, cross3,
        Complex.mul_re, Complex.mul_im, Complex.add_re, Complex.add_im,
        Complex.sub_re, Complex.sub_im, Complex.neg_re, Complex.neg_im,
        Complex.ofReal_re, Complex.ofReal_im, -Complex.ofReal_pow,
        -Complex.ofReal_mul, -Complex.ofReal_add,
        ← Complex.ofReal_sub,
        ← Complex.ofReal_neg] <;>
      ring
  · show deriv (fun x' => rationalField x' y z t 1) x -
        deriv (fun y' => rationalField x y' z t 0) y =
      Complex.I * deriv (fun t' => rationalField x y z t' 2) t
    rw [(hasDerivAt_rationalField_x_one x y z t).deriv,
      (hasDerivAt_rationalField_y_zero x y z t).deriv,
      (hasDerivAt_rationalField_t_two x y z t).deriv]
    field_simp [hw5]
    apply Complex.ext <;>
      simp [alphaGradientNumerators, betaGradientNumerators,
        alphaXNumerator, alphaYNumerator, alphaZNumerator, betaXNumerator,
        betaYNumerator, betaZNumerator, alphaCommonFactor,
        betaReducedNumerator, complexDenominator, radialAux, cross3,
        Complex.mul_re, Complex.mul_im, Complex.add_re, Complex.add_im,
        Complex.sub_re, Complex.sub_im, Complex.neg_re, Complex.neg_im,
        Complex.ofReal_re, Complex.ofReal_im, -Complex.ofReal_pow,
        -Complex.ofReal_mul, -Complex.ofReal_add,
        -Complex.ofReal_sub, ← Complex.ofReal_neg] <;>
      ring

/-- The rational Bateman field is divergence-free at every space-time point. -/
theorem rational_field_divergence_free (x y z t : ℝ) :
    deriv (fun x' => rationalField x' y z t 0) x +
      deriv (fun y' => rationalField x y' z t 1) y +
      deriv (fun z' => rationalField x y z' t 2) z = 0 := by
  have hw := complex_denominator_ne_zero x y z t
  have hw5 : complexDenominator x y z t ^ 5 ≠ 0 := pow_ne_zero 5 hw
  rw [(hasDerivAt_rationalField_x_zero x y z t).deriv,
    (hasDerivAt_rationalField_y_one x y z t).deriv,
    (hasDerivAt_rationalField_z_two x y z t).deriv]
  field_simp [hw5]
  apply Complex.ext <;>
    simp [alphaGradientNumerators, betaGradientNumerators,
      alphaXNumerator, alphaYNumerator, alphaZNumerator, betaXNumerator,
      betaYNumerator, betaZNumerator, alphaCommonFactor,
      betaReducedNumerator, complexDenominator, radialAux, cross3,
      Complex.mul_re, Complex.mul_im, Complex.add_re, Complex.add_im,
      Complex.sub_re, Complex.sub_im, Complex.neg_re, Complex.neg_im,
      Complex.ofReal_re, Complex.ofReal_im, -Complex.ofReal_pow,
        -Complex.ofReal_mul, -Complex.ofReal_add,
      -Complex.ofReal_sub, ← Complex.ofReal_neg] <;>
    ring

end Qatlib.Papers.KnotLight13.TorusFamily
