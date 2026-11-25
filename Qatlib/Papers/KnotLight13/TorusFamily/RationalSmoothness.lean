/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Papers.KnotLight13.TorusFamily.RationalMaxwell
public import Mathlib.Analysis.Calculus.ContDiff.Operations

/-!
# Smoothness of the rational Bateman field

[Kedia2013TyingKnots], equation (6) and p150404-2,
[DOI](https://doi.org/10.1103/physrevlett.111.150404).
This module proves the regularity half of the paper's statement that the
Bateman field `F = ∇α × ∇β` of the explicit rational pair is a smooth
solution of the free Maxwell equations. Every field entry, as well as the
scalar potentials α and β themselves, is `C ^ ⊤` on all of real space-time:
each is a polynomial divided by a power of the common denominator, which
never vanishes. Complex inversion is smooth away from zero, which carries
the division through. Decay bounds, energy statements, field-line geometry,
helicity values, and topological statements are treated in the companion
module `Qatlib.Papers.KnotLight13.TorusFamily.RationalRegularity` or not
claimed at all.
-/

@[expose] public section
set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace Qatlib.Papers.KnotLight13.TorusFamily

open Qatlib.Papers.KnotLight13.TorusFamily (radialAux rationalAlpha rationalBeta
  pairDenominator pair_denominator_pos)
open Qatlib.Papers.KnottedLight08.HopfField (cross3 dot3)

/-! ### Smoothness of the coordinate sections -/

/-- The first (x) coordinate projection of space-time is smooth. -/
theorem contDiff_x_coord : ContDiff ℝ ⊤ (fun p : ℝ × ℝ × ℝ × ℝ => p.1) :=
  contDiff_fst

/-- The second (y) coordinate projection of space-time is smooth. -/
theorem contDiff_y_coord : ContDiff ℝ ⊤ (fun p : ℝ × ℝ × ℝ × ℝ => p.2.1) :=
  contDiff_fst.comp contDiff_snd

/-- The third (z) coordinate projection of space-time is smooth. -/
theorem contDiff_z_coord : ContDiff ℝ ⊤ (fun p : ℝ × ℝ × ℝ × ℝ => p.2.2.1) :=
  contDiff_fst.comp (contDiff_snd.comp contDiff_snd)

/-- The fourth (t) coordinate projection of space-time is smooth. -/
theorem contDiff_t_coord : ContDiff ℝ ⊤ (fun p : ℝ × ℝ × ℝ × ℝ => p.2.2.2) :=
  contDiff_snd.comp (contDiff_snd.comp contDiff_snd)

/-- A smooth real section followed by the real-to-complex coercion is smooth. -/
theorem contDiff_complex_ofReal_fun {f : ℝ × ℝ × ℝ × ℝ → ℝ} (hf : ContDiff ℝ ⊤ f) :
    ContDiff ℝ ⊤ (fun p => (f p : ℂ)) :=
  Complex.ofRealCLM.contDiff.comp hf

/-- A quotient of smooth complex-valued functions with everywhere-nonzero
denominator is smooth: complex inversion is smooth away from zero. -/
theorem contDiff_div_complex {f g : ℝ × ℝ × ℝ × ℝ → ℂ} (hf : ContDiff ℝ ⊤ f)
    (hg : ContDiff ℝ ⊤ g) (h : ∀ p, g p ≠ 0) :
    ContDiff ℝ ⊤ (fun p => f p / g p) := by
  have hinv : ContDiff ℝ ⊤ (fun p => (g p)⁻¹) := hg.inv h
  have hgen : ContDiff ℝ ⊤ (fun p => f p * (g p)⁻¹) := hf.mul hinv
  simpa only [div_eq_mul_inv] using hgen

/-- The auxiliary radius `A` is smooth as a function of space-time. -/
theorem contDiff_radialAux :
    ContDiff ℝ ⊤ (fun p : ℝ × ℝ × ℝ × ℝ => radialAux p.1 p.2.1 p.2.2.1 p.2.2.2) := by
  simp only [radialAux]
  exact ((((contDiff_x_coord.pow 2).add (contDiff_y_coord.pow 2)).add
    (contDiff_z_coord.pow 2)).sub (contDiff_t_coord.pow 2)).add contDiff_const

/-- The common complex denominator `w` is smooth as a function of space-time. -/
theorem contDiff_complexDenominator :
    ContDiff ℝ ⊤ (fun p : ℝ × ℝ × ℝ × ℝ =>
      complexDenominator p.1 p.2.1 p.2.2.1 p.2.2.2) := by
  simp only [complexDenominator]
  exact (contDiff_complex_ofReal_fun contDiff_radialAux).add
    (contDiff_const.mul (contDiff_complex_ofReal_fun
      (contDiff_const.mul contDiff_t_coord)))

/-- The common factor `g = 1 + i(t − z)` is smooth as a function of space-time. -/
theorem contDiff_alphaCommonFactor :
    ContDiff ℝ ⊤ (fun p : ℝ × ℝ × ℝ × ℝ =>
      alphaCommonFactor p.2.2.1 p.2.2.2) := by
  simp only [alphaCommonFactor]
  exact contDiff_const.add (contDiff_const.mul
    (contDiff_complex_ofReal_fun (contDiff_t_coord.sub contDiff_z_coord)))

/-- The reduced numerator `x − iy` of β is smooth as a function of space-time. -/
theorem contDiff_betaReducedNumerator :
    ContDiff ℝ ⊤ (fun p : ℝ × ℝ × ℝ × ℝ =>
      betaReducedNumerator p.1 p.2.1) := by
  simp only [betaReducedNumerator]
  exact (contDiff_complex_ofReal_fun contDiff_x_coord).sub
    (contDiff_const.mul (contDiff_complex_ofReal_fun contDiff_y_coord))

/-- The numerator of α is smooth as a function of space-time. -/
theorem contDiff_alphaNumerator :
    ContDiff ℝ ⊤ (fun p : ℝ × ℝ × ℝ × ℝ =>
      alphaNumerator p.1 p.2.1 p.2.2.1 p.2.2.2) := by
  simp only [alphaNumerator]
  exact (contDiff_complex_ofReal_fun
      (contDiff_radialAux.sub contDiff_const)).add
    (contDiff_const.mul (contDiff_complex_ofReal_fun
      (contDiff_const.mul contDiff_z_coord)))
/-- The numerator of `w² ∂ₓα` is smooth as a function of space-time. -/
theorem contDiff_alphaXNumerator :
    ContDiff ℝ ⊤ (fun p : ℝ × ℝ × ℝ × ℝ =>
      alphaXNumerator p.1 p.2.1 p.2.2.1 p.2.2.2) := by
  simp only [alphaXNumerator]
  exact (contDiff_const.mul (contDiff_complex_ofReal_fun contDiff_x_coord)).mul
    contDiff_alphaCommonFactor

/-- The numerator of `w² ∂_yα` is smooth as a function of space-time. -/
theorem contDiff_alphaYNumerator :
    ContDiff ℝ ⊤ (fun p : ℝ × ℝ × ℝ × ℝ =>
      alphaYNumerator p.1 p.2.1 p.2.2.1 p.2.2.2) := by
  simp only [alphaYNumerator]
  exact (contDiff_const.mul (contDiff_complex_ofReal_fun contDiff_y_coord)).mul
    contDiff_alphaCommonFactor

/-- The numerator of `w² ∂_zα` is smooth as a function of space-time. -/
theorem contDiff_alphaZNumerator :
    ContDiff ℝ ⊤ (fun p : ℝ × ℝ × ℝ × ℝ =>
      alphaZNumerator p.1 p.2.1 p.2.2.1 p.2.2.2) := by
  simp only [alphaZNumerator]
  exact ((contDiff_const.mul (contDiff_complex_ofReal_fun contDiff_z_coord)).mul
    contDiff_alphaCommonFactor).add
    ((contDiff_const.mul contDiff_const).mul contDiff_complexDenominator)

/-- The numerator of `w² ∂ₓβ` is smooth as a function of space-time. -/
theorem contDiff_betaXNumerator :
    ContDiff ℝ ⊤ (fun p : ℝ × ℝ × ℝ × ℝ =>
      betaXNumerator p.1 p.2.1 p.2.2.1 p.2.2.2) := by
  simp only [betaXNumerator]
  exact (contDiff_const.mul contDiff_complexDenominator).sub
    ((contDiff_const.mul (contDiff_complex_ofReal_fun contDiff_x_coord)).mul
      contDiff_betaReducedNumerator)

/-- The numerator of `w² ∂_yβ` is smooth as a function of space-time. -/
theorem contDiff_betaYNumerator :
    ContDiff ℝ ⊤ (fun p : ℝ × ℝ × ℝ × ℝ =>
      betaYNumerator p.1 p.2.1 p.2.2.1 p.2.2.2) := by
  simp only [betaYNumerator]
  exact ((contDiff_const.mul contDiff_const).mul contDiff_complexDenominator).neg.sub
    ((contDiff_const.mul (contDiff_complex_ofReal_fun contDiff_y_coord)).mul
      contDiff_betaReducedNumerator)

/-- The numerator of `w² ∂_zβ` is smooth as a function of space-time. -/
theorem contDiff_betaZNumerator :
    ContDiff ℝ ⊤ (fun p : ℝ × ℝ × ℝ × ℝ =>
      betaZNumerator p.1 p.2.1 p.2.2.1 p.2.2.2) := by
  simp only [betaZNumerator]
  exact ((contDiff_const.mul (contDiff_complex_ofReal_fun contDiff_z_coord)).mul
    contDiff_betaReducedNumerator).neg

/-- Every entry of the α-gradient numerator vector is smooth. -/
theorem contDiff_alphaGradientNumerators (j : Fin 3) :
    ContDiff ℝ ⊤ (fun p : ℝ × ℝ × ℝ × ℝ =>
      alphaGradientNumerators p.1 p.2.1 p.2.2.1 p.2.2.2 j) := by
  fin_cases j
  · simp only [alphaGradientNumerators]; exact contDiff_alphaXNumerator
  · simp only [alphaGradientNumerators]; exact contDiff_alphaYNumerator
  · simp only [alphaGradientNumerators]; exact contDiff_alphaZNumerator

/-- Every entry of the β-gradient numerator vector is smooth. -/
theorem contDiff_betaGradientNumerators (j : Fin 3) :
    ContDiff ℝ ⊤ (fun p : ℝ × ℝ × ℝ × ℝ =>
      betaGradientNumerators p.1 p.2.1 p.2.2.1 p.2.2.2 j) := by
  fin_cases j
  · simp only [betaGradientNumerators]; exact contDiff_betaXNumerator
  · simp only [betaGradientNumerators]; exact contDiff_betaYNumerator
  · simp only [betaGradientNumerators]; exact contDiff_betaZNumerator

/-- Every entry of the cross-product numerator of the field is smooth. -/
theorem contDiff_crossNumerators (j : Fin 3) :
    ContDiff ℝ ⊤ (fun p : ℝ × ℝ × ℝ × ℝ =>
      cross3 (alphaGradientNumerators p.1 p.2.1 p.2.2.1 p.2.2.2)
        (betaGradientNumerators p.1 p.2.1 p.2.2.1 p.2.2.2) j) := by
  fin_cases j
  · show ContDiff ℝ ⊤ (fun p : ℝ × ℝ × ℝ × ℝ =>
        alphaYNumerator p.1 p.2.1 p.2.2.1 p.2.2.2 * betaZNumerator p.1 p.2.1 p.2.2.1 p.2.2.2 -
        alphaZNumerator p.1 p.2.1 p.2.2.1 p.2.2.2 * betaYNumerator p.1 p.2.1 p.2.2.1 p.2.2.2)
    exact ((contDiff_alphaGradientNumerators 1).mul (contDiff_betaGradientNumerators 2)).sub
      ((contDiff_alphaGradientNumerators 2).mul (contDiff_betaGradientNumerators 1))
  · show ContDiff ℝ ⊤ (fun p : ℝ × ℝ × ℝ × ℝ =>
        alphaZNumerator p.1 p.2.1 p.2.2.1 p.2.2.2 * betaXNumerator p.1 p.2.1 p.2.2.1 p.2.2.2 -
        alphaXNumerator p.1 p.2.1 p.2.2.1 p.2.2.2 * betaZNumerator p.1 p.2.1 p.2.2.1 p.2.2.2)
    exact ((contDiff_alphaGradientNumerators 2).mul (contDiff_betaGradientNumerators 0)).sub
      ((contDiff_alphaGradientNumerators 0).mul (contDiff_betaGradientNumerators 2))
  · show ContDiff ℝ ⊤ (fun p : ℝ × ℝ × ℝ × ℝ =>
        alphaXNumerator p.1 p.2.1 p.2.2.1 p.2.2.2 * betaYNumerator p.1 p.2.1 p.2.2.1 p.2.2.2 -
        alphaYNumerator p.1 p.2.1 p.2.2.1 p.2.2.2 * betaXNumerator p.1 p.2.1 p.2.2.1 p.2.2.2)
    exact ((contDiff_alphaGradientNumerators 0).mul (contDiff_betaGradientNumerators 1)).sub
      ((contDiff_alphaGradientNumerators 1).mul (contDiff_betaGradientNumerators 0))

/-- The rational scalar α is smooth on all of real space-time. -/
theorem contDiff_rationalAlpha :
    ContDiff ℝ ⊤ (fun p : ℝ × ℝ × ℝ × ℝ =>
      rationalAlpha p.1 p.2.1 p.2.2.1 p.2.2.2) :=
  contDiff_div_complex contDiff_alphaNumerator contDiff_complexDenominator
    (fun p => complex_denominator_ne_zero p.1 p.2.1 p.2.2.1 p.2.2.2)

/-- The rational scalar β is smooth on all of real space-time. -/
theorem contDiff_rationalBeta :
    ContDiff ℝ ⊤ (fun p : ℝ × ℝ × ℝ × ℝ =>
      rationalBeta p.1 p.2.1 p.2.2.1 p.2.2.2) := by
  show ContDiff ℝ ⊤ (fun p : ℝ × ℝ × ℝ × ℝ =>
    ((2 : ℂ) * (p.1 : ℝ) - Complex.I * ((2 * p.2.1 : ℝ))) /
      complexDenominator p.1 p.2.1 p.2.2.1 p.2.2.2)
  exact contDiff_div_complex
    ((contDiff_const.mul (contDiff_complex_ofReal_fun contDiff_x_coord)).sub
      (contDiff_const.mul (contDiff_complex_ofReal_fun
        (contDiff_const.mul contDiff_y_coord)))) contDiff_complexDenominator
    (fun p => complex_denominator_ne_zero p.1 p.2.1 p.2.2.1 p.2.2.2)

/-- Every entry of the rational Bateman field is smooth on all of real
space-time: the field is a polynomial numerator over a power of the
never-vanishing common denominator. -/
theorem contDiff_rationalField (j : Fin 3) :
    ContDiff ℝ ⊤ (fun p : ℝ × ℝ × ℝ × ℝ =>
      rationalField p.1 p.2.1 p.2.2.1 p.2.2.2 j) := by
  have hden : ContDiff ℝ ⊤ (fun p : ℝ × ℝ × ℝ × ℝ =>
      complexDenominator p.1 p.2.1 p.2.2.1 p.2.2.2 ^ 4) := by
    simpa using contDiff_complexDenominator.pow 4
  have h := contDiff_div_complex (contDiff_crossNumerators j) hden
    (fun p => pow_ne_zero 4 (complex_denominator_ne_zero p.1 p.2.1 p.2.2.1 p.2.2.2))
  rw [contDiff_iff_contDiffAt]
  intro x'
  exact h.contDiffAt.congr_of_eventuallyEq
    (Filter.Eventually.of_forall fun q =>
      rationalField_eq_cross_div q.1 q.2.1 q.2.2.1 q.2.2.2 j)
