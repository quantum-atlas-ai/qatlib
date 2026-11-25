/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Mathlib.Basic.Complex.Basic
public import Mathlib.Data.Fin.VecNotation
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.NormNum
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Qatlib.Papers.KnottedLight08.HopfField.NullAlgebra
public import Qatlib.Papers.KnottedLight08.HopfField.RanadaScalars
public import Qatlib.Papers.KnottedLight08.HopfField.RanadaField

/-!
# The null invariants of the Rañada Hopf fields

[IrvineBouwmeester2008KnottedLight], p. 717,
[DOI](https://doi.org/10.1038/nphys1056).
The Hopf electromagnetic field of equation (2) satisfies the null condition
`E · B = 0` together with equal complex bilinear squares
`E · E = B · B` at every spacetime point; this is the pointwise algebraic
input for the conservation of field-line linking discussed on p. 717.

The proof follows the quaternionic rotation of the letter pattern: the real
part of the electric homogeneous numerator equals minus the imaginary part of
the magnetic one. Splitting `etaHomog = X + iY` and `zetaHomog = -Y + iW` with
real component vectors `X`, `Y`, `W`, the Binet-Cauchy identity reduces both
null statements to two real polynomial identities among the letter values and
their certified spatial gradients, `key_dot_identity` and
`key_norm_identity`, each proved by exact division by the defining relation
`2 * ranadaA = x^2 + y^2 + z^2 - t^2 + 1` of the letter `A` followed by
ring-normalization of the quotient. Linking-number conservation itself is a
global statement about field lines and is not claimed here.
-/

@[expose] public section
set_option autoImplicit false

namespace Qatlib.Papers.KnottedLight08.NullLinking

open Qatlib.Papers.KnottedLight08.HopfField (dot3 cross3)
open Qatlib.Papers.KnottedLight08.HopfField
open scoped ComplexConjugate

/-! ### Bilinear algebra helpers -/

/-- The Binet-Cauchy identity for the bilinear dot and cross products. -/
theorem dot3_cross3_cross3 {R : Type*} [CommRing R] (u v w s : Fin 3 → R) :
    dot3 (cross3 u v) (cross3 w s) =
      dot3 u w * dot3 v s - dot3 u s * dot3 v w := by
  simp only [dot3, cross3, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.tail_cons, Matrix.head_cons]
  ring

/-- The bilinear dot product is symmetric. -/
theorem dot3_comm {R : Type*} [CommRing R] (u v : Fin 3 → R) : dot3 u v = dot3 v u := by
  simp only [dot3]
  ring

/-- The dot product is homogeneous in its first argument. -/
theorem dot3_smul_left {R : Type*} [CommRing R] (c : R) (u v : Fin 3 → R) :
    dot3 (fun j => c * u j) v = c * dot3 u v := by
  simp only [dot3]
  ring

/-- The dot product is homogeneous in its second argument. -/
theorem dot3_smul_right {R : Type*} [CommRing R] (c : R) (u v : Fin 3 → R) :
    dot3 u (fun j => c * v j) = c * dot3 u v := by
  simp only [dot3]
  ring

/-- Negating the first argument negates the dot product. -/
theorem dot3_neg_left {R : Type*} [CommRing R] (u v : Fin 3 → R) :
    dot3 (fun j => -u j) v = -dot3 u v := by
  simp only [dot3]
  ring

/-- Negating the second argument negates the dot product. -/
theorem dot3_neg_right {R : Type*} [CommRing R] (u v : Fin 3 → R) :
    dot3 u (fun j => -v j) = -dot3 u v := by
  simp only [dot3]
  ring

/-- Conjugation passes through the bilinear dot product. -/
theorem dot3_conj (u v : Fin 3 → ℂ) :
    conj (dot3 u v) = dot3 (fun k => conj (u k)) (fun k => conj (v k)) := by
  simp only [dot3, conj_add', conj_mul']

/-- Conjugating only the first factor conjugates the pairing with a conjugated
second factor. -/
theorem dot3_conj_left (u v : Fin 3 → ℂ) :
    dot3 (fun k => conj (u k)) v = conj (dot3 u (fun k => conj (v k))) := by
  rw [dot3_conj]
  exact congrArg _ (funext fun k => (Complex.conj_conj (v k)).symm)

/-- The bilinear dot of two explicitly split complex vectors. -/
theorem dot3_split (a b c d : Fin 3 → ℝ) :
    dot3 (fun j => ((a j : ℝ) : ℂ) + Complex.I * ((b j : ℝ) : ℂ))
        (fun j => ((c j : ℝ) : ℂ) + Complex.I * ((d j : ℝ) : ℂ)) =
      ((dot3 a c - dot3 b d : ℝ) : ℂ) +
        Complex.I * ((dot3 a d + dot3 b c : ℝ) : ℂ) := by
  rw [Complex.ext_iff]
  constructor <;>
    simp only [dot3, Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im,
      Complex.I_re, Complex.I_im, Complex.ofReal_re, Complex.ofReal_im, add_zero, mul_zero,
      zero_mul, sub_zero] <;>
    ring

/-- The conjugate of an explicitly split complex number. -/
theorem conj_split (p q : ℝ) :
    conj (((p : ℝ) : ℂ) + Complex.I * ((q : ℝ) : ℂ)) =
      ((p : ℝ) : ℂ) - Complex.I * ((q : ℝ) : ℂ) := by
  simp only [conj_add', conj_mul', Complex.conj_ofReal, Complex.conj_I]
  ring

/-- The squared modulus of an explicitly split complex number. -/
theorem mul_conj_split (p q : ℝ) :
    (((p : ℝ) : ℂ) + Complex.I * ((q : ℝ) : ℂ)) *
        (((p : ℝ) : ℂ) - Complex.I * ((q : ℝ) : ℂ)) =
      ((p ^ 2 + q ^ 2 : ℝ) : ℂ) := by
  rw [Complex.ext_iff]
  constructor
  · simp only [Complex.add_re, Complex.add_im, Complex.sub_re, Complex.sub_im,
      Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im, Complex.ofReal_re,
      Complex.ofReal_im, mul_zero, zero_mul, one_mul, sub_self, sub_zero, zero_sub,
      add_zero]
    ring
  · simp only [Complex.add_re, Complex.add_im, Complex.sub_re, Complex.sub_im,
      Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im, Complex.ofReal_re,
      Complex.ofReal_im, mul_zero, zero_mul, one_mul, sub_self, sub_zero, zero_sub,
      add_zero]
    ring

/-! ### The real split of the homogeneous numerators -/

/-- Real part vector of the magnetic homogeneous numerator. -/
noncomputable def etaRePart (x y z t : ℝ) : Fin 3 → ℝ :=
  fun j => (etaHomog x y z t j).re

/-- Imaginary part vector of the magnetic homogeneous numerator. -/
noncomputable def etaImPart (x y z t : ℝ) : Fin 3 → ℝ :=
  fun j => (etaHomog x y z t j).im

/-- Imaginary part vector of the electric homogeneous numerator. -/
noncomputable def zetaImPart (x y z t : ℝ) : Fin 3 → ℝ :=
  fun j => (zetaHomog x y z t j).im


/-! ### Explicit letter components -/

/-- Cartesian component `0` of the real part of the
magnetic homogeneous numerator, as an explicit polynomial
in the letter `ranadaA` and the spacetime coordinates. -/
theorem etaRePart_zero (x y z t : ℝ) :
    etaRePart x y z t 0 =
    (2:ℝ) * ranadaA x y z t * t + z * t ^ 2 - (2:ℝ) * ranadaA x y z t ^ 2 * t - ranadaA x y z t ^ 2 * z + x * y * t ^ 2 + (2:ℝ) * ranadaA x y z t * x ^ 2 * t - ranadaA x y z t ^ 2 * x * y := by
  simp only [etaRePart, etaHomog, etaNumGrad, etaDenGrad, Matrix.cons_val_zero, etaNumX, etaDenX, etaNum, etaDen, ranadaP, ranadaQ, ranadaR, ranadaS, Complex.sub_re, Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im, Complex.ofReal_re, Complex.ofReal_im, add_zero, mul_zero, zero_mul, one_mul, sub_self]
  ring

/-- Cartesian component `1` of the real part of the
magnetic homogeneous numerator, as an explicit polynomial
in the letter `ranadaA` and the spacetime coordinates. -/
theorem etaRePart_one (x y z t : ℝ) :
    etaRePart x y z t 1 =
    t ^ 2 - ranadaA x y z t ^ 2 - ranadaA x y z t * t ^ 2 - (2:ℝ) * ranadaA x y z t * z * t + ranadaA x y z t ^ 3 + y ^ 2 * t ^ 2 + (2:ℝ) * ranadaA x y z t * x * y * t - ranadaA x y z t ^ 2 * y ^ 2 := by
  simp only [etaRePart, etaHomog, etaNumGrad, etaDenGrad, Matrix.cons_val_one, Matrix.cons_val_zero, etaNumY, etaDenY, etaNum, etaDen, ranadaP, ranadaQ, ranadaR, ranadaS, Complex.sub_re, Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im, Complex.ofReal_re, Complex.ofReal_im, add_zero, mul_zero, zero_mul, one_mul, sub_self]
  ring

/-- Cartesian component `2` of the real part of the
magnetic homogeneous numerator, as an explicit polynomial
in the letter `ranadaA` and the spacetime coordinates. -/
theorem etaRePart_two (x y z t : ℝ) :
    etaRePart x y z t 2 =
    -x * t ^ 2 + (2:ℝ) * ranadaA x y z t * y * t + ranadaA x y z t ^ 2 * x + y * z * t ^ 2 + (2:ℝ) * ranadaA x y z t * x * z * t - ranadaA x y z t ^ 2 * y * z := by
  simp only [etaRePart, etaHomog, etaNumGrad, etaDenGrad, Matrix.cons_val_two, Matrix.tail_cons, Matrix.head_cons, etaNumZ, etaDenZ, etaNum, etaDen, ranadaP, ranadaQ, ranadaR, ranadaS, Complex.sub_re, Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im, Complex.ofReal_re, Complex.ofReal_im, add_zero, mul_zero, zero_mul, one_mul, sub_self]
  ring

/-- Cartesian component `0` of the imaginary part of the
magnetic homogeneous numerator, as an explicit polynomial
in the letter `ranadaA` and the spacetime coordinates. -/
theorem etaImPart_zero (x y z t : ℝ) :
    etaImPart x y z t 0 =
    -x * t + y * t ^ 2 + (2:ℝ) * ranadaA x y z t * x * t + ranadaA x y z t ^ 2 * y - x * z * t ^ 2 - x * z ^ 2 * t - x * y ^ 2 * t - x ^ 3 * t - ranadaA x y z t ^ 2 * x * t - ranadaA x y z t ^ 2 * x * z := by
  simp only [etaImPart, etaHomog, etaNumGrad, etaDenGrad, Matrix.cons_val_zero, etaNumX, etaDenX, etaNum, etaDen, ranadaP, ranadaQ, ranadaR, ranadaS, Complex.sub_im, Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im, Complex.ofReal_re, Complex.ofReal_im, add_zero, mul_zero, zero_mul, one_mul, sub_self]
  ring

/-- Cartesian component `1` of the imaginary part of the
magnetic homogeneous numerator, as an explicit polynomial
in the letter `ranadaA` and the spacetime coordinates. -/
theorem etaImPart_one (x y z t : ℝ) :
    etaImPart x y z t 1 =
    -y * t - x * t ^ 2 + (2:ℝ) * ranadaA x y z t * y * t - ranadaA x y z t ^ 2 * x - y * z * t ^ 2 - y * z ^ 2 * t - y ^ 3 * t - x ^ 2 * y * t - ranadaA x y z t ^ 2 * y * t - ranadaA x y z t ^ 2 * y * z := by
  simp only [etaImPart, etaHomog, etaNumGrad, etaDenGrad, Matrix.cons_val_one, Matrix.cons_val_zero, etaNumY, etaDenY, etaNum, etaDen, ranadaP, ranadaQ, ranadaR, ranadaS, Complex.sub_im, Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im, Complex.ofReal_re, Complex.ofReal_im, add_zero, mul_zero, zero_mul, one_mul, sub_self]
  ring

/-- Cartesian component `2` of the imaginary part of the
magnetic homogeneous numerator, as an explicit polynomial
in the letter `ranadaA` and the spacetime coordinates. -/
theorem etaImPart_two (x y z t : ℝ) :
    etaImPart x y z t 2 =
    -t ^ 2 - z * t - ranadaA x y z t ^ 2 + ranadaA x y z t * t ^ 2 + (2:ℝ) * ranadaA x y z t * z * t + ranadaA x y z t ^ 3 - z ^ 2 * t ^ 2 - z ^ 3 * t - y ^ 2 * z * t - x ^ 2 * z * t - ranadaA x y z t ^ 2 * z * t - ranadaA x y z t ^ 2 * z ^ 2 := by
  simp only [etaImPart, etaHomog, etaNumGrad, etaDenGrad, Matrix.cons_val_two, Matrix.tail_cons, Matrix.head_cons, etaNumZ, etaDenZ, etaNum, etaDen, ranadaP, ranadaQ, ranadaR, ranadaS, Complex.sub_im, Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im, Complex.ofReal_re, Complex.ofReal_im, add_zero, mul_zero, zero_mul, one_mul, sub_self]
  ring

/-- Cartesian component `0` of the imaginary part of the
electric homogeneous numerator, as an explicit polynomial
in the letter `ranadaA` and the spacetime coordinates. -/
theorem zetaImPart_zero (x y z t : ℝ) :
    zetaImPart x y z t 0 =
    t ^ 2 - ranadaA x y z t ^ 2 - ranadaA x y z t * t ^ 2 - (2:ℝ) * ranadaA x y z t * z * t + ranadaA x y z t ^ 3 + x ^ 2 * t ^ 2 - (2:ℝ) * ranadaA x y z t * x * y * t - ranadaA x y z t ^ 2 * x ^ 2 := by
  simp only [zetaImPart, zetaHomog, zetaNumGrad, zetaDenGrad, Matrix.cons_val_zero, zetaNumX, zetaDenX, zetaNum, zetaDen, ranadaP, ranadaQ, ranadaR, ranadaS, Complex.sub_im, Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im, Complex.ofReal_re, Complex.ofReal_im, add_zero, mul_zero, zero_mul, one_mul, sub_self]
  ring

/-- Cartesian component `1` of the imaginary part of the
electric homogeneous numerator, as an explicit polynomial
in the letter `ranadaA` and the spacetime coordinates. -/
theorem zetaImPart_one (x y z t : ℝ) :
    zetaImPart x y z t 1 =
    -(2:ℝ) * ranadaA x y z t * t - z * t ^ 2 + (2:ℝ) * ranadaA x y z t ^ 2 * t + ranadaA x y z t ^ 2 * z + x * y * t ^ 2 - (2:ℝ) * ranadaA x y z t * y ^ 2 * t - ranadaA x y z t ^ 2 * x * y := by
  simp only [zetaImPart, zetaHomog, zetaNumGrad, zetaDenGrad, Matrix.cons_val_one, Matrix.cons_val_zero, zetaNumY, zetaDenY, zetaNum, zetaDen, ranadaP, ranadaQ, ranadaR, ranadaS, Complex.sub_im, Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im, Complex.ofReal_re, Complex.ofReal_im, add_zero, mul_zero, zero_mul, one_mul, sub_self]
  ring

/-- Cartesian component `2` of the imaginary part of the
electric homogeneous numerator, as an explicit polynomial
in the letter `ranadaA` and the spacetime coordinates. -/
theorem zetaImPart_two (x y z t : ℝ) :
    zetaImPart x y z t 2 =
    y * t ^ 2 + (2:ℝ) * ranadaA x y z t * x * t - ranadaA x y z t ^ 2 * y + x * z * t ^ 2 - (2:ℝ) * ranadaA x y z t * y * z * t - ranadaA x y z t ^ 2 * x * z := by
  simp only [zetaImPart, zetaHomog, zetaNumGrad, zetaDenGrad, Matrix.cons_val_two, Matrix.tail_cons, Matrix.head_cons, zetaNumZ, zetaDenZ, zetaNum, zetaDen, ranadaP, ranadaQ, ranadaR, ranadaS, Complex.sub_im, Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im, Complex.ofReal_re, Complex.ofReal_im, add_zero, mul_zero, zero_mul, one_mul, sub_self]
  ring


/-! ### The quaternionic rotation of the electric numerator -/

/-- Cartesian component `0` of the real part of the electric
homogeneous numerator, as an explicit polynomial in the letter `ranadaA`
and the spacetime coordinates. -/
theorem zetaHomog_re_zero (x y z t : ℝ) :
    (zetaHomog x y z t 0).re =
    x * t - y * t ^ 2 - (2:ℝ) * ranadaA x y z t * x * t - ranadaA x y z t ^ 2 * y + x * z * t ^ 2 + x * z ^ 2 * t + x * y ^ 2 * t + x ^ 3 * t + ranadaA x y z t ^ 2 * x * t + ranadaA x y z t ^ 2 * x * z := by
  simp only [zetaHomog, zetaNumGrad, zetaDenGrad, Matrix.cons_val_zero, zetaNumX, zetaDenX, zetaNum, zetaDen, ranadaP, ranadaQ, ranadaR, ranadaS, Complex.sub_re, Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im, Complex.ofReal_re, Complex.ofReal_im, add_zero, mul_zero, zero_mul, one_mul, sub_self]
  ring

/-- Cartesian component `1` of the real part of the electric
homogeneous numerator, as an explicit polynomial in the letter `ranadaA`
and the spacetime coordinates. -/
theorem zetaHomog_re_one (x y z t : ℝ) :
    (zetaHomog x y z t 1).re =
    y * t + x * t ^ 2 - (2:ℝ) * ranadaA x y z t * y * t + ranadaA x y z t ^ 2 * x + y * z * t ^ 2 + y * z ^ 2 * t + y ^ 3 * t + x ^ 2 * y * t + ranadaA x y z t ^ 2 * y * t + ranadaA x y z t ^ 2 * y * z := by
  simp only [zetaHomog, zetaNumGrad, zetaDenGrad, Matrix.cons_val_one, Matrix.cons_val_zero, zetaNumY, zetaDenY, zetaNum, zetaDen, ranadaP, ranadaQ, ranadaR, ranadaS, Complex.sub_re, Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im, Complex.ofReal_re, Complex.ofReal_im, add_zero, mul_zero, zero_mul, one_mul, sub_self]
  ring

/-- Cartesian component `2` of the real part of the electric
homogeneous numerator, as an explicit polynomial in the letter `ranadaA`
and the spacetime coordinates. -/
theorem zetaHomog_re_two (x y z t : ℝ) :
    (zetaHomog x y z t 2).re =
    t ^ 2 + z * t + ranadaA x y z t ^ 2 - ranadaA x y z t * t ^ 2 - (2:ℝ) * ranadaA x y z t * z * t - ranadaA x y z t ^ 3 + z ^ 2 * t ^ 2 + z ^ 3 * t + y ^ 2 * z * t + x ^ 2 * z * t + ranadaA x y z t ^ 2 * z * t + ranadaA x y z t ^ 2 * z ^ 2 := by
  simp only [zetaHomog, zetaNumGrad, zetaDenGrad, Matrix.cons_val_two, Matrix.tail_cons, Matrix.head_cons, zetaNumZ, zetaDenZ, zetaNum, zetaDen, ranadaP, ranadaQ, ranadaR, ranadaS, Complex.sub_re, Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im, Complex.ofReal_re, Complex.ofReal_im, add_zero, mul_zero, zero_mul, one_mul, sub_self]
  ring


/-- The electric homogeneous numerator has real part equal to minus the
magnetic imaginary part: this is the quaternionic rotation relating the two
letter charts. -/
theorem zetaHomog_re (x y z t : ℝ) (j : Fin 3) :
    (zetaHomog x y z t j).re = -(etaImPart x y z t j) := by
  fin_cases j
  · show (zetaHomog x y z t 0).re = -(etaImPart x y z t 0)
    rw [zetaHomog_re_zero, etaImPart_zero]
    ring
  · show (zetaHomog x y z t 1).re = -(etaImPart x y z t 1)
    rw [zetaHomog_re_one, etaImPart_one]
    ring
  · show (zetaHomog x y z t 2).re = -(etaImPart x y z t 2)
    rw [zetaHomog_re_two, etaImPart_two]
    ring

/-- The magnetic homogeneous numerator splits into real and imaginary parts. -/
theorem etaHomog_split (x y z t : ℝ) :
    (etaHomog x y z t) =
      fun j => ((etaRePart x y z t j : ℝ) : ℂ) +
        Complex.I * ((etaImPart x y z t j : ℝ) : ℂ) := by
  funext j
  rw [Complex.ext_iff]
  constructor
  · simp only [etaRePart, etaImPart, Complex.add_re, Complex.mul_re, Complex.I_re,
      Complex.I_im, Complex.ofReal_re, Complex.ofReal_im, mul_zero, zero_mul, sub_self,
      add_zero]
  · simp only [etaRePart, etaImPart, Complex.add_im, Complex.mul_im, Complex.I_re,
      Complex.I_im, Complex.ofReal_re, Complex.ofReal_im, mul_zero, one_mul, zero_add]

/-- The electric homogeneous numerator splits with rotated real part. -/
theorem zetaHomog_split (x y z t : ℝ) :
    (zetaHomog x y z t) =
      fun j => ((-(etaImPart x y z t j) : ℝ) : ℂ) +
        Complex.I * ((zetaImPart x y z t j : ℝ) : ℂ) := by
  funext j
  rw [Complex.ext_iff]
  constructor
  · rw [zetaHomog_re]
    simp only [Complex.add_re, Complex.mul_re, Complex.I_re, Complex.I_im,
      Complex.ofReal_re, Complex.ofReal_im, mul_zero, zero_mul, sub_self, add_zero]
  · rw [show (zetaHomog x y z t j).im = zetaImPart x y z t j from by
      simp only [zetaImPart]]
    simp only [Complex.add_im, Complex.mul_im, Complex.I_re, Complex.I_im,
      Complex.ofReal_re, Complex.ofReal_im, mul_zero, one_mul, zero_add]

/-- The conjugate of the magnetic homogeneous numerator, split. -/
theorem etaHomog_conj_split (x y z t : ℝ) :
    (fun k => conj (etaHomog x y z t k)) =
      fun k => ((etaRePart x y z t k : ℝ) : ℂ) +
        Complex.I * ((-(etaImPart x y z t k) : ℝ) : ℂ) := by
  funext k
  rw [congrFun (etaHomog_split x y z t) k, conj_split, Complex.ofReal_neg]
  ring

/-- Both letter pairs have the same total squared modulus. -/
theorem zetaSumSq_eq_etaSumSq (x y z t : ℝ) :
    zetaSumSq x y z t = etaSumSq x y z t := by
  simp only [etaSumSq, zetaSumSq, etaNum, etaDen, zetaNum, zetaDen, conj_split]
  rw [Complex.ext_iff]
  constructor
  · simp only [Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im,
      Complex.sub_re, Complex.sub_im, Complex.I_re, Complex.I_im, Complex.ofReal_re,
      Complex.ofReal_im, mul_zero, zero_mul, one_mul, sub_self, sub_zero, zero_sub,
      add_zero]
    ring
  · simp only [Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im,
      Complex.sub_re, Complex.sub_im, Complex.I_re, Complex.I_im, Complex.ofReal_re,
      Complex.ofReal_im, mul_zero, zero_mul, one_mul, sub_self, sub_zero, zero_sub,
      add_zero]
    ring


/-! ### The two real polynomial identities -/

/-- The letter identity `2 * ranadaA = x^2 + y^2 + z^2 - t^2 + 1`, which is the
only relation between the letter values needed beyond their definitions. -/
theorem two_ranadaA (x y z t : ℝ) :
    (2:ℝ) * ranadaA x y z t - (x ^ 2 + y ^ 2 + z ^ 2 - t ^ 2 + 1) = 0 := by
  have hr : ranadaA x y z t = (x ^ 2 + y ^ 2 + z ^ 2 - t ^ 2 + 1) / 2 := rfl
  rw [hr]
  field_simp
  ring


set_option maxRecDepth 20000 in
/-- First quaternionic identity: `|Y|² (X · W) = (X · Y)(Y · W)` for the
split vectors of the two homogeneous numerators. It is proved by exact division
of the expanded polynomial by the defining relation of `ranadaA`. -/
theorem key_dot_identity (x y z t : ℝ) :
    dot3 (etaImPart x y z t) (etaImPart x y z t) *
        dot3 (etaRePart x y z t) (zetaImPart x y z t) =
      dot3 (etaRePart x y z t) (etaImPart x y z t) *
        dot3 (etaImPart x y z t) (zetaImPart x y z t) := by
  have hA := two_ranadaA x y z t
  simp only [dot3, etaRePart_zero, etaRePart_one, etaRePart_two, etaImPart_zero,
    etaImPart_one, etaImPart_two, zetaImPart_zero, zetaImPart_one, zetaImPart_two]
  linear_combination (x * y * t ^ 6 - (2:ℝ) * ranadaA x y z t * y ^ 2 * t ^ 5 + (2:ℝ) * ranadaA x y z t * x ^ 2 * t ^ 5 - (6:ℝ) * ranadaA x y z t ^ 2 * x * y * t ^ 4 + (2:ℝ) * ranadaA x y z t ^ 3 * y ^ 2 * t ^ 3 - (2:ℝ) * ranadaA x y z t ^ 3 * x ^ 2 * t ^ 3 + ranadaA x y z t ^ 4 * x * y * t ^ 2 - (4:ℝ) * ranadaA x y z t * x * y * t ^ 6 + (8:ℝ) * ranadaA x y z t ^ 2 * y ^ 2 * t ^ 5 - (8:ℝ) * ranadaA x y z t ^ 2 * x ^ 2 * t ^ 5 + (24:ℝ) * ranadaA x y z t ^ 3 * x * y * t ^ 4 - (8:ℝ) * ranadaA x y z t ^ 4 * y ^ 2 * t ^ 3 + (8:ℝ) * ranadaA x y z t ^ 4 * x ^ 2 * t ^ 3 - (4:ℝ) * ranadaA x y z t ^ 5 * x * y * t ^ 2 + (2:ℝ) * x * y * z ^ 2 * t ^ 6 + (2:ℝ) * x * y ^ 3 * t ^ 6 + (2:ℝ) * x ^ 3 * y * t ^ 6 - (4:ℝ) * ranadaA x y z t * y ^ 2 * z ^ 2 * t ^ 5 - (4:ℝ) * ranadaA x y z t * y ^ 4 * t ^ 5 + (4:ℝ) * ranadaA x y z t * x ^ 2 * z ^ 2 * t ^ 5 + (4:ℝ) * ranadaA x y z t * x ^ 4 * t ^ 5 + (5:ℝ) * ranadaA x y z t ^ 2 * x * y * t ^ 6 - (12:ℝ) * ranadaA x y z t ^ 2 * x * y * z ^ 2 * t ^ 4 - (12:ℝ) * ranadaA x y z t ^ 2 * x * y ^ 3 * t ^ 4 - (12:ℝ) * ranadaA x y z t ^ 2 * x ^ 3 * y * t ^ 4 - (10:ℝ) * ranadaA x y z t ^ 3 * y ^ 2 * t ^ 5 + (4:ℝ) * ranadaA x y z t ^ 3 * y ^ 2 * z ^ 2 * t ^ 3 + (4:ℝ) * ranadaA x y z t ^ 3 * y ^ 4 * t ^ 3 + (10:ℝ) * ranadaA x y z t ^ 3 * x ^ 2 * t ^ 5 - (4:ℝ) * ranadaA x y z t ^ 3 * x ^ 2 * z ^ 2 * t ^ 3 - (4:ℝ) * ranadaA x y z t ^ 3 * x ^ 4 * t ^ 3 - (31:ℝ) * ranadaA x y z t ^ 4 * x * y * t ^ 4 + (2:ℝ) * ranadaA x y z t ^ 4 * x * y * z ^ 2 * t ^ 2 + (2:ℝ) * ranadaA x y z t ^ 4 * x * y ^ 3 * t ^ 2 + (2:ℝ) * ranadaA x y z t ^ 4 * x ^ 3 * y * t ^ 2 + (12:ℝ) * ranadaA x y z t ^ 5 * y ^ 2 * t ^ 3 - (12:ℝ) * ranadaA x y z t ^ 5 * x ^ 2 * t ^ 3 + (11:ℝ) * ranadaA x y z t ^ 6 * x * y * t ^ 2 - (2:ℝ) * ranadaA x y z t ^ 7 * y ^ 2 * t + (2:ℝ) * ranadaA x y z t ^ 7 * x ^ 2 * t - ranadaA x y z t ^ 8 * x * y - (4:ℝ) * ranadaA x y z t * x * y * z ^ 2 * t ^ 6 - (4:ℝ) * ranadaA x y z t * x * y ^ 3 * t ^ 6 - (4:ℝ) * ranadaA x y z t * x ^ 3 * y * t ^ 6 + (8:ℝ) * ranadaA x y z t ^ 2 * y ^ 2 * z ^ 2 * t ^ 5 + (8:ℝ) * ranadaA x y z t ^ 2 * y ^ 4 * t ^ 5 - (8:ℝ) * ranadaA x y z t ^ 2 * x ^ 2 * z ^ 2 * t ^ 5 - (8:ℝ) * ranadaA x y z t ^ 2 * x ^ 4 * t ^ 5 - (2:ℝ) * ranadaA x y z t ^ 3 * x * y * t ^ 6 + (24:ℝ) * ranadaA x y z t ^ 3 * x * y * z ^ 2 * t ^ 4 + (24:ℝ) * ranadaA x y z t ^ 3 * x * y ^ 3 * t ^ 4 + (24:ℝ) * ranadaA x y z t ^ 3 * x ^ 3 * y * t ^ 4 + (4:ℝ) * ranadaA x y z t ^ 4 * y ^ 2 * t ^ 5 - (8:ℝ) * ranadaA x y z t ^ 4 * y ^ 2 * z ^ 2 * t ^ 3 - (8:ℝ) * ranadaA x y z t ^ 4 * y ^ 4 * t ^ 3 - (4:ℝ) * ranadaA x y z t ^ 4 * x ^ 2 * t ^ 5 + (8:ℝ) * ranadaA x y z t ^ 4 * x ^ 2 * z ^ 2 * t ^ 3 + (8:ℝ) * ranadaA x y z t ^ 4 * x ^ 4 * t ^ 3 + (14:ℝ) * ranadaA x y z t ^ 5 * x * y * t ^ 4 - (4:ℝ) * ranadaA x y z t ^ 5 * x * y * z ^ 2 * t ^ 2 - (4:ℝ) * ranadaA x y z t ^ 5 * x * y ^ 3 * t ^ 2 - (4:ℝ) * ranadaA x y z t ^ 5 * x ^ 3 * y * t ^ 2 - (8:ℝ) * ranadaA x y z t ^ 6 * y ^ 2 * t ^ 3 + (8:ℝ) * ranadaA x y z t ^ 6 * x ^ 2 * t ^ 3 - (14:ℝ) * ranadaA x y z t ^ 7 * x * y * t ^ 2 + (4:ℝ) * ranadaA x y z t ^ 8 * y ^ 2 * t - (4:ℝ) * ranadaA x y z t ^ 8 * x ^ 2 * t + (2:ℝ) * ranadaA x y z t ^ 9 * x * y + x * y * z ^ 4 * t ^ 6 + (2:ℝ) * x * y ^ 3 * z ^ 2 * t ^ 6 + x * y ^ 5 * t ^ 6 + (2:ℝ) * x ^ 3 * y * z ^ 2 * t ^ 6 + (2:ℝ) * x ^ 3 * y ^ 3 * t ^ 6 + x ^ 5 * y * t ^ 6 - (2:ℝ) * ranadaA x y z t * y ^ 2 * z ^ 4 * t ^ 5 - (4:ℝ) * ranadaA x y z t * y ^ 4 * z ^ 2 * t ^ 5 - (2:ℝ) * ranadaA x y z t * y ^ 6 * t ^ 5 + (2:ℝ) * ranadaA x y z t * x ^ 2 * z ^ 4 * t ^ 5 - (2:ℝ) * ranadaA x y z t * x ^ 2 * y ^ 4 * t ^ 5 + (4:ℝ) * ranadaA x y z t * x ^ 4 * z ^ 2 * t ^ 5 + (2:ℝ) * ranadaA x y z t * x ^ 4 * y ^ 2 * t ^ 5 + (2:ℝ) * ranadaA x y z t * x ^ 6 * t ^ 5 + ranadaA x y z t ^ 2 * x * y * z ^ 2 * t ^ 6 - (6:ℝ) * ranadaA x y z t ^ 2 * x * y * z ^ 4 * t ^ 4 + ranadaA x y z t ^ 2 * x * y ^ 3 * t ^ 6 - (12:ℝ) * ranadaA x y z t ^ 2 * x * y ^ 3 * z ^ 2 * t ^ 4 - (6:ℝ) * ranadaA x y z t ^ 2 * x * y ^ 5 * t ^ 4 + ranadaA x y z t ^ 2 * x ^ 3 * y * t ^ 6 - (12:ℝ) * ranadaA x y z t ^ 2 * x ^ 3 * y * z ^ 2 * t ^ 4 - (12:ℝ) * ranadaA x y z t ^ 2 * x ^ 3 * y ^ 3 * t ^ 4 - (6:ℝ) * ranadaA x y z t ^ 2 * x ^ 5 * y * t ^ 4 - (2:ℝ) * ranadaA x y z t ^ 3 * y ^ 2 * z ^ 2 * t ^ 5 + (2:ℝ) * ranadaA x y z t ^ 3 * y ^ 2 * z ^ 4 * t ^ 3 - (2:ℝ) * ranadaA x y z t ^ 3 * y ^ 4 * t ^ 5 + (4:ℝ) * ranadaA x y z t ^ 3 * y ^ 4 * z ^ 2 * t ^ 3 + (2:ℝ) * ranadaA x y z t ^ 3 * y ^ 6 * t ^ 3 + (2:ℝ) * ranadaA x y z t ^ 3 * x ^ 2 * z ^ 2 * t ^ 5 - (2:ℝ) * ranadaA x y z t ^ 3 * x ^ 2 * z ^ 4 * t ^ 3 + (2:ℝ) * ranadaA x y z t ^ 3 * x ^ 2 * y ^ 4 * t ^ 3 + (2:ℝ) * ranadaA x y z t ^ 3 * x ^ 4 * t ^ 5 - (4:ℝ) * ranadaA x y z t ^ 3 * x ^ 4 * z ^ 2 * t ^ 3 - (2:ℝ) * ranadaA x y z t ^ 3 * x ^ 4 * y ^ 2 * t ^ 3 - (2:ℝ) * ranadaA x y z t ^ 3 * x ^ 6 * t ^ 3 - (7:ℝ) * ranadaA x y z t ^ 4 * x * y * z ^ 2 * t ^ 4 + ranadaA x y z t ^ 4 * x * y * z ^ 4 * t ^ 2 - (7:ℝ) * ranadaA x y z t ^ 4 * x * y ^ 3 * t ^ 4 + (2:ℝ) * ranadaA x y z t ^ 4 * x * y ^ 3 * z ^ 2 * t ^ 2 + ranadaA x y z t ^ 4 * x * y ^ 5 * t ^ 2 - (7:ℝ) * ranadaA x y z t ^ 4 * x ^ 3 * y * t ^ 4 + (2:ℝ) * ranadaA x y z t ^ 4 * x ^ 3 * y * z ^ 2 * t ^ 2 + (2:ℝ) * ranadaA x y z t ^ 4 * x ^ 3 * y ^ 3 * t ^ 2 + ranadaA x y z t ^ 4 * x ^ 5 * y * t ^ 2 + (4:ℝ) * ranadaA x y z t ^ 5 * y ^ 2 * z ^ 2 * t ^ 3 + (4:ℝ) * ranadaA x y z t ^ 5 * y ^ 4 * t ^ 3 - (4:ℝ) * ranadaA x y z t ^ 5 * x ^ 2 * z ^ 2 * t ^ 3 - (4:ℝ) * ranadaA x y z t ^ 5 * x ^ 4 * t ^ 3 - ranadaA x y z t ^ 6 * x * y * t ^ 4 + (7:ℝ) * ranadaA x y z t ^ 6 * x * y * z ^ 2 * t ^ 2 + (7:ℝ) * ranadaA x y z t ^ 6 * x * y ^ 3 * t ^ 2 + (7:ℝ) * ranadaA x y z t ^ 6 * x ^ 3 * y * t ^ 2 + (2:ℝ) * ranadaA x y z t ^ 7 * y ^ 2 * t ^ 3 - (2:ℝ) * ranadaA x y z t ^ 7 * y ^ 2 * z ^ 2 * t - (2:ℝ) * ranadaA x y z t ^ 7 * y ^ 4 * t - (2:ℝ) * ranadaA x y z t ^ 7 * x ^ 2 * t ^ 3 + (2:ℝ) * ranadaA x y z t ^ 7 * x ^ 2 * z ^ 2 * t + (2:ℝ) * ranadaA x y z t ^ 7 * x ^ 4 * t + (6:ℝ) * ranadaA x y z t ^ 8 * x * y * t ^ 2 - ranadaA x y z t ^ 8 * x * y * z ^ 2 - ranadaA x y z t ^ 8 * x * y ^ 3 - ranadaA x y z t ^ 8 * x ^ 3 * y - (2:ℝ) * ranadaA x y z t ^ 9 * y ^ 2 * t + (2:ℝ) * ranadaA x y z t ^ 9 * x ^ 2 * t - ranadaA x y z t ^ 10 * x * y) * hA

set_option maxRecDepth 20000 in
/-- Second quaternionic identity balancing squared norms and projections of
the split vectors, again by exact division by the defining relation of
`ranadaA`. -/
theorem key_norm_identity (x y z t : ℝ) :
    dot3 (etaImPart x y z t) (etaImPart x y z t) *
        (dot3 (zetaImPart x y z t) (zetaImPart x y z t) -
          dot3 (etaRePart x y z t) (etaRePart x y z t)) =
      dot3 (etaImPart x y z t) (zetaImPart x y z t) *
          dot3 (etaImPart x y z t) (zetaImPart x y z t) -
        dot3 (etaRePart x y z t) (etaImPart x y z t) *
        dot3 (etaRePart x y z t) (etaImPart x y z t) := by
  have hA := two_ranadaA x y z t
  simp only [dot3, etaRePart_zero, etaRePart_one, etaRePart_two, etaImPart_zero,
    etaImPart_one, etaImPart_two, zetaImPart_zero, zetaImPart_one, zetaImPart_two]
  linear_combination (-y ^ 2 * t ^ 6 + x ^ 2 * t ^ 6 - (8:ℝ) * ranadaA x y z t * x * y * t ^ 5 + (6:ℝ) * ranadaA x y z t ^ 2 * y ^ 2 * t ^ 4 - (6:ℝ) * ranadaA x y z t ^ 2 * x ^ 2 * t ^ 4 + (8:ℝ) * ranadaA x y z t ^ 3 * x * y * t ^ 3 - ranadaA x y z t ^ 4 * y ^ 2 * t ^ 2 + ranadaA x y z t ^ 4 * x ^ 2 * t ^ 2 + (4:ℝ) * ranadaA x y z t * y ^ 2 * t ^ 6 - (4:ℝ) * ranadaA x y z t * x ^ 2 * t ^ 6 + (32:ℝ) * ranadaA x y z t ^ 2 * x * y * t ^ 5 - (24:ℝ) * ranadaA x y z t ^ 3 * y ^ 2 * t ^ 4 + (24:ℝ) * ranadaA x y z t ^ 3 * x ^ 2 * t ^ 4 - (32:ℝ) * ranadaA x y z t ^ 4 * x * y * t ^ 3 + (4:ℝ) * ranadaA x y z t ^ 5 * y ^ 2 * t ^ 2 - (4:ℝ) * ranadaA x y z t ^ 5 * x ^ 2 * t ^ 2 - (2:ℝ) * y ^ 2 * z ^ 2 * t ^ 6 - (2:ℝ) * y ^ 4 * t ^ 6 + (2:ℝ) * x ^ 2 * z ^ 2 * t ^ 6 + (2:ℝ) * x ^ 4 * t ^ 6 - (16:ℝ) * ranadaA x y z t * x * y * z ^ 2 * t ^ 5 - (16:ℝ) * ranadaA x y z t * x * y ^ 3 * t ^ 5 - (16:ℝ) * ranadaA x y z t * x ^ 3 * y * t ^ 5 - (5:ℝ) * ranadaA x y z t ^ 2 * y ^ 2 * t ^ 6 + (12:ℝ) * ranadaA x y z t ^ 2 * y ^ 2 * z ^ 2 * t ^ 4 + (12:ℝ) * ranadaA x y z t ^ 2 * y ^ 4 * t ^ 4 + (5:ℝ) * ranadaA x y z t ^ 2 * x ^ 2 * t ^ 6 - (12:ℝ) * ranadaA x y z t ^ 2 * x ^ 2 * z ^ 2 * t ^ 4 - (12:ℝ) * ranadaA x y z t ^ 2 * x ^ 4 * t ^ 4 - (40:ℝ) * ranadaA x y z t ^ 3 * x * y * t ^ 5 + (16:ℝ) * ranadaA x y z t ^ 3 * x * y * z ^ 2 * t ^ 3 + (16:ℝ) * ranadaA x y z t ^ 3 * x * y ^ 3 * t ^ 3 + (16:ℝ) * ranadaA x y z t ^ 3 * x ^ 3 * y * t ^ 3 + (31:ℝ) * ranadaA x y z t ^ 4 * y ^ 2 * t ^ 4 - (2:ℝ) * ranadaA x y z t ^ 4 * y ^ 2 * z ^ 2 * t ^ 2 - (2:ℝ) * ranadaA x y z t ^ 4 * y ^ 4 * t ^ 2 - (31:ℝ) * ranadaA x y z t ^ 4 * x ^ 2 * t ^ 4 + (2:ℝ) * ranadaA x y z t ^ 4 * x ^ 2 * z ^ 2 * t ^ 2 + (2:ℝ) * ranadaA x y z t ^ 4 * x ^ 4 * t ^ 2 + (48:ℝ) * ranadaA x y z t ^ 5 * x * y * t ^ 3 - (11:ℝ) * ranadaA x y z t ^ 6 * y ^ 2 * t ^ 2 + (11:ℝ) * ranadaA x y z t ^ 6 * x ^ 2 * t ^ 2 - (8:ℝ) * ranadaA x y z t ^ 7 * x * y * t + ranadaA x y z t ^ 8 * y ^ 2 - ranadaA x y z t ^ 8 * x ^ 2 + (4:ℝ) * ranadaA x y z t * y ^ 2 * z ^ 2 * t ^ 6 + (4:ℝ) * ranadaA x y z t * y ^ 4 * t ^ 6 - (4:ℝ) * ranadaA x y z t * x ^ 2 * z ^ 2 * t ^ 6 - (4:ℝ) * ranadaA x y z t * x ^ 4 * t ^ 6 + (32:ℝ) * ranadaA x y z t ^ 2 * x * y * z ^ 2 * t ^ 5 + (32:ℝ) * ranadaA x y z t ^ 2 * x * y ^ 3 * t ^ 5 + (32:ℝ) * ranadaA x y z t ^ 2 * x ^ 3 * y * t ^ 5 + (2:ℝ) * ranadaA x y z t ^ 3 * y ^ 2 * t ^ 6 - (24:ℝ) * ranadaA x y z t ^ 3 * y ^ 2 * z ^ 2 * t ^ 4 - (24:ℝ) * ranadaA x y z t ^ 3 * y ^ 4 * t ^ 4 - (2:ℝ) * ranadaA x y z t ^ 3 * x ^ 2 * t ^ 6 + (24:ℝ) * ranadaA x y z t ^ 3 * x ^ 2 * z ^ 2 * t ^ 4 + (24:ℝ) * ranadaA x y z t ^ 3 * x ^ 4 * t ^ 4 + (16:ℝ) * ranadaA x y z t ^ 4 * x * y * t ^ 5 - (32:ℝ) * ranadaA x y z t ^ 4 * x * y * z ^ 2 * t ^ 3 - (32:ℝ) * ranadaA x y z t ^ 4 * x * y ^ 3 * t ^ 3 - (32:ℝ) * ranadaA x y z t ^ 4 * x ^ 3 * y * t ^ 3 - (14:ℝ) * ranadaA x y z t ^ 5 * y ^ 2 * t ^ 4 + (4:ℝ) * ranadaA x y z t ^ 5 * y ^ 2 * z ^ 2 * t ^ 2 + (4:ℝ) * ranadaA x y z t ^ 5 * y ^ 4 * t ^ 2 + (14:ℝ) * ranadaA x y z t ^ 5 * x ^ 2 * t ^ 4 - (4:ℝ) * ranadaA x y z t ^ 5 * x ^ 2 * z ^ 2 * t ^ 2 - (4:ℝ) * ranadaA x y z t ^ 5 * x ^ 4 * t ^ 2 - (32:ℝ) * ranadaA x y z t ^ 6 * x * y * t ^ 3 + (14:ℝ) * ranadaA x y z t ^ 7 * y ^ 2 * t ^ 2 - (14:ℝ) * ranadaA x y z t ^ 7 * x ^ 2 * t ^ 2 + (16:ℝ) * ranadaA x y z t ^ 8 * x * y * t - (2:ℝ) * ranadaA x y z t ^ 9 * y ^ 2 + (2:ℝ) * ranadaA x y z t ^ 9 * x ^ 2 - y ^ 2 * z ^ 4 * t ^ 6 - (2:ℝ) * y ^ 4 * z ^ 2 * t ^ 6 - y ^ 6 * t ^ 6 + x ^ 2 * z ^ 4 * t ^ 6 - x ^ 2 * y ^ 4 * t ^ 6 + (2:ℝ) * x ^ 4 * z ^ 2 * t ^ 6 + x ^ 4 * y ^ 2 * t ^ 6 + x ^ 6 * t ^ 6 - (8:ℝ) * ranadaA x y z t * x * y * z ^ 4 * t ^ 5 - (16:ℝ) * ranadaA x y z t * x * y ^ 3 * z ^ 2 * t ^ 5 - (8:ℝ) * ranadaA x y z t * x * y ^ 5 * t ^ 5 - (16:ℝ) * ranadaA x y z t * x ^ 3 * y * z ^ 2 * t ^ 5 - (16:ℝ) * ranadaA x y z t * x ^ 3 * y ^ 3 * t ^ 5 - (8:ℝ) * ranadaA x y z t * x ^ 5 * y * t ^ 5 - ranadaA x y z t ^ 2 * y ^ 2 * z ^ 2 * t ^ 6 + (6:ℝ) * ranadaA x y z t ^ 2 * y ^ 2 * z ^ 4 * t ^ 4 - ranadaA x y z t ^ 2 * y ^ 4 * t ^ 6 + (12:ℝ) * ranadaA x y z t ^ 2 * y ^ 4 * z ^ 2 * t ^ 4 + (6:ℝ) * ranadaA x y z t ^ 2 * y ^ 6 * t ^ 4 + ranadaA x y z t ^ 2 * x ^ 2 * z ^ 2 * t ^ 6 - (6:ℝ) * ranadaA x y z t ^ 2 * x ^ 2 * z ^ 4 * t ^ 4 + (6:ℝ) * ranadaA x y z t ^ 2 * x ^ 2 * y ^ 4 * t ^ 4 + ranadaA x y z t ^ 2 * x ^ 4 * t ^ 6 - (12:ℝ) * ranadaA x y z t ^ 2 * x ^ 4 * z ^ 2 * t ^ 4 - (6:ℝ) * ranadaA x y z t ^ 2 * x ^ 4 * y ^ 2 * t ^ 4 - (6:ℝ) * ranadaA x y z t ^ 2 * x ^ 6 * t ^ 4 - (8:ℝ) * ranadaA x y z t ^ 3 * x * y * z ^ 2 * t ^ 5 + (8:ℝ) * ranadaA x y z t ^ 3 * x * y * z ^ 4 * t ^ 3 - (8:ℝ) * ranadaA x y z t ^ 3 * x * y ^ 3 * t ^ 5 + (16:ℝ) * ranadaA x y z t ^ 3 * x * y ^ 3 * z ^ 2 * t ^ 3 + (8:ℝ) * ranadaA x y z t ^ 3 * x * y ^ 5 * t ^ 3 - (8:ℝ) * ranadaA x y z t ^ 3 * x ^ 3 * y * t ^ 5 + (16:ℝ) * ranadaA x y z t ^ 3 * x ^ 3 * y * z ^ 2 * t ^ 3 + (16:ℝ) * ranadaA x y z t ^ 3 * x ^ 3 * y ^ 3 * t ^ 3 + (8:ℝ) * ranadaA x y z t ^ 3 * x ^ 5 * y * t ^ 3 + (7:ℝ) * ranadaA x y z t ^ 4 * y ^ 2 * z ^ 2 * t ^ 4 - ranadaA x y z t ^ 4 * y ^ 2 * z ^ 4 * t ^ 2 + (7:ℝ) * ranadaA x y z t ^ 4 * y ^ 4 * t ^ 4 - (2:ℝ) * ranadaA x y z t ^ 4 * y ^ 4 * z ^ 2 * t ^ 2 - ranadaA x y z t ^ 4 * y ^ 6 * t ^ 2 - (7:ℝ) * ranadaA x y z t ^ 4 * x ^ 2 * z ^ 2 * t ^ 4 + ranadaA x y z t ^ 4 * x ^ 2 * z ^ 4 * t ^ 2 - ranadaA x y z t ^ 4 * x ^ 2 * y ^ 4 * t ^ 2 - (7:ℝ) * ranadaA x y z t ^ 4 * x ^ 4 * t ^ 4 + (2:ℝ) * ranadaA x y z t ^ 4 * x ^ 4 * z ^ 2 * t ^ 2 + ranadaA x y z t ^ 4 * x ^ 4 * y ^ 2 * t ^ 2 + ranadaA x y z t ^ 4 * x ^ 6 * t ^ 2 + (16:ℝ) * ranadaA x y z t ^ 5 * x * y * z ^ 2 * t ^ 3 + (16:ℝ) * ranadaA x y z t ^ 5 * x * y ^ 3 * t ^ 3 + (16:ℝ) * ranadaA x y z t ^ 5 * x ^ 3 * y * t ^ 3 + ranadaA x y z t ^ 6 * y ^ 2 * t ^ 4 - (7:ℝ) * ranadaA x y z t ^ 6 * y ^ 2 * z ^ 2 * t ^ 2 - (7:ℝ) * ranadaA x y z t ^ 6 * y ^ 4 * t ^ 2 - ranadaA x y z t ^ 6 * x ^ 2 * t ^ 4 + (7:ℝ) * ranadaA x y z t ^ 6 * x ^ 2 * z ^ 2 * t ^ 2 + (7:ℝ) * ranadaA x y z t ^ 6 * x ^ 4 * t ^ 2 + (8:ℝ) * ranadaA x y z t ^ 7 * x * y * t ^ 3 - (8:ℝ) * ranadaA x y z t ^ 7 * x * y * z ^ 2 * t - (8:ℝ) * ranadaA x y z t ^ 7 * x * y ^ 3 * t - (8:ℝ) * ranadaA x y z t ^ 7 * x ^ 3 * y * t - (6:ℝ) * ranadaA x y z t ^ 8 * y ^ 2 * t ^ 2 + ranadaA x y z t ^ 8 * y ^ 2 * z ^ 2 + ranadaA x y z t ^ 8 * y ^ 4 + (6:ℝ) * ranadaA x y z t ^ 8 * x ^ 2 * t ^ 2 - ranadaA x y z t ^ 8 * x ^ 2 * z ^ 2 - ranadaA x y z t ^ 8 * x ^ 4 - (8:ℝ) * ranadaA x y z t ^ 9 * x * y * t + ranadaA x y z t ^ 10 * y ^ 2 - ranadaA x y z t ^ 10 * x ^ 2) * hA

/-! ### Canonical dot-product rewrites -/

/-- Dot of the negated imaginary magnetic split against the real one. -/
theorem neg_eta_im_dot_eta_re (x y z t : ℝ) :
    dot3 (fun j => -(etaImPart x y z t j)) (etaRePart x y z t) =
      -(dot3 (etaRePart x y z t) (etaImPart x y z t)) := by
  rw [dot3_neg_left, dot3_comm]

/-- Dot of the negated imaginary magnetic split against itself. -/
theorem neg_eta_im_dot_eta_im (x y z t : ℝ) :
    dot3 (fun j => -(etaImPart x y z t j)) (etaImPart x y z t) =
      -(dot3 (etaImPart x y z t) (etaImPart x y z t)) := by
  rw [dot3_neg_left]

/-- Dot of the negated imaginary magnetic split against the electric one. -/
theorem neg_eta_im_dot_zeta_im (x y z t : ℝ) :
    dot3 (fun j => -(etaImPart x y z t j)) (zetaImPart x y z t) =
      -(dot3 (etaImPart x y z t) (zetaImPart x y z t)) := by
  rw [dot3_neg_left]

/-- Dot of the imaginary magnetic split against its own negation. -/
theorem eta_im_dot_neg_eta_im (x y z t : ℝ) :
    dot3 (etaImPart x y z t) (fun j => -(etaImPart x y z t j)) =
      -(dot3 (etaImPart x y z t) (etaImPart x y z t)) := by
  rw [dot3_neg_right]

/-- Dot of the real magnetic split against the negated imaginary one. -/
theorem eta_re_dot_neg_eta_im (x y z t : ℝ) :
    dot3 (etaRePart x y z t) (fun j => -(etaImPart x y z t j)) =
      -(dot3 (etaRePart x y z t) (etaImPart x y z t)) := by
  rw [dot3_neg_right]

/-- Double negation cancels in both split arguments. -/
theorem neg_eta_im_dot_neg_eta_im (x y z t : ℝ) :
    dot3 (fun j => -(etaImPart x y z t j)) (fun j => -(etaImPart x y z t j)) =
      dot3 (etaImPart x y z t) (etaImPart x y z t) := by
  rw [dot3_neg_left, dot3_neg_right, neg_neg]

/-- Dot of the electric imaginary split against the negated magnetic one. -/
theorem zeta_im_dot_neg_eta_im (x y z t : ℝ) :
    dot3 (zetaImPart x y z t) (fun j => -(etaImPart x y z t j)) =
      -(dot3 (etaImPart x y z t) (zetaImPart x y z t)) := by
  rw [dot3_neg_right, dot3_comm]

/-- The electric imaginary against real magnetic dot, in canonical order. -/
theorem zeta_im_dot_eta_re (x y z t : ℝ) :
    dot3 (zetaImPart x y z t) (etaRePart x y z t) =
      dot3 (etaRePart x y z t) (zetaImPart x y z t) :=
  dot3_comm _ _

/-- The electric imaginary against magnetic imaginary dot, in canonical order. -/
theorem zeta_im_dot_eta_im (x y z t : ℝ) :
    dot3 (zetaImPart x y z t) (etaImPart x y z t) =
      dot3 (etaImPart x y z t) (zetaImPart x y z t) :=
  dot3_comm _ _

/-- The magnetic imaginary against real dot, in canonical order. -/
theorem eta_im_dot_eta_re (x y z t : ℝ) :
    dot3 (etaImPart x y z t) (etaRePart x y z t) =
      dot3 (etaRePart x y z t) (etaImPart x y z t) :=
  dot3_comm _ _

/-- Dot of the electric imaginary split against its own negation. -/
theorem zeta_im_dot_neg_zeta_im (x y z t : ℝ) :
    dot3 (zetaImPart x y z t) (fun j => -(zetaImPart x y z t j)) =
      -(dot3 (zetaImPart x y z t) (zetaImPart x y z t)) := by
  rw [dot3_neg_right]

/-- Double negation cancels across both mixed split arguments. -/
theorem neg_eta_im_dot_neg_zeta_im (x y z t : ℝ) :
    dot3 (fun j => -(etaImPart x y z t j)) (fun j => -(zetaImPart x y z t j)) =
      dot3 (etaImPart x y z t) (zetaImPart x y z t) := by
  rw [dot3_neg_left, dot3_neg_right, neg_neg]

/-! ### The split square and Hermitian pairings -/

/-- The conjugate of the electric homogeneous numerator, split. -/
theorem zetaHomog_conj_split (x y z t : ℝ) :
    (fun k => conj (zetaHomog x y z t k)) =
      fun k => ((-(etaImPart x y z t k) : ℝ) : ℂ) +
        Complex.I * ((-(zetaImPart x y z t k) : ℝ) : ℂ) := by
  funext k
  rw [congrFun (zetaHomog_split x y z t) k, conj_split]
  simp only [Complex.ofReal_neg]
  ring

/-- The bilinear square of the electric homogeneous numerator, split into real
and imaginary parts. -/
theorem zetaHomog_square_split (x y z t : ℝ) :
    dot3 (zetaHomog x y z t) (zetaHomog x y z t) =
      ((dot3 (etaImPart x y z t) (etaImPart x y z t) -
          dot3 (zetaImPart x y z t) (zetaImPart x y z t) : ℝ) : ℂ) +
        Complex.I * ((-(dot3 (etaImPart x y z t) (zetaImPart x y z t)) -
          dot3 (etaImPart x y z t) (zetaImPart x y z t) : ℝ) : ℂ) := by
  rw [zetaHomog_split, dot3_split, neg_eta_im_dot_neg_eta_im, neg_eta_im_dot_zeta_im,
    zeta_im_dot_neg_eta_im]
  rw [Complex.ext_iff]
  constructor
  · simp only [Complex.add_re, Complex.mul_re, Complex.I_re, Complex.I_im,
      Complex.ofReal_re, Complex.ofReal_im, mul_zero, zero_mul, sub_self, add_zero]
  · simp only [Complex.add_im, Complex.mul_im, Complex.I_re, Complex.I_im,
      Complex.ofReal_re, Complex.ofReal_im, mul_zero, one_mul]
    ring

/-- The bilinear square of the magnetic homogeneous numerator, split into real
and imaginary parts. -/
theorem etaHomog_square_split (x y z t : ℝ) :
    dot3 (etaHomog x y z t) (etaHomog x y z t) =
      ((dot3 (etaRePart x y z t) (etaRePart x y z t) -
          dot3 (etaImPart x y z t) (etaImPart x y z t) : ℝ) : ℂ) +
        Complex.I * ((dot3 (etaRePart x y z t) (etaImPart x y z t) +
          dot3 (etaRePart x y z t) (etaImPart x y z t) : ℝ) : ℂ) := by
  rw [etaHomog_split, dot3_split, eta_im_dot_eta_re]

/-- The Hermitian square of the electric homogeneous numerator is real. -/
theorem zetaHomog_hermitian (x y z t : ℝ) :
    dot3 (zetaHomog x y z t) (fun k => conj (zetaHomog x y z t k)) =
      ((dot3 (etaImPart x y z t) (etaImPart x y z t) +
          dot3 (zetaImPart x y z t) (zetaImPart x y z t) : ℝ) : ℂ) := by
  rw [zetaHomog_conj_split, zetaHomog_split, dot3_split, neg_eta_im_dot_neg_eta_im,
    zeta_im_dot_neg_zeta_im, neg_eta_im_dot_neg_zeta_im, zeta_im_dot_neg_eta_im, sub_neg_eq_add]
  rw [Complex.ext_iff]
  constructor
  · simp only [Complex.add_re, Complex.mul_re, Complex.I_re, Complex.I_im,
      Complex.ofReal_re, Complex.ofReal_im, mul_zero, zero_mul, sub_self, add_zero]
  · simp only [Complex.add_im, Complex.mul_im, Complex.I_re, Complex.I_im,
      Complex.ofReal_re, Complex.ofReal_im, mul_zero, one_mul]
    ring

/-- The Hermitian square of the magnetic homogeneous numerator is real. -/
theorem etaHomog_hermitian (x y z t : ℝ) :
    dot3 (etaHomog x y z t) (fun k => conj (etaHomog x y z t k)) =
      ((dot3 (etaRePart x y z t) (etaRePart x y z t) +
          dot3 (etaImPart x y z t) (etaImPart x y z t) : ℝ) : ℂ) := by
  rw [etaHomog_conj_split, etaHomog_split, dot3_split, eta_im_dot_neg_eta_im,
    eta_re_dot_neg_eta_im, eta_im_dot_eta_re, sub_neg_eq_add]
  rw [Complex.ext_iff]
  constructor
  · simp only [Complex.add_re, Complex.mul_re, Complex.I_re, Complex.I_im,
      Complex.ofReal_re, Complex.ofReal_im, mul_zero, zero_mul, sub_self, add_zero]
  · simp only [Complex.add_im, Complex.mul_im, Complex.I_re, Complex.I_im,
      Complex.ofReal_re, Complex.ofReal_im, mul_zero, one_mul]
    ring

/-! ### The pointwise null invariants -/

/-- The mixed complex pairings of the electric and magnetic homogeneous
numerators have equal squared moduli; by `key_dot_identity` the difference of
the two squared moduli is four times the balanced cross product. -/
theorem zeta_eta_pairing_absSq (x y z t : ℝ) :
    dot3 (zetaHomog x y z t) (etaHomog x y z t) *
        conj (dot3 (zetaHomog x y z t) (etaHomog x y z t)) =
      dot3 (zetaHomog x y z t) (fun k => conj (etaHomog x y z t k)) *
        conj (dot3 (zetaHomog x y z t) (fun k => conj (etaHomog x y z t k))) := by
  rw [zetaHomog_split, etaHomog_conj_split, etaHomog_split, dot3_split, dot3_split,
    conj_split, conj_split, mul_conj_split, mul_conj_split,
    neg_eta_im_dot_eta_re, zeta_im_dot_eta_im, neg_eta_im_dot_eta_im, zeta_im_dot_eta_re,
    zeta_im_dot_neg_eta_im, neg_eta_im_dot_neg_eta_im, sub_neg_eq_add]
  have hcore : (-(dot3 (etaRePart x y z t) (etaImPart x y z t)) -
          dot3 (etaImPart x y z t) (zetaImPart x y z t)) ^ 2 +
        (-(dot3 (etaImPart x y z t) (etaImPart x y z t)) +
          dot3 (etaRePart x y z t) (zetaImPart x y z t)) ^ 2 =
      (-(dot3 (etaRePart x y z t) (etaImPart x y z t)) +
          dot3 (etaImPart x y z t) (zetaImPart x y z t)) ^ 2 +
        (dot3 (etaImPart x y z t) (etaImPart x y z t) +
          dot3 (etaRePart x y z t) (zetaImPart x y z t)) ^ 2 := by
    linear_combination (-4:ℝ) * key_dot_identity x y z t
  rw [hcore]

/-- The Hopf electric and magnetic fields are pointwise orthogonal. -/
theorem ranadaE_dot_ranadaB (x y z t : ℝ) :
    dot3 (ranadaE x y z t) (ranadaB x y z t) = 0 := by
  have hE : ranadaE x y z t = fun j => (1 / (4 * Real.pi * Complex.I)) *
      ((zetaSumSq x y z t) ^ 2)⁻¹ *
      cross3 (zetaHomog x y z t) (fun k => conj (zetaHomog x y z t k)) j := by
    funext j
    simp only [ranadaE, div_eq_inv_mul]
    ring
  have hB : ranadaB x y z t = fun j => (1 / (4 * Real.pi * Complex.I)) *
      ((etaSumSq x y z t) ^ 2)⁻¹ *
      cross3 (etaHomog x y z t) (fun k => conj (etaHomog x y z t k)) j := by
    funext j
    simp only [ranadaB, div_eq_inv_mul]
    ring
  rw [hE, hB]
  simp only [dot3_smul_left, dot3_smul_right]
  rw [dot3_cross3_cross3, ← dot3_conj (zetaHomog x y z t) (etaHomog x y z t),
    dot3_conj_left (zetaHomog x y z t) (etaHomog x y z t),
    zeta_eta_pairing_absSq x y z t]
  ring

/-- The Hopf electric and magnetic fields have equal complex bilinear squares,
which is the pointwise null condition of the Riemann-Silberstein field. -/
theorem ranadaE_sq_eq_ranadaB_sq (x y z t : ℝ) :
    dot3 (ranadaE x y z t) (ranadaE x y z t) =
      dot3 (ranadaB x y z t) (ranadaB x y z t) := by
  have hE : ranadaE x y z t = fun j => (1 / (4 * Real.pi * Complex.I)) *
      ((zetaSumSq x y z t) ^ 2)⁻¹ *
      cross3 (zetaHomog x y z t) (fun k => conj (zetaHomog x y z t k)) j := by
    funext j
    simp only [ranadaE, div_eq_inv_mul]
    ring
  have hB : ranadaB x y z t = fun j => (1 / (4 * Real.pi * Complex.I)) *
      ((etaSumSq x y z t) ^ 2)⁻¹ *
      cross3 (etaHomog x y z t) (fun k => conj (etaHomog x y z t k)) j := by
    funext j
    simp only [ranadaB, div_eq_inv_mul]
    ring
  rw [hE, hB, zetaSumSq_eq_etaSumSq x y z t]
  simp only [dot3_smul_left, dot3_smul_right]
  rw [dot3_cross3_cross3, dot3_cross3_cross3,
    ← dot3_conj (zetaHomog x y z t) (zetaHomog x y z t),
    ← dot3_conj (etaHomog x y z t) (etaHomog x y z t),
    dot3_comm (fun k => conj (zetaHomog x y z t k)) (zetaHomog x y z t),
    dot3_comm (fun k => conj (etaHomog x y z t k)) (etaHomog x y z t),
    zetaHomog_square_split, etaHomog_square_split, zetaHomog_hermitian,
    etaHomog_hermitian, conj_split, conj_split, mul_conj_split, mul_conj_split]
  rw [← Complex.ofReal_mul, ← Complex.ofReal_mul, ← Complex.ofReal_sub,
    ← Complex.ofReal_sub]
  have hcore :
      (dot3 (etaImPart x y z t) (etaImPart x y z t) -
          dot3 (zetaImPart x y z t) (zetaImPart x y z t)) ^ 2 +
        (-(dot3 (etaImPart x y z t) (zetaImPart x y z t)) -
          dot3 (etaImPart x y z t) (zetaImPart x y z t)) ^ 2 -
        (dot3 (etaImPart x y z t) (etaImPart x y z t) +
          dot3 (zetaImPart x y z t) (zetaImPart x y z t)) *
          (dot3 (etaImPart x y z t) (etaImPart x y z t) +
            dot3 (zetaImPart x y z t) (zetaImPart x y z t)) =
      (dot3 (etaRePart x y z t) (etaRePart x y z t) -
          dot3 (etaImPart x y z t) (etaImPart x y z t)) ^ 2 +
        (dot3 (etaRePart x y z t) (etaImPart x y z t) +
          dot3 (etaRePart x y z t) (etaImPart x y z t)) ^ 2 -
        (dot3 (etaRePart x y z t) (etaRePart x y z t) +
          dot3 (etaImPart x y z t) (etaImPart x y z t)) *
          (dot3 (etaRePart x y z t) (etaRePart x y z t) +
            dot3 (etaImPart x y z t) (etaImPart x y z t)) := by
    linear_combination (-4:ℝ) * key_norm_identity x y z t
  rw [hcore]

end Qatlib.Papers.KnottedLight08.NullLinking
