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
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.NormNum
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Qatlib.Papers.KnottedLight08.HopfField.NullAlgebra
public import Qatlib.Papers.KnottedLight08.HopfField.RanadaScalars
public import Qatlib.Papers.KnottedLight08.HopfField.RanadaField
public import Qatlib.Papers.KnottedLight08.NullLinking.NullInvariants
public import Qatlib.Papers.KnottedLight08.NullLinking.ComplexPhaseFibers

/-!
# Hopf fibers of the Rañada fields

[IrvineBouwmeester2008KnottedLight], pp. 717-718,
[DOI](https://doi.org/10.1038/nphys1056).
Two structural facts behind the linked field lines of the Hopf solution.

At every time the magnetic field is pointwise orthogonal to the homogeneous
numerator of the magnetic scalar and to its quotient-form spatial gradient.
The electric field satisfies the corresponding identities for `zeta`.
These total algebraic identities give the directional vanishing used in a
field-line argument on the charts where the scalar is defined.

Second, at `t = 0` the letter quadruple `(P, Q, R, S)` is the square of the
letter `A` times the image of the public inverse stereographic projection
under the coordinate rotation `(a, b, c, d) ↦ (a, c, -b, d)`, the total letter
squared norm collapses to `A ^ 4`, and the printed magnetic scalar reduces to
the compact Möbius form `(z - i y) / (x + i (x^2 + y^2 + z^2 - 1) / 2)`.
-/

@[expose] public section
set_option autoImplicit false

namespace Qatlib.Papers.KnottedLight08.NullLinking

open Qatlib.Papers.KnottedLight08.HopfField (dot3 cross3 stereo stereo_denominator_pos dot_cross_left)
open Qatlib.Papers.KnottedLight08.HopfField
open scoped ComplexConjugate

/-! ### Pointwise orthogonality to the quotient gradients -/

/-- The magnetic field is pointwise orthogonal to its own homogeneous
numerator, hence to the gradient of the magnetic scalar wherever that scalar
is defined. -/
theorem ranadaB_dot_etaHomog (x y z t : ℝ) :
    dot3 (ranadaB x y z t) (etaHomog x y z t) = 0 := by
  have hB : ranadaB x y z t =
      fun j => ((1 / (4 * Real.pi * Complex.I)) * (etaSumSq x y z t ^ 2)⁻¹) *
        cross3 (etaHomog x y z t) (fun k => conj (etaHomog x y z t k)) j := by
    funext j
    simp only [ranadaB, div_eq_inv_mul]
    ring
  rw [hB]
  simp only [dot3_smul_left]
  rw [dot_cross_left]
  ring

/-- The electric field is pointwise orthogonal to its own homogeneous
numerator, hence to the gradient of the electric scalar wherever that scalar
is defined. -/
theorem ranadaE_dot_zetaHomog (x y z t : ℝ) :
    dot3 (ranadaE x y z t) (zetaHomog x y z t) = 0 := by
  have hE : ranadaE x y z t =
      fun j => ((1 / (4 * Real.pi * Complex.I)) * (zetaSumSq x y z t ^ 2)⁻¹) *
        cross3 (zetaHomog x y z t) (fun k => conj (zetaHomog x y z t k)) j := by
    funext j
    simp only [ranadaE, div_eq_inv_mul]
    ring
  rw [hE]
  simp only [dot3_smul_left]
  rw [dot_cross_left]
  ring

/-- The magnetic field is orthogonal to the printed quotient-form gradient of
the magnetic scalar as a total identity in the field inversion algebra. -/
theorem ranadaB_dot_etaGrad (x y z t : ℝ) :
    dot3 (ranadaB x y z t) (etaGrad x y z t) = 0 := by
  have hB : ranadaB x y z t =
      fun j => ((1 / (4 * Real.pi * Complex.I)) * (etaSumSq x y z t ^ 2)⁻¹) *
        cross3 (etaHomog x y z t) (fun k => conj (etaHomog x y z t k)) j := by
    funext j
    simp only [ranadaB, div_eq_inv_mul]
    ring
  have hG : etaGrad x y z t =
      fun j => (etaDen x y z t ^ 2)⁻¹ * etaHomog x y z t j := by
    funext j
    simp only [etaGrad, etaHomog, div_eq_inv_mul]
  rw [hB, hG]
  simp only [dot3_smul_left, dot3_smul_right]
  rw [dot_cross_left]
  ring

/-- The electric field is orthogonal to the printed quotient-form gradient of
the electric scalar as a total identity in the field inversion algebra. -/
theorem ranadaE_dot_zetaGrad (x y z t : ℝ) :
    dot3 (ranadaE x y z t) (zetaGrad x y z t) = 0 := by
  have hE : ranadaE x y z t =
      fun j => ((1 / (4 * Real.pi * Complex.I)) * (zetaSumSq x y z t ^ 2)⁻¹) *
        cross3 (zetaHomog x y z t) (fun k => conj (zetaHomog x y z t k)) j := by
    funext j
    simp only [ranadaE, div_eq_inv_mul]
    ring
  have hG : zetaGrad x y z t =
      fun j => (zetaDen x y z t ^ 2)⁻¹ * zetaHomog x y z t j := by
    funext j
    simp only [zetaGrad, zetaHomog, div_eq_inv_mul]
  rw [hE, hG]
  simp only [dot3_smul_left, dot3_smul_right]
  rw [dot_cross_left]
  ring

/-! ### The `t = 0` letter structure -/

/-- At `t = 0` the letter quadruple is the square of the letter `A` times the
inverse stereographic projection composed with the coordinate rotation
`(a, b, c, d) ↦ (a, c, -b, d)`. -/
theorem ranadaQuat_t_zero (x y z : ℝ) :
    ranadaQuat x y z 0 = fun j => ranadaA x y z 0 ^ 2 *
      (![stereo x y z 0, stereo x y z 2, -(stereo x y z 1), stereo x y z 3]) j := by
  funext j
  have hd : (x ^ 2 + y ^ 2 + z ^ 2 + 1 : ℝ) ≠ 0 := (stereo_denominator_pos x y z).ne'
  fin_cases j
  · show ranadaP x y z 0 = ranadaA x y z 0 ^ 2 * stereo x y z 0
    simp only [ranadaP, ranadaA, stereo, Matrix.cons_val_zero]
    field_simp [hd]
    ring
  · show ranadaQ x y z 0 = ranadaA x y z 0 ^ 2 * stereo x y z 2
    simp only [ranadaQ, ranadaA, stereo, Matrix.cons_val_two, Matrix.tail_cons,
      Matrix.head_cons]
    field_simp [hd]
    ring
  · show ranadaR x y z 0 = ranadaA x y z 0 ^ 2 * -(stereo x y z 1)
    simp only [ranadaR, ranadaA, stereo, Matrix.cons_val_one, Matrix.cons_val_zero]
    field_simp [hd]
    ring
  · show ranadaS x y z 0 = ranadaA x y z 0 ^ 2 * stereo x y z 3
    simp only [ranadaS, ranadaA, stereo, Matrix.cons_val_three, Matrix.tail_cons,
      Matrix.head_cons]
    field_simp [hd]
    ring

/-- At `t = 0` the total letter squared norm collapses to the fourth power of
the letter `A`. -/
theorem etaSumSq_t_zero (x y z : ℝ) :
    etaSumSq x y z 0 = ((ranadaA x y z 0 ^ 4 : ℝ) : ℂ) := by
  have h1 : etaSumSq x y z 0 =
      ((ranadaP x y z 0 ^ 2 + ranadaQ x y z 0 ^ 2 + ranadaR x y z 0 ^ 2 +
        ranadaS x y z 0 ^ 2 : ℝ) : ℂ) := etaPairNormSq x y z 0
  have h2 : ranadaP x y z 0 ^ 2 + ranadaQ x y z 0 ^ 2 + ranadaR x y z 0 ^ 2 +
      ranadaS x y z 0 ^ 2 = ranadaA x y z 0 ^ 4 := by
    rw [ranadaNormSq_eq x y z 0]
    have hA : ranadaA x y z 0 = (x ^ 2 + y ^ 2 + z ^ 2 + 1) / 2 := ranadaA_t_zero x y z
    rw [hA]
    field_simp
    ring
  rw [h1, h2]

/-- At `t = 0` the total letter squared norm of the electric pair collapses to
the fourth power of the letter `A` as well. -/
theorem zetaSumSq_t_zero (x y z : ℝ) :
    zetaSumSq x y z 0 = ((ranadaA x y z 0 ^ 4 : ℝ) : ℂ) := by
  have h1 : zetaSumSq x y z 0 =
      ((ranadaP x y z 0 ^ 2 + ranadaQ x y z 0 ^ 2 + ranadaR x y z 0 ^ 2 +
        ranadaS x y z 0 ^ 2 : ℝ) : ℂ) := zetaPairNormSq x y z 0
  have h2 : ranadaP x y z 0 ^ 2 + ranadaQ x y z 0 ^ 2 + ranadaR x y z 0 ^ 2 +
      ranadaS x y z 0 ^ 2 = ranadaA x y z 0 ^ 4 := by
    rw [ranadaNormSq_eq x y z 0]
    have hA : ranadaA x y z 0 = (x ^ 2 + y ^ 2 + z ^ 2 + 1) / 2 := ranadaA_t_zero x y z
    rw [hA]
    field_simp
    ring
  rw [h1, h2]

/-- At `t = 0` the printed magnetic scalar is the compact Möbius form
`(z - i y) / (x + i (x^2 + y^2 + z^2 - 1) / 2)`; the letter `A` cancels
because it is strictly positive at `t = 0`. -/
theorem ranadaEta_t_zero (x y z : ℝ) :
    ranadaEta x y z 0 = (((z : ℝ) : ℂ) - Complex.I * ((y : ℝ) : ℂ)) /
        (((x : ℝ) : ℂ) + Complex.I *
          (((x ^ 2 + y ^ 2 + z ^ 2 - 1) / 2 : ℝ) : ℂ)) := by
  have hA : ((ranadaA x y z 0 : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast ne_of_gt (ranadaA_t_zero_pos x y z)
  have hn : ((ranadaQ x y z 0 : ℝ) : ℂ) + Complex.I * ((ranadaR x y z 0 : ℝ) : ℂ) =
      ((ranadaA x y z 0 : ℝ) : ℂ) *
        (((z : ℝ) : ℂ) - Complex.I * ((y : ℝ) : ℂ)) := by
    simp only [ranadaQ, ranadaR, ranadaA]
    push_cast
    ring
  have hd : ((ranadaP x y z 0 : ℝ) : ℂ) + Complex.I * ((ranadaS x y z 0 : ℝ) : ℂ) =
      ((ranadaA x y z 0 : ℝ) : ℂ) *
        (((x : ℝ) : ℂ) + Complex.I *
          (((x ^ 2 + y ^ 2 + z ^ 2 - 1) / 2 : ℝ) : ℂ)) := by
    simp only [ranadaP, ranadaS, ranadaA]
    push_cast
    ring
  simp only [ranadaEta]
  rw [hn, hd]
  field_simp [hA]

/-! ### The global projective magnetic coordinate -/

/-- The norm of the magnetic homogeneous letter pair, used to put it on the
unit three-sphere before forming its projective class. -/
noncomputable def magneticPairNorm (x y z t : ℝ) : ℝ :=
  Real.sqrt (Complex.normSq (etaNum x y z t) + Complex.normSq (etaDen x y z t))

/-- The magnetic homogeneous letter pair never vanishes, including at the
poles of the printed scalar. -/
theorem magneticPairNorm_pos (x y z t : ℝ) : 0 < magneticPairNorm x y z t := by
  apply Real.sqrt_pos.2
  have h := ranadaNormSq_pos x y z t
  simpa [etaNum, etaDen, Complex.normSq_apply, Complex.add_re, Complex.mul_re,
    Complex.add_im, Complex.mul_im, pow_two, add_assoc, add_left_comm, add_comm] using h

/-- The Rañada magnetic coordinate as a unit pair of homogeneous
coordinates; the second entry may vanish at a pole of the affine chart. -/
noncomputable def magneticHopfPair (x y z t : ℝ) : ℂ × ℂ :=
  (etaNum x y z t / magneticPairNorm x y z t,
    etaDen x y z t / magneticPairNorm x y z t)

/-- The normalized Rañada magnetic coordinate lies on the unit
three-sphere at every space-time point. -/
theorem magneticHopfPair_unit (x y z t : ℝ) :
    Complex.normSq (magneticHopfPair x y z t).1 +
      Complex.normSq (magneticHopfPair x y z t).2 = 1 := by
  have hsq : Complex.normSq ((magneticPairNorm x y z t : ℝ) : ℂ) =
      Complex.normSq (etaNum x y z t) + Complex.normSq (etaDen x y z t) := by
    rw [Complex.normSq_ofReal, ← pow_two, magneticPairNorm,
      Real.sq_sqrt (add_nonneg (Complex.normSq_nonneg _) (Complex.normSq_nonneg _))]
  have hne : Complex.normSq ((magneticPairNorm x y z t : ℝ) : ℂ) ≠ 0 := by
    rw [Complex.normSq_ofReal]
    exact mul_ne_zero (magneticPairNorm_pos x y z t).ne'
      (magneticPairNorm_pos x y z t).ne'
  simp only [magneticHopfPair, Complex.normSq_div, ← add_div]
  exact (div_eq_one_iff_eq hne).2 hsq.symm

/-- On the magnetic affine chart, equality of the printed Rañada scalars
is exactly membership in the same compact projective Hopf fiber. -/
theorem ranadaEta_eq_iff_mem_unitHopfFiber (x y z x' y' z' t : ℝ)
    (h : etaDen x y z t ≠ 0) (h' : etaDen x' y' z' t ≠ 0) :
    ranadaEta x y z t = ranadaEta x' y' z' t ↔
      magneticHopfPair x y z t ∈ unitHopfFiber (magneticHopfPair x' y' z' t) := by
  have hk : (magneticPairNorm x y z t : ℂ) ≠ 0 := by
    exact_mod_cast (magneticPairNorm_pos x y z t).ne'
  have hk' : (magneticPairNorm x' y' z' t : ℂ) ≠ 0 := by
    exact_mod_cast (magneticPairNorm_pos x' y' z' t).ne'
  rw [ranadaEta_def, ranadaEta_def, div_eq_div_iff h h']
  change _ ↔ _ ∧ _
  rw [and_iff_right (magneticHopfPair_unit x y z t)]
  simp only [magneticHopfPair, div_mul_div_comm, div_left_inj' (mul_ne_zero hk hk')]
  rw [mul_comm (etaDen x y z t) (etaNum x' y' z' t)]

end Qatlib.Papers.KnottedLight08.NullLinking
