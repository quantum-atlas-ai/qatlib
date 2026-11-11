/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.FastHermitian06.MainResults.GeneralFinalState.Basic
import Qatlib.Papers.FastHermitian06.MainResults.SpinFlip
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Exponential

/-!
# Evolution for a general two-level Hamiltonian

The normalized traceless matrix `sigmaUnitGen` squares to the identity in the unbroken region.
This yields an explicit hyperbolic-function decomposition of the matrix exponential
`evolution4`, and hence the trigonometric state formula `evolution18`. See [BenderEtAl2007].

## Main statements

* `sigmaUnitGen_sq`: the normalized matrix is an involution.
* `evolution4_decomp`: separates the scalar phase from the normalized evolution.
* `evolution18`: evaluates evolution of `ket0` using `bracket18`.

## References

* [Bender et al., 2007][BenderEtAl2007]
-/

set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false
noncomputable section

open Matrix
open scoped BigOperators Matrix ComplexOrder

open Qatlib.Papers.FastHermitian06.MainResults.Defs

namespace Qatlib.Papers.FastHermitian06.MainResults.GeneralFinalState

open Qatlib.Papers.FastHermitian06.MainResults.Defs

/-- The nonnegative square root of the general squared-gap expression. -/
def omegaGen (y z γ : ℝ) : ℝ := Real.sqrt (omegaSqGen y z γ)

/-- The condition that `omegaSqGen y z γ` is strictly positive. -/
def unbrokenPTGen (y z γ : ℝ) : Prop := 0 < omegaSqGen y z γ

/-- In the general unbroken region, the square of `omegaGen` equals `omegaSqGen`. -/
theorem omegaGen_sq (y z γ : ℝ) (h : unbrokenPTGen y z γ) :
    omegaGen y z γ ^ 2 = omegaSqGen y z γ := by
  unfold omegaGen
  exact Real.sq_sqrt (le_of_lt h)

/-- The traceless matrix `sigmaNGen` scaled by `2 / omegaGen`. -/
def sigmaUnitGen (y z γ : ℝ) : Mat2 :=
  (((2 / omegaGen y z γ : ℝ)) : ℂ) • sigmaNGen y z γ

/-- Real scalar multiplication of a complex matrix equals scalar multiplication by the
corresponding complex number. -/
theorem real_smul_eq_complex_smul (r : ℝ) (M : Mat2) :
    r • M = ((r : ℂ) • M) := by
  ext i j
  simp [Matrix.smul_apply]

/-- The normalized traceless matrix squares to the identity when the squared gap is positive and
both trigonometric denominators are nonzero. -/
theorem sigmaUnitGen_sq (y z γ : ℝ) (hsin : Real.sin γ ≠ 0)
    (hcos : Real.cos γ ≠ 0) (hunb : unbrokenPTGen y z γ) :
    sigmaUnitGen y z γ * sigmaUnitGen y z γ = (1 : Mat2) := by
  have hω : omegaGen y z γ ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr hunb)
  have hsq : omegaGen y z γ ^ 2 = omegaSqGen y z γ := omegaGen_sq y z γ hunb
  have hcoefR : (2 / omegaGen y z γ) * (2 / omegaGen y z γ)
      * (omegaSqGen y z γ / 4) = 1 := by
    field_simp [hω]
    nlinarith [hsq]
  have hcoef : (((2 / omegaGen y z γ : ℝ)) : ℂ) * (((2 / omegaGen y z γ : ℝ)) : ℂ)
      * ((omegaSqGen y z γ / 4 : ℝ) : ℂ) = 1 := by
    have := congrArg ((↑) : ℝ → ℂ) hcoefR
    push_cast at this ⊢
    exact this
  have hinner : ((omegaSqGen y z γ / 4 : ℝ) • (1 : Mat2))
      = (((omegaSqGen y z γ / 4 : ℝ)) : ℂ) • (1 : Mat2) :=
    real_smul_eq_complex_smul _ _
  rw [sigmaUnitGen, Matrix.smul_mul, Matrix.mul_smul,
    sigmaNGen_sq y z γ hsin hcos, hinner, smul_smul, smul_smul, hcoef, one_smul]

/-- For nonzero gap, decomposes `H4` into its scalar part and half the gap times `sigmaUnitGen`. -/
theorem H4_decomp_unit (x y z γ : ℝ) (hω : omegaGen y z γ ≠ 0) :
    H4 x y z γ = (x : ℂ) • (1 : Mat2)
      + (((omegaGen y z γ / 2 : ℝ)) : ℂ) • sigmaUnitGen y z γ := by
  have hcoef : (((omegaGen y z γ / 2 : ℝ)) : ℂ) * (((2 / omegaGen y z γ : ℝ)) : ℂ)
      = 1 := by
    push_cast
    field_simp [hω]
  rw [H4_decomp, sigmaUnitGen, smul_smul, hcoef, one_smul]

/-- The matrix exponential of `(-I * t / ħ)` times `H4`. -/
def evolution4 (x y z γ ħ t : ℝ) : Mat2 :=
  NormedSpace.exp ((-(Complex.I * ((t / ħ : ℝ) : ℂ))) • H4 x y z γ)

/-- The scalar exponent `-I * t * x / ħ` in the general evolution. -/
def genPhase (x ħ t : ℝ) : ℂ :=
  (-(Complex.I * ((t / ħ : ℝ) : ℂ))) * (x : ℂ)

/-- The exponent `-I * t * omegaGen / (2 * ħ)` for the normalized traceless part. -/
def genHalf (y z γ ħ t : ℝ) : ℂ :=
  (-(Complex.I * ((t / ħ : ℝ) : ℂ))) * (((omegaGen y z γ / 2 : ℝ)) : ℂ)

/-- The hyperbolic cosine of `genHalf` equals the real cosine at the corresponding half-gap
time. -/
theorem cosh_genHalf (y z γ ħ t : ℝ) :
    Complex.cosh (genHalf y z γ ħ t)
      = ((Real.cos (omegaGen y z γ * t / (2 * ħ)) : ℝ) : ℂ) := by
  have hz : genHalf y z γ ħ t
      = -(((((omegaGen y z γ * t / (2 * ħ)) : ℝ)) : ℂ) * Complex.I) := by
    unfold genHalf
    push_cast
    ring
  rw [hz, Complex.cosh_neg, Complex.cosh_mul_I, ← Complex.ofReal_cos]

/-- The hyperbolic sine of `genHalf` equals `-I` times the real sine at the corresponding
half-gap time. -/
theorem sinh_genHalf (y z γ ħ t : ℝ) :
    Complex.sinh (genHalf y z γ ħ t)
      = (-Complex.I) * ((Real.sin (omegaGen y z γ * t / (2 * ħ)) : ℝ) : ℂ) := by
  have hz : genHalf y z γ ħ t
      = -(((((omegaGen y z γ * t / (2 * ħ)) : ℝ)) : ℂ) * Complex.I) := by
    unfold genHalf
    push_cast
    ring
  rw [hz, Complex.sinh_neg, Complex.sinh_mul_I, ← Complex.ofReal_sin]
  ring

/-- In the unbroken region with nonzero trigonometric denominators, decomposes `evolution4` into
a scalar exponential and a hyperbolic combination of the identity and `sigmaUnitGen`. -/
theorem evolution4_decomp (x y z γ ħ t : ℝ) (hsin : Real.sin γ ≠ 0)
    (hcos : Real.cos γ ≠ 0) (hunb : unbrokenPTGen y z γ) :
    evolution4 x y z γ ħ t
      = Complex.exp (genPhase x ħ t) •
          (Complex.cosh (genHalf y z γ ħ t) • (1 : Mat2)
            + Complex.sinh (genHalf y z γ ħ t) • sigmaUnitGen y z γ) := by
  have hω : omegaGen y z γ ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr hunb)
  have hsplit : (-(Complex.I * ((t / ħ : ℝ) : ℂ))) • H4 x y z γ
      = genPhase x ħ t • (1 : Mat2)
        + genHalf y z γ ħ t • sigmaUnitGen y z γ := by
    rw [H4_decomp_unit x y z γ hω, smul_add, smul_smul, smul_smul]
    rfl
  have hcomm : Commute (genPhase x ħ t • (1 : Mat2))
      (genHalf y z γ ħ t • sigmaUnitGen y z γ) :=
    Commute.smul_left (Commute.one_left (genHalf y z γ ħ t • sigmaUnitGen y z γ)) _
  rw [evolution4, hsplit, Matrix.exp_add_of_commute _ _ hcomm,
    Qatlib.Papers.FastHermitian06.MainResults.SpinFlip.exp_smul_one,
    Qatlib.Papers.ThermalDrift26.ThermalSampling.reflection_exp
      (sigmaUnitGen y z γ)
      (sigmaUnitGen_sq y z γ hsin hcos hunb) (genHalf y z γ ħ t)]
  rw [Matrix.smul_mul, Matrix.one_mul]

/-- Evaluates `sigmaNGen` on `ket0` as its explicit first column. -/
theorem sigmaNGen_mulVec_ket0 (y z γ : ℝ) :
    sigmaNGen y z γ *ᵥ ket0
      = ![ (z : ℂ) + (y : ℂ) * Complex.I,
           ((z / Real.tan γ : ℝ) : ℂ) - ((y * Real.tan γ : ℝ) : ℂ) * Complex.I ] := by
  ext i
  fin_cases i <;> simp [sigmaNGen, ket0, Matrix.mulVec]

/-- Evaluates `sigmaUnitGen` on `ket0` as `2 / omegaGen` times the first column of `sigmaNGen`. -/
theorem sigmaUnitGen_mulVec_ket0 (y z γ : ℝ) :
    sigmaUnitGen y z γ *ᵥ ket0
      = (((2 / omegaGen y z γ : ℝ)) : ℂ) •
          ![ (z : ℂ) + (y : ℂ) * Complex.I,
             ((z / Real.tan γ : ℝ) : ℂ) - ((y * Real.tan γ : ℝ) : ℂ) * Complex.I ] := by
  rw [sigmaUnitGen, Matrix.smul_mulVec, sigmaNGen_mulVec_ket0]

/-- The explicit two-coordinate trigonometric vector appearing after removal of the scalar phase
in equation (18) of [BenderEtAl2007]. -/
def bracket18 (y z γ ħ t : ℝ) : State2 :=
  ![ ((Real.cos (omegaGen y z γ * t / (2 * ħ)) : ℝ) : ℂ)
        + ((((2 * y) / omegaGen y z γ : ℝ)) : ℂ)
            * ((Real.sin (omegaGen y z γ * t / (2 * ħ)) : ℝ) : ℂ)
        - Complex.I * (((((2 * z) / omegaGen y z γ : ℝ)) : ℂ)
            * ((Real.sin (omegaGen y z γ * t / (2 * ħ)) : ℝ) : ℂ)),
     - ((((2 * y) / omegaGen y z γ : ℝ)) : ℂ) * ((Real.tan γ : ℝ) : ℂ)
          * ((Real.sin (omegaGen y z γ * t / (2 * ħ)) : ℝ) : ℂ)
        - Complex.I * (((((2 * z) / (omegaGen y z γ * Real.tan γ) : ℝ)) : ℂ)
            * ((Real.sin (omegaGen y z γ * t / (2 * ħ)) : ℝ) : ℂ)) ]

/-- The exponential of `genPhase` equals `cis (-(x * t / ħ))`. -/
theorem exp_genPhase (x ħ t : ℝ) :
    Complex.exp (genPhase x ħ t) = cis (-(x * t / ħ)) := by
  unfold genPhase cis
  congr 1
  push_cast
  ring

/-- The evolution of `ket0` equals `cis (-(x * t / ħ))` times `bracket18` under the stated gap
and denominator hypotheses. This is the state formula corresponding to equation (18) of
[BenderEtAl2007]. -/
theorem evolution18 (x y z γ ħ t : ℝ) (hsin : Real.sin γ ≠ 0)
    (hcos : Real.cos γ ≠ 0) (hunb : unbrokenPTGen y z γ) :
    evolution4 x y z γ ħ t *ᵥ ket0
      = cis (-(x * t / ħ)) • bracket18 y z γ ħ t := by
  rw [evolution4_decomp x y z γ ħ t hsin hcos hunb, exp_genPhase,
    Matrix.smul_mulVec, Matrix.add_mulVec, Matrix.smul_mulVec, Matrix.smul_mulVec,
    Matrix.one_mulVec, sigmaUnitGen_mulVec_ket0, cosh_genHalf, sinh_genHalf, bracket18]
  funext i
  fin_cases i <;>
    simp only [ket0, Pi.smul_apply, Pi.add_apply, Matrix.cons_val_zero',
      Matrix.cons_val_succ', Matrix.cons_val_fin_one, smul_eq_mul, mul_one, mul_zero,
      zero_add]
  · push_cast
    ring_nf
    rw [Defs.I_sq]
    ring
  · push_cast
    ring_nf
    rw [Defs.I_sq]
    ring

end Qatlib.Papers.FastHermitian06.MainResults.GeneralFinalState
