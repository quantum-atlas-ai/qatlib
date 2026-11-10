/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.FastHermitian06.MainResults.GeneralFinalState.Basic
import Qatlib.Papers.FastHermitian06.MainResults.SpinFlip
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Exponential
set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false
noncomputable section

open Matrix
open scoped BigOperators Matrix ComplexOrder

open Qatlib.Papers.FastHermitian06.MainResults.Defs

namespace Qatlib.Papers.FastHermitian06.MainResults.GeneralFinalState

open Qatlib.Papers.FastHermitian06.MainResults.Defs

def omegaGen (y z γ : ℝ) : ℝ := Real.sqrt (omegaSqGen y z γ)

def unbrokenPTGen (y z γ : ℝ) : Prop := 0 < omegaSqGen y z γ

theorem omegaGen_sq (y z γ : ℝ) (h : unbrokenPTGen y z γ) :
    omegaGen y z γ ^ 2 = omegaSqGen y z γ := by
  unfold omegaGen
  exact Real.sq_sqrt (le_of_lt h)

def sigmaUnitGen (y z γ : ℝ) : Mat2 :=
  (((2 / omegaGen y z γ : ℝ)) : ℂ) • sigmaNGen y z γ

theorem real_smul_eq_complex_smul (r : ℝ) (M : Mat2) :
    r • M = ((r : ℂ) • M) := by
  ext i j
  simp [Matrix.smul_apply]

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

theorem H4_decomp_unit (x y z γ : ℝ) (hω : omegaGen y z γ ≠ 0) :
    H4 x y z γ = (x : ℂ) • (1 : Mat2)
      + (((omegaGen y z γ / 2 : ℝ)) : ℂ) • sigmaUnitGen y z γ := by
  have hcoef : (((omegaGen y z γ / 2 : ℝ)) : ℂ) * (((2 / omegaGen y z γ : ℝ)) : ℂ)
      = 1 := by
    push_cast
    field_simp [hω]
  rw [H4_decomp, sigmaUnitGen, smul_smul, hcoef, one_smul]

def evolution4 (x y z γ ħ t : ℝ) : Mat2 :=
  NormedSpace.exp ((-(Complex.I * ((t / ħ : ℝ) : ℂ))) • H4 x y z γ)

def genPhase (x ħ t : ℝ) : ℂ :=
  (-(Complex.I * ((t / ħ : ℝ) : ℂ))) * (x : ℂ)

def genHalf (y z γ ħ t : ℝ) : ℂ :=
  (-(Complex.I * ((t / ħ : ℝ) : ℂ))) * (((omegaGen y z γ / 2 : ℝ)) : ℂ)

theorem cosh_genHalf (y z γ ħ t : ℝ) :
    Complex.cosh (genHalf y z γ ħ t)
      = ((Real.cos (omegaGen y z γ * t / (2 * ħ)) : ℝ) : ℂ) := by
  have hz : genHalf y z γ ħ t
      = -(((((omegaGen y z γ * t / (2 * ħ)) : ℝ)) : ℂ) * Complex.I) := by
    unfold genHalf
    push_cast
    ring
  rw [hz, Complex.cosh_neg, Complex.cosh_mul_I, ← Complex.ofReal_cos]

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

theorem sigmaNGen_mulVec_ket0 (y z γ : ℝ) :
    sigmaNGen y z γ *ᵥ ket0
      = ![ (z : ℂ) + (y : ℂ) * Complex.I,
           ((z / Real.tan γ : ℝ) : ℂ) - ((y * Real.tan γ : ℝ) : ℂ) * Complex.I ] := by
  ext i
  fin_cases i <;> simp [sigmaNGen, ket0, Matrix.mulVec]

theorem sigmaUnitGen_mulVec_ket0 (y z γ : ℝ) :
    sigmaUnitGen y z γ *ᵥ ket0
      = (((2 / omegaGen y z γ : ℝ)) : ℂ) •
          ![ (z : ℂ) + (y : ℂ) * Complex.I,
             ((z / Real.tan γ : ℝ) : ℂ) - ((y * Real.tan γ : ℝ) : ℂ) * Complex.I ] := by
  rw [sigmaUnitGen, Matrix.smul_mulVec, sigmaNGen_mulVec_ket0]

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

theorem exp_genPhase (x ħ t : ℝ) :
    Complex.exp (genPhase x ħ t) = cis (-(x * t / ħ)) := by
  unfold genPhase cis
  congr 1
  push_cast
  ring

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
