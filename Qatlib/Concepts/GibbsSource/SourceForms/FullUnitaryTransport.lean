/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Concepts.GibbsSource.SourceForms.FullSourceGapForm

@[expose] public section


/-! # Physical unitary transport of the finite source forms

Conjugation transports the actual thermal factors, their adjoints, and the
complete weighted Gram operator.  The source weights and the physical half
are unchanged.  Hilbert--Schmidt inner products and the normalized variance
are preserved on every complex input, not just on an eigenbasis.
-/

open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.QuantumGibbs.FormAlgebra
open Qatlib.Concepts.GibbsSource.FormAlgebra
open Qatlib.Concepts.GibbsSource.CkgBounds



namespace Qatlib.Concepts.GibbsSource.SourceForms

open Matrix
open scoped BigOperators MatrixOrder ComplexOrder

variable {D : ℕ}

/-- Physical change of operator coordinates. -/
noncomputable def fullUnitaryConj (U X : Operator D) : Operator D := U * X * Uᴴ

/-- Full Unitary Conj inverse for the stated finite source data. -/
theorem fullUnitaryConj_inverse (U X : Operator D) (hU : Uᴴ * U = 1) :
    fullUnitaryConj U (fullUnitaryConj Uᴴ X) = X := by
  have hUU : U * Uᴴ = 1 := mul_eq_one_comm.mp hU
  simp only [fullUnitaryConj, Matrix.conjTranspose_conjTranspose]
  calc
    _ = (U * Uᴴ) * X * (U * Uᴴ) := by noncomm_ring
    _ = X := by rw [hUU, Matrix.one_mul, Matrix.mul_one]

/-- Full Unitary Conj left Inverse for the stated finite source data. -/
theorem fullUnitaryConj_leftInverse (U X : Operator D) (hU : Uᴴ * U = 1) :
    fullUnitaryConj Uᴴ (fullUnitaryConj U X) = X := by
  simpa only [Matrix.conjTranspose_conjTranspose] using
    fullUnitaryConj_inverse Uᴴ X (by
      simpa only [Matrix.conjTranspose_conjTranspose] using mul_eq_one_comm.mp hU)

/-- Full Unitary Conj injective for the stated finite source data. -/
theorem fullUnitaryConj_injective (U : Operator D) (hU : Uᴴ * U = 1) :
    Function.Injective (fullUnitaryConj U) := by
  intro X Y h
  have he := congrArg (fullUnitaryConj Uᴴ) h
  simpa only [fullUnitaryConj_leftInverse U _ hU] using he

/-- Full Unitary Conj eq zero for the stated finite source data. -/
theorem fullUnitaryConj_eq_zero (U X : Operator D) (hU : Uᴴ * U = 1) :
    fullUnitaryConj U X = 0 ↔ X = 0 := by
  have hzero : fullUnitaryConj U (0 : Operator D) = 0 := by
    simp only [fullUnitaryConj, Matrix.mul_zero, Matrix.zero_mul]
  have he : fullUnitaryConj U X = fullUnitaryConj U 0 ↔ X = 0 :=
    (fullUnitaryConj_injective U hU).eq_iff
  simpa only [hzero] using he

/-- Full Unitary Conj mul for the stated finite source data. -/
theorem fullUnitaryConj_mul (U X Y : Operator D) (hU : Uᴴ * U = 1) :
    fullUnitaryConj U X * fullUnitaryConj U Y = fullUnitaryConj U (X * Y) := by
  rw [fullUnitaryConj, fullUnitaryConj, fullUnitaryConj,
    conj_mul_conj, hU, Matrix.mul_one]

/-- Full Unitary Conj hs Inner for the stated finite source data. -/
theorem fullUnitaryConj_hsInner (U X Y : Operator D) (hU : Uᴴ * U = 1) :
    hsInner (fullUnitaryConj U X) (fullUnitaryConj U Y) = hsInner X Y := by
  have hstar : (fullUnitaryConj U X)ᴴ = fullUnitaryConj U Xᴴ := by
    simp only [fullUnitaryConj, Matrix.conjTranspose_mul,
      Matrix.conjTranspose_conjTranspose, Matrix.mul_assoc]
  rw [hsInner, hstar, fullUnitaryConj_mul U Xᴴ Y hU]
  change Matrix.trace (U * (Xᴴ * Y) * Uᴴ) = Matrix.trace (Xᴴ * Y)
  rw [Matrix.trace_mul_comm, ← Matrix.mul_assoc,
    hU, Matrix.one_mul]

/-- Full Unitary Conj hs Var for the stated finite source data. -/
theorem fullUnitaryConj_hsVar (U W X : Operator D) (hU : Uᴴ * U = 1) :
    hsVar (fullUnitaryConj U W) (fullUnitaryConj U X) = hsVar W X := by
  simp only [hsVar, fullUnitaryConj_hsInner U _ _ hU]

/-- Full Unitary Conj sharp for the stated finite source data. -/
theorem fullUnitaryConj_sharp (U ρ B : Operator D)
    (hU : Uᴴ * U = 1) (hρ : ρ.PosDef) :
    sharp (fullUnitaryConj U ρ) (fullUnitaryConj U B) =
      fullUnitaryConj U (sharp ρ B) := by
  have hR : IsUnit (fourthRoot ρ) := by
    rw [Matrix.isUnit_iff_isUnit_det]
    exact isUnit_iff_ne_zero.mpr (fourthRoot_det_ne_zero hρ)
  simp only [sharp, fullUnitaryConj]
  rw [fourthRoot_conj U ρ hU hρ.posSemidef.nonneg,
    conj_inv U (fourthRoot ρ) hU hR,
    conj_mul_conj, hU, Matrix.mul_one,
    conj_mul_conj, hU, Matrix.mul_one]

/-- Full Unitary Conj flat for the stated finite source data. -/
theorem fullUnitaryConj_flat (U ρ B : Operator D)
    (hU : Uᴴ * U = 1) (hρ : ρ.PosDef) :
    flat (fullUnitaryConj U ρ) (fullUnitaryConj U B) =
      fullUnitaryConj U (flat ρ B) := by
  have hR : IsUnit (fourthRoot ρ) := by
    rw [Matrix.isUnit_iff_isUnit_det]
    exact isUnit_iff_ne_zero.mpr (fourthRoot_det_ne_zero hρ)
  simp only [flat, fullUnitaryConj]
  rw [fourthRoot_conj U ρ hU hρ.posSemidef.nonneg,
    conj_inv U (fourthRoot ρ) hU hR,
    conj_mul_conj, hU, Matrix.mul_one,
    conj_mul_conj, hU, Matrix.mul_one]

/-- The physical thermal factor acts by conjugation on every complex input. -/
theorem fullUnitaryConj_parentFactor (U ρ B X : Operator D)
    (hU : Uᴴ * U = 1) (hρ : ρ.PosDef) :
    parentFactor (fullUnitaryConj U ρ) (fullUnitaryConj U B)
        (fullUnitaryConj U X) = fullUnitaryConj U (parentFactor ρ B X) := by
  rw [parentFactor_apply, parentFactor_apply,
    fullUnitaryConj_sharp U ρ B hU hρ, fullUnitaryConj_flat U ρ B hU hρ,
    fullUnitaryConj_mul U _ _ hU, fullUnitaryConj_mul U _ _ hU]
  simp only [fullUnitaryConj, Matrix.mul_sub, Matrix.sub_mul]

/-- Full Unitary Conj parent Factor Adj for the stated finite source data. -/
theorem fullUnitaryConj_parentFactorAdj (U ρ B X : Operator D)
    (hU : Uᴴ * U = 1) (hρ : ρ.PosDef) :
    parentFactorAdj (fullUnitaryConj U ρ) (fullUnitaryConj U B)
        (fullUnitaryConj U X) = fullUnitaryConj U (parentFactorAdj ρ B X) := by
  have hstar : (fullUnitaryConj U B)ᴴ = fullUnitaryConj U Bᴴ := by
    simp only [fullUnitaryConj, Matrix.conjTranspose_mul,
      Matrix.conjTranspose_conjTranspose, Matrix.mul_assoc]
  rw [parentFactorAdj_apply, parentFactorAdj_apply, hstar,
    fullUnitaryConj_flat U ρ Bᴴ hU hρ, fullUnitaryConj_sharp U ρ Bᴴ hU hρ,
    fullUnitaryConj_mul U _ _ hU, fullUnitaryConj_mul U _ _ hU]
  simp only [fullUnitaryConj, Matrix.mul_sub, Matrix.sub_mul]

variable {ι : Type*} [Fintype ι]

/-- No change to frequencies, weights, or within-proposal interference. -/
theorem fullUnitaryConj_wplainForm (U ρ : Operator D) (w : ι → ι → ℝ)
    (A : ι → Operator D) (X : Operator D)
    (hU : Uᴴ * U = 1) (hρ : ρ.PosDef) :
    wplainForm w (fullUnitaryConj U ρ) (fun a => fullUnitaryConj U (A a))
      (fullUnitaryConj U X) = wplainForm w ρ A X := by
  simp only [wplainForm, fullUnitaryConj_parentFactor U ρ _ X hU hρ,
    fullUnitaryConj_hsInner U _ _ hU]

/-- Full Unitary Conj wdamped Form for the stated finite source data. -/
theorem fullUnitaryConj_wdampedForm (U ρ : Operator D) (w : ι → ι → ℝ)
    (β : ℝ) (ν : ι → ℝ) (A : ι → Operator D) (X : Operator D)
    (hU : Uᴴ * U = 1) (hρ : ρ.PosDef) :
    wdampedForm w β (fullUnitaryConj U ρ) ν (fun a => fullUnitaryConj U (A a))
      (fullUnitaryConj U X) = wdampedForm w β ρ ν A X := by
  simp only [wdampedForm, fullUnitaryConj_parentFactor U ρ _ X hU hρ,
    fullUnitaryConj_hsInner U _ _ hU]

/-- Full Unitary Conj source Plain Form for the stated finite source data. -/
theorem fullUnitaryConj_sourcePlainForm (U ρ : Operator D) (β : ℝ)
    (ν : ι → ℝ) (A : ι → Operator D) (X : Operator D)
    (hU : Uᴴ * U = 1) (hρ : ρ.PosDef) :
    ckgSourcePlainForm β (fullUnitaryConj U ρ) ν
      (fun a => fullUnitaryConj U (A a)) (fullUnitaryConj U X) =
        ckgSourcePlainForm β ρ ν A X :=
  fullUnitaryConj_wplainForm U ρ _ A X hU hρ

/-- Full Unitary Conj source Damped Form for the stated finite source data. -/
theorem fullUnitaryConj_sourceDampedForm (U ρ : Operator D) (β : ℝ)
    (ν : ι → ℝ) (A : ι → Operator D) (X : Operator D)
    (hU : Uᴴ * U = 1) (hρ : ρ.PosDef) :
    ckgSourceDampedForm β (fullUnitaryConj U ρ) ν
      (fun a => fullUnitaryConj U (A a)) (fullUnitaryConj U X) =
        ckgSourceDampedForm β ρ ν A X :=
  fullUnitaryConj_wdampedForm U ρ _ β ν A X hU hρ

/-- Full Unitary Conj parent Gram Fam Op for the stated finite source data. -/
theorem fullUnitaryConj_parentGramFamOp (U ρ : Operator D) (w : ι → ι → ℝ)
    (A : ι → Operator D) (X : Operator D)
    (hU : Uᴴ * U = 1) (hρ : ρ.PosDef) :
    parentGramFamOp w (fullUnitaryConj U ρ) (fun a => fullUnitaryConj U (A a))
      (fullUnitaryConj U X) = fullUnitaryConj U (parentGramFamOp w ρ A X) := by
  simp only [parentGramFamOp_apply,
    fullUnitaryConj_parentFactor U ρ _ X hU hρ,
    fullUnitaryConj_parentFactorAdj U ρ _ _ hU hρ]
  simp only [fullUnitaryConj, Matrix.mul_sum, Matrix.sum_mul,
    Matrix.mul_smul, Matrix.smul_mul]

end Qatlib.Concepts.GibbsSource.SourceForms
