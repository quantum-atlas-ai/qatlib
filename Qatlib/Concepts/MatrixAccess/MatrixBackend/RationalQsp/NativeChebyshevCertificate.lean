/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.MatrixAccess.MatrixBackend.RationalQsp.NativeStandardPhaseWord
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Chebyshev.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Inverse
import Qatlib.Concepts.MatrixAccess.MatrixBackend.PolynomialArrays.Public
import Qatlib.Concepts.MatrixAccess.MatrixBackend.PolynomialArrays.Verifier
import Qatlib.Concepts.MatrixAccess.MatrixBackend.NativeWords.RationalCircle
import Qatlib.Concepts.MatrixAccess.MatrixBackend.NativeWords.HouseholderRotationTable
import Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords.NativeHouseholder
import Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords.NativePhasePrecision

set_option backward.isDefEq.respectTransparency false

open Qatlib.Concepts.PhaseGeometry.RationalCayleyPhase

/-! Exact posterior Chebyshev certificates for the actual Gaussian response.
Every monomial coefficient is compared, including all tails; no sampled
accuracy or monomial-L1 acceptance is substituted for Chebyshev accuracy. -/
set_option autoImplicit false
noncomputable section
namespace Qatlib.Concepts.MatrixAccess.MatrixBackend.RationalQsp.Data
open Qatlib.Concepts.MatrixAccess.MatrixBackend.PolynomialArrays Qatlib.Concepts.MatrixAccess.MatrixBackend.PolynomialArrays.SourceInput Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords.Prep Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords.Data Qatlib.Concepts.MatrixAccess.MatrixBackend.NativeWords

open Polynomial
open Qatlib.Concepts.NativeNumerics.PhaseSynthesis
open Qatlib.Concepts.SignalPrimitive.PhaseFrontend
open Qatlib.Concepts.TrotterFormula.SuzukiFourth

/-- Adjacent basis polynomials are carried together; the implementation does
not branch into two recursive calls for every T_n. This is not a bit-time proof. -/
def nativeChebyshevPowerPair : ℕ → List ℚ × List ℚ
  | 0 => ([1],[0,1])
  | n+1 =>
    let pq := nativeChebyshevPowerPair n
    (pq.2,ratSubList (0::pq.2.map (fun q => 2*q)) pq.1)

/-- Construction for native Chebyshev Power in the native chebyshev certificate model. -/
def nativeChebyshevPower (n : ℕ) : List ℚ := (nativeChebyshevPowerPair n).1

/-- The finite construction in `NativeChebyshevCertificate` satisfies `realTarget_twiceShift` under the displayed hypotheses. -/
private theorem realTarget_twiceShift (cs : List ℚ) :
    realTarget (0::cs.map (fun q => 2*q))=2*X*realTarget cs := by
  rw [realTarget_cons,realTarget_scale]
  have hC2 : (C (2 : ℝ) : Polynomial ℝ)=2 := by
    rw [show (2 : ℝ)=1+1 by norm_num,Polynomial.C_add]
    simp only [Polynomial.C_1]
    ring
  norm_num only [Rat.cast_ofNat,Rat.cast_zero,Polynomial.C_0,zero_add]
  rw [hC2]
  ring

/-- The finite construction in `NativeChebyshevCertificate` satisfies `nativeChebyshevPowerPair_semantics` under the displayed hypotheses. -/
theorem nativeChebyshevPowerPair_semantics (n : ℕ) :
    realTarget (nativeChebyshevPowerPair n).1=Polynomial.Chebyshev.T ℝ (n : ℤ) ∧
    realTarget (nativeChebyshevPowerPair n).2=Polynomial.Chebyshev.T ℝ ((n+1 : ℕ) : ℤ) := by
  induction n with
  | zero => simp [nativeChebyshevPowerPair,realTarget_cons]
  | succ n ih =>
    constructor
    · exact ih.2
    · change realTarget (ratSubList (0::(nativeChebyshevPowerPair n).2.map (fun q => 2*q))
        (nativeChebyshevPowerPair n).1)=_
      rw [realTarget_sub,realTarget_twiceShift,ih.1,ih.2]
      have hn1 : ((n+1 : ℕ) : ℤ)=(n : ℤ)+1 := by omega
      have hn2 : ((n+1+1 : ℕ) : ℤ)=(n : ℤ)+2 := by omega
      rw [hn1,hn2,Polynomial.Chebyshev.T_add_two]

/-- The finite construction in `NativeChebyshevCertificate` satisfies `nativeChebyshevPower_semantics` under the displayed hypotheses. -/
theorem nativeChebyshevPower_semantics (n : ℕ) :
    realTarget (nativeChebyshevPower n)=Polynomial.Chebyshev.T ℝ (n : ℤ) :=
  (nativeChebyshevPowerPair_semantics n).1

/-- Construction for native Chebyshev Polynomial From in the native chebyshev certificate model. -/
def nativeChebyshevPolynomialFrom (j : ℕ) : List ℚ → Polynomial ℝ
  | [] => 0
  | c::cs => C (c : ℝ)*Polynomial.Chebyshev.T ℝ (j : ℤ)+
      nativeChebyshevPolynomialFrom (j+1) cs

/-- Construction for native Chebyshev Power Sum From in the native chebyshev certificate model. -/
def nativeChebyshevPowerSumFrom (j : ℕ) : List ℚ → List ℚ
  | [] => []
  | c::cs => ratAddList ((nativeChebyshevPower j).map (fun a => c*a))
      (nativeChebyshevPowerSumFrom (j+1) cs)

/-- The finite construction in `NativeChebyshevCertificate` satisfies `nativeChebyshevPowerSumFrom_semantics` under the displayed hypotheses. -/
theorem nativeChebyshevPowerSumFrom_semantics (j : ℕ) (cs : List ℚ) :
    realTarget (nativeChebyshevPowerSumFrom j cs)=nativeChebyshevPolynomialFrom j cs := by
  induction cs generalizing j with
  | nil => simp [nativeChebyshevPowerSumFrom,nativeChebyshevPolynomialFrom]
  | cons c cs ih =>
    rw [nativeChebyshevPowerSumFrom,realTarget_add,realTarget_scale,
      nativeChebyshevPower_semantics,ih]
    rfl

/-- Construction for native Chebyshev Mass in the native chebyshev certificate model. -/
def nativeChebyshevMass (cs : List ℚ) : ℚ := (cs.map abs).sum

/-- The finite construction in `NativeChebyshevCertificate` satisfies `nativeChebyshevMass_nonneg` under the displayed hypotheses. -/
theorem nativeChebyshevMass_nonneg (cs : List ℚ) : 0≤nativeChebyshevMass cs := by
  apply List.sum_nonneg
  intro a ha
  obtain ⟨c,hc,rfl⟩ := List.mem_map.mp ha
  exact abs_nonneg c

/-- The estimate `nativeChebyshev_eval_bound` retains the actual parameter, input-error and normalization budgets. -/
theorem nativeChebyshev_eval_bound (j : ℕ) (x : ℝ) (hx : x∈Set.Icc (-1 : ℝ) 1) :
    |(Polynomial.Chebyshev.T ℝ (j : ℤ)).eval x|≤1 := by
  rw [←Real.cos_arccos hx.1 hx.2,Polynomial.Chebyshev.T_real_cos]
  exact Real.abs_cos_le_one _

/-- The estimate `nativeChebyshevPolynomialFrom_eval_bound` retains the actual parameter, input-error and normalization budgets. -/
theorem nativeChebyshevPolynomialFrom_eval_bound (j : ℕ) (cs : List ℚ)
    (x : ℝ) (hx : x∈Set.Icc (-1 : ℝ) 1) :
    |(nativeChebyshevPolynomialFrom j cs).eval x|≤(nativeChebyshevMass cs : ℝ) := by
  induction cs generalizing j with
  | nil => simp [nativeChebyshevPolynomialFrom,nativeChebyshevMass]
  | cons c cs ih =>
    have hterm : |(c : ℝ)*(Polynomial.Chebyshev.T ℝ (j : ℤ)).eval x|≤|(c : ℝ)| := by
      rw [abs_mul]
      exact (mul_le_mul_of_nonneg_left (nativeChebyshev_eval_bound j x hx)
        (abs_nonneg (c : ℝ))).trans_eq (mul_one _)
    simp only [nativeChebyshevPolynomialFrom,Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_C]
    have h := (abs_add_le _ _).trans (add_le_add hterm (ih (j+1)))
    simpa only [nativeChebyshevMass,List.map_cons,List.sum_cons,Rat.cast_add,Rat.cast_abs] using h

/-- All coefficients up to the larger actual array length; no degree truncation. -/
def nativeRationalCoefficientCheck (xs ys : List ℚ) : Bool :=
  decide (∀ i : Fin (max xs.length ys.length),xs.getD i.val 0=ys.getD i.val 0)

/-- The finite construction in `NativeChebyshevCertificate` satisfies `nativeRationalCoefficientCheck_sound` under the displayed hypotheses. -/
theorem nativeRationalCoefficientCheck_sound (xs ys : List ℚ)
    (h : nativeRationalCoefficientCheck xs ys=true) : realTarget xs=realTarget ys := by
  have hc : ∀ i : Fin (max xs.length ys.length),xs.getD i.val 0=ys.getD i.val 0 := of_decide_eq_true h
  ext i
  rw [realTarget_coeff,realTarget_coeff]
  by_cases hi : i< max xs.length ys.length
  · rw [hc ⟨i,hi⟩]
  · have hx : xs.length ≤ i := (le_max_left _ _).trans (le_of_not_gt hi)
    have hy : ys.length ≤ i := (le_max_right _ _).trans (le_of_not_gt hi)
    rw [List.getD_eq_default _ _ hx,List.getD_eq_default _ _ hy]

/-- The finite construction in `NativeChebyshevCertificate` satisfies `gaussian_realTarget_eval` under the displayed hypotheses. -/
theorem gaussian_realTarget_eval (cs : List GaussianRat) (x : ℝ) :
    (realTarget (cs.map Prod.fst)).eval x=((dataPolynomial cs).eval (x : ℂ)).re := by
  induction cs with
  | nil => simp
  | cons c cs ih =>
    rw [List.map_cons,realTarget_cons,dataPolynomial_cons]
    simp [Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_C,Polynomial.eval_X,
      gaussianRatComplex,Complex.mul_re,←ih]

/-- Construction for native Response Real Coefficients in the native chebyshev certificate model. -/
def nativeResponseRealCoefficients (data : PhaseData) : List ℚ :=
  ((responseData data.base data.phases).1.1).map Prod.fst

/-- The finite construction in `NativeChebyshevCertificate` satisfies `nativeResponseRealCoefficients_eval` under the displayed hypotheses. -/
theorem nativeResponseRealCoefficients_eval (data : PhaseData) (x : ℝ) :
    (realTarget (nativeResponseRealCoefficients data)).eval x=
      ((responseP (gaussianRatComplex data.base) (data.phases.map gaussianRatComplex)).eval (x : ℂ)).re := by
  rw [nativeResponseRealCoefficients,gaussian_realTarget_eval,
    (gaussian_response_native_coefficients data.base data.phases).1]

/-- Construction for native Chebyshev Residual Check in the native chebyshev certificate model. -/
def nativeChebyshevResidualCheck (target residual : List ℚ) (data : PhaseData) : Bool :=
  nativeRationalCoefficientCheck
    (ratSubList (nativeResponseRealCoefficients data) (nativeChebyshevPowerSumFrom 0 target))
    (nativeChebyshevPowerSumFrom 0 residual)

/-- Accepted residual means an identity for the actual full response polynomial;
its Chebyshev L1 mass then bounds the whole interval without a degree factor. -/
theorem nativeChebyshevResidualCheck_uniform (target residual : List ℚ) (data : PhaseData)
    (hcheck : nativeChebyshevResidualCheck target residual data=true) :
    ∀ x∈Set.Icc (-1 : ℝ) 1,
      |((responseP (gaussianRatComplex data.base) (data.phases.map gaussianRatComplex)).eval
        (x : ℂ)).re-(nativeChebyshevPolynomialFrom 0 target).eval x|≤
          (nativeChebyshevMass residual : ℝ) := by
  have hp := nativeRationalCoefficientCheck_sound _ _ hcheck
  rw [realTarget_sub,nativeChebyshevPowerSumFrom_semantics,
    nativeChebyshevPowerSumFrom_semantics] at hp
  intro x hx
  have he := congrArg (fun q : Polynomial ℝ => q.eval x) hp
  rw [Polynomial.eval_sub,nativeResponseRealCoefficients_eval] at he
  rw [he]
  exact nativeChebyshevPolynomialFrom_eval_bound 0 residual x hx

end Qatlib.Concepts.MatrixAccess.MatrixBackend.RationalQsp.Data
