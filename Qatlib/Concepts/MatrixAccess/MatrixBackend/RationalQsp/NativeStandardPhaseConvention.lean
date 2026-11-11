/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.NativeNumerics.PhaseSynthesis.GaussianResponseData
import Qatlib.Concepts.TrotterFormula.SuzukiFourth.QSP
import Qatlib.Concepts.MatrixAccess.MatrixBackend.PolynomialArrays.Public
import Qatlib.Concepts.MatrixAccess.MatrixBackend.PolynomialArrays.Verifier
import Qatlib.Concepts.MatrixAccess.MatrixBackend.NativeWords.RationalCircle
import Qatlib.Concepts.MatrixAccess.MatrixBackend.NativeWords.HouseholderRotationTable
import Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords.NativeHouseholder
import Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords.NativePhasePrecision

set_option backward.isDefEq.respectTransparency false

open Qatlib.Concepts.PhaseGeometry.RationalCayleyPhase

/-! Explicit convention adapter from W(x)=[[x,i*s],[i*s,x]] with imaginary
upper response to the native reflection recurrence with real upper response.
This adapter does not produce phase factors or certify an external backend cost. -/
set_option autoImplicit false
noncomputable section
namespace Qatlib.Concepts.MatrixAccess.MatrixBackend.RationalQsp.Data
open Qatlib.Concepts.MatrixAccess.MatrixBackend.PolynomialArrays Qatlib.Concepts.MatrixAccess.MatrixBackend.PolynomialArrays.SourceInput Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords.Prep Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords.Data Qatlib.Concepts.MatrixAccess.MatrixBackend.NativeWords

open Polynomial
open Qatlib.Concepts.NativeNumerics.PhaseSynthesis
open Qatlib.Concepts.TrotterFormula.SuzukiFourth

/-- Standard W(x) recurrence, with the lower component represented as s*Q. -/
def standardResponse (base : ℂ) : List ℂ → Polynomial ℂ × Polynomial ℂ
  | [] => (C base,0)
  | z::zs =>
    let pq := standardResponse base zs
    (C z*(X*pq.1+C Complex.I*(1-X^2)*pq.2),
      C (star z)*(C Complex.I*pq.1+X*pq.2))

/-- Construction for standard Response P in the native standard phase convention model. -/
def standardResponseP (base : ℂ) (zs : List ℂ) : Polynomial ℂ := (standardResponse base zs).1
/-- Construction for standard Response Q in the native standard phase convention model. -/
def standardResponseQ (base : ℂ) (zs : List ℂ) : Polynomial ℂ := (standardResponse base zs).2

/-- The upper standard response at the empty phase list is the constant base polynomial. -/
@[simp] theorem standardResponseP_nil (base : ℂ) : standardResponseP base []=C base := rfl
/-- The lower standard response vanishes at the empty phase list. -/
@[simp] theorem standardResponseQ_nil (base : ℂ) : standardResponseQ base []=0 := rfl
/-- The upper standard response follows the ordered W-matrix recurrence. -/
@[simp] theorem standardResponseP_cons (base z : ℂ) (zs : List ℂ) :
    standardResponseP base (z::zs)=C z*(X*standardResponseP base zs+
      C Complex.I*(1-X^2)*standardResponseQ base zs) := rfl
/-- The finite construction in `NativeStandardPhaseConvention` satisfies `standardResponseQ_cons` under the displayed hypotheses. -/
@[simp] theorem standardResponseQ_cons (base z : ℂ) (zs : List ℂ) :
    standardResponseQ base (z::zs)=C (star z)*(C Complex.I*standardResponseP base zs+
      X*standardResponseQ base zs) := rfl

/-- Uniform quarter-turn on all d+1 phases has a tracked degree-dependent phase.
The top response cannot be identified with the standard top response directly. -/
theorem native_standard_quarter_response (base : ℂ) (zs : List ℂ) :
    responseP ((-Complex.I)*base) (zs.map (fun z => (-Complex.I)*z))=
      C ((-Complex.I)^(zs.length+1))*standardResponseP base zs ∧
    responseQ ((-Complex.I)*base) (zs.map (fun z => (-Complex.I)*z))=
      C ((-Complex.I)^zs.length)*standardResponseQ base zs := by
  induction zs with
  | nil => simp
  | cons z zs ih =>
    constructor
    · rw [List.map_cons,responseP_cons,ih.1,ih.2,standardResponseP_cons]
      apply Polynomial.funext
      intro x
      simp only [List.length_cons,Polynomial.eval_mul,Polynomial.eval_add,
        Polynomial.eval_sub,Polynomial.eval_pow,Polynomial.eval_C,Polynomial.eval_X,
        Polynomial.eval_one,pow_succ]
      ring_nf
      simp [Complex.I_sq,Complex.I_pow_three]; ring
    · rw [List.map_cons,responseQ_cons,ih.1,ih.2,standardResponseQ_cons]
      apply Polynomial.funext
      intro x
      simp only [List.length_cons,Polynomial.eval_mul,Polynomial.eval_add,
        Polynomial.eval_sub,Polynomial.eval_C,Polynomial.eval_X,pow_succ,map_mul,map_neg,Complex.star_def,Complex.conj_I]
      ring_nf
      simp; ring

/-- Exact Gaussian quarter power, using only coordinate choices/signs. -/
def nativeQuarterPower (n : ℕ) : GaussianRat :=
  if n%4=0 then (1,0) else if n%4=1 then (0,1)
  else if n%4=2 then (-1,0) else (0,-1)

/-- The finite construction in `NativeStandardPhaseConvention` satisfies `nativeQuarterPower_complex` under the displayed hypotheses. -/
theorem nativeQuarterPower_complex (n : ℕ) : gaussianRatComplex (nativeQuarterPower n)=Complex.I^n := by
  rw [Complex.I_pow_eq_pow_mod]
  have hn : n%4<4 := Nat.mod_lt n (by decide)
  interval_cases h : n%4 <;> norm_num [nativeQuarterPower,h,gaussianRatComplex,Complex.I_sq,Complex.I_pow_three]

/-- Base is the last standard phase. The first phase has a different correction
from all subsequent phases; length and Gaussian rationality are preserved. -/
def nativePacketFromStandard (data : PhaseData) : PhaseData where
  base := gmul (0,-1) data.base
  phases := match data.phases with
    | [] => []
    | z::tail => gmul (nativeQuarterPower tail.length) z :: tail.map (gmul (0,-1))

/-- The same emitted instruction list satisfies `nativePacketFromStandard_length` with the displayed gate and query accounting. -/
theorem nativePacketFromStandard_length (data : PhaseData) :
    (nativePacketFromStandard data).phases.length=data.phases.length := by
  cases data with
  | mk base zs => cases zs <;> simp [nativePacketFromStandard]

/-- The finite construction in `NativeStandardPhaseConvention` satisfies `nativeMinusI_complex` under the displayed hypotheses. -/
@[simp] theorem nativeMinusI_complex : gaussianRatComplex ((0,-1) : GaussianRat)= -Complex.I := by
  norm_num [gaussianRatComplex]

/-- Complex semantics of the computable packet conversion. -/
def standardToNativePhases : List ℂ → List ℂ
  | [] => []
  | z::tail => Complex.I^tail.length*z :: tail.map (fun z => (-Complex.I)*z)

/-- The finite construction in `NativeStandardPhaseConvention` satisfies `quarter_power_cancel` under the displayed hypotheses. -/
private theorem quarter_power_cancel (n : ℕ) : Complex.I^n*(-Complex.I)^n=1 := by
  rw [←mul_pow]
  simp

/-- The finite construction in `NativeStandardPhaseConvention` satisfies `converted_response_head` under the displayed hypotheses. -/
private theorem converted_response_head (base : ℂ) (zs : List ℂ) :
    responseP ((-Complex.I)*base) (standardToNativePhases zs)=
      C (Complex.I^zs.length)*responseP ((-Complex.I)*base) (zs.map (fun z => (-Complex.I)*z)) := by
  cases zs with
  | nil => simp [standardToNativePhases]
  | cons z tail =>
    have hc : Complex.I^(tail.length+1)*((-Complex.I)*z)=Complex.I^tail.length*z := by
      rw [pow_succ]
      ring_nf
      simp [Complex.I_sq]
    simp only [standardToNativePhases,List.map_cons,List.length_cons,responseP_cons]
    rw [←mul_assoc,←Polynomial.C_mul,hc]

/-- The finite construction in `NativeStandardPhaseConvention` satisfies `nativePacketFromStandard_base_complex` under the displayed hypotheses. -/
theorem nativePacketFromStandard_base_complex (data : PhaseData) :
    gaussianRatComplex (nativePacketFromStandard data).base=(-Complex.I)*gaussianRatComplex data.base := by
  change gaussianRatComplex (gmul (0,-1) data.base)=_
  rw [complex_gmul,nativeMinusI_complex]

/-- The finite construction in `NativeStandardPhaseConvention` satisfies `nativePacketFromStandard_phases_complex` under the displayed hypotheses. -/
theorem nativePacketFromStandard_phases_complex (data : PhaseData) :
    (nativePacketFromStandard data).phases.map gaussianRatComplex=
      standardToNativePhases (data.phases.map gaussianRatComplex) := by
  cases data with
  | mk base zs => cases zs <;>
    simp [nativePacketFromStandard,standardToNativePhases,complex_gmul,nativeQuarterPower_complex,
      List.map_map,Function.comp_def]

/-- Whole polynomial identity, at every signal value and both query parities.
This is an explicit phase correction, not equality of the two full operators. -/
theorem nativePacketFromStandard_response (data : PhaseData) :
    responseP (gaussianRatComplex (nativePacketFromStandard data).base)
      ((nativePacketFromStandard data).phases.map gaussianRatComplex)=
    C (-Complex.I)*standardResponseP (gaussianRatComplex data.base)
      (data.phases.map gaussianRatComplex) := by
  rw [nativePacketFromStandard_base_complex,nativePacketFromStandard_phases_complex,
    converted_response_head,(native_standard_quarter_response _ _).1,←mul_assoc,←Polynomial.C_mul]
  have hp (n : ℕ) : Complex.I^n*(-Complex.I)^(n+1)= -Complex.I := by
    rw [pow_succ,←mul_assoc,quarter_power_cancel,one_mul]
  rw [hp]

/-- The finite construction in `NativeStandardPhaseConvention` satisfies `nativePacketFromStandard_real_imag` under the displayed hypotheses. -/
theorem nativePacketFromStandard_real_imag (data : PhaseData) (x : ℂ) :
    ((responseP (gaussianRatComplex (nativePacketFromStandard data).base)
      ((nativePacketFromStandard data).phases.map gaussianRatComplex)).eval x).re=
    ((standardResponseP (gaussianRatComplex data.base) (data.phases.map gaussianRatComplex)).eval x).im := by
  rw [nativePacketFromStandard_response,Polynomial.eval_mul,Polynomial.eval_C]
  simp [Complex.mul_re]

/-- A genuine uniform standard-response guarantee transfers with no error loss.
This does not create that guarantee or claim the external algorithm has run. -/
theorem nativePacketFromStandard_uniform (data : PhaseData) (f : ℝ → ℝ) (ε : ℝ)
    (h : ∀ x∈Set.Icc (-1 : ℝ) 1,
      |((standardResponseP (gaussianRatComplex data.base) (data.phases.map gaussianRatComplex)).eval
        (x : ℂ)).im-f x|≤ε) :
    ∀ x∈Set.Icc (-1 : ℝ) 1,
      |((responseP (gaussianRatComplex (nativePacketFromStandard data).base)
        ((nativePacketFromStandard data).phases.map gaussianRatComplex)).eval (x : ℂ)).re-f x|≤ε := by
  simpa only [nativePacketFromStandard_real_imag] using h

/-- The actual standard single-qubit phase matrix; false is the first index. -/
def standardPhaseMatrix (z : ℂ) : Matrix Bool Bool ℂ
  | false,false => z
  | true,true => star z
  | _,_ => 0

/-- Construction for standard Signal Matrix in the native standard phase convention model. -/
def standardSignalMatrix (x s : ℝ) : Matrix Bool Bool ℂ
  | false,false => x
  | true,true => x
  | _,_ => Complex.I*(s : ℂ)

/-- This is D(z0) W ... W D(base), in the literature's displayed order. -/
def standardMatrixWord (base : ℂ) (x s : ℝ) : List ℂ → Matrix Bool Bool ℂ
  | [] => standardPhaseMatrix base
  | z::zs => standardPhaseMatrix z*standardSignalMatrix x s*standardMatrixWord base x s zs

/-- The two polynomial recurrences are the actual first column of W's matrix
product, not merely another unconnected representation of a target function. -/
theorem standardMatrixWord_column (base : ℂ) (zs : List ℂ) (x s : ℝ)
    (hs : s*s=1-x*x) :
    standardMatrixWord base x s zs false false=(standardResponseP base zs).eval (x : ℂ) ∧
    standardMatrixWord base x s zs true false=
      (s : ℂ)*(standardResponseQ base zs).eval (x : ℂ) := by
  have hsc : (s : ℂ)*(s : ℂ)=1-(x : ℂ)*(x : ℂ) := by exact_mod_cast hs
  induction zs with
  | nil => simp [standardMatrixWord,standardPhaseMatrix]
  | cons z zs ih =>
    constructor
    · simp only [standardMatrixWord,Matrix.mul_apply,Fintype.sum_bool,
        standardPhaseMatrix,standardSignalMatrix,zero_mul,zero_add,
        standardResponseP_cons,Polynomial.eval_mul,Polynomial.eval_add,Polynomial.eval_sub,
        Polynomial.eval_pow,Polynomial.eval_C,Polynomial.eval_X,Polynomial.eval_one,ih.1,ih.2]
      linear_combination z*Complex.I*(standardResponseQ base zs).eval (x : ℂ)*hsc
    · simp only [standardMatrixWord,Matrix.mul_apply,Fintype.sum_bool,
        standardPhaseMatrix,standardSignalMatrix,zero_mul,add_zero,
        standardResponseQ_cons,Polynomial.eval_mul,Polynomial.eval_add,
        Polynomial.eval_C,Polynomial.eval_X,ih.1,ih.2]
      ring

/-- Exact unit Gaussian phases stay exact unit phases under coordinate sign/
quarter-turn changes. No floating normalization or extra signal query occurs. -/
theorem nativePacketFromStandard_unit (data : PhaseData)
    (hb : ‖gaussianRatComplex data.base‖=1)
    (hz : ∀ z∈data.phases,‖gaussianRatComplex z‖=1) :
    ‖gaussianRatComplex (nativePacketFromStandard data).base‖=1 ∧
      ∀ z∈(nativePacketFromStandard data).phases,‖gaussianRatComplex z‖=1 := by
  constructor
  · rw [nativePacketFromStandard_base_complex,norm_mul]
    simp [hb]
  · cases data with
    | mk base zs =>
      cases zs with
      | nil => simp [nativePacketFromStandard]
      | cons z tail =>
        intro w hw
        change w∈gmul (nativeQuarterPower tail.length) z :: tail.map (gmul (0,-1)) at hw
        rcases List.mem_cons.mp hw with h | h
        · subst w
          rw [complex_gmul,nativeQuarterPower_complex,norm_mul,norm_pow]
          simp [hz z (by simp)]
        · obtain ⟨v,hv,rfl⟩ := List.mem_map.mp h
          rw [complex_gmul,nativeMinusI_complex,norm_mul]
          simp [hz v (List.mem_cons_of_mem z hv)]

/-- Direct link to the literature's actual W-matrix product at any real signal
with s^2=1-x^2; in particular s=sqrt(1-x^2) on [-1,1]. -/
theorem nativePacketFromStandard_matrix_real_imag (data : PhaseData) (x s : ℝ)
    (hs : s*s=1-x*x) :
    ((responseP (gaussianRatComplex (nativePacketFromStandard data).base)
      ((nativePacketFromStandard data).phases.map gaussianRatComplex)).eval (x : ℂ)).re=
    (standardMatrixWord (gaussianRatComplex data.base) x s
      (data.phases.map gaussianRatComplex) false false).im := by
  rw [nativePacketFromStandard_real_imag,(standardMatrixWord_column _ _ _ _ hs).1]

end Qatlib.Concepts.MatrixAccess.MatrixBackend.RationalQsp.Data
