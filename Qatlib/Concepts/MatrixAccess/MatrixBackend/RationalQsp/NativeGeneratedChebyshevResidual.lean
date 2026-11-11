/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.MatrixAccess.MatrixBackend.RationalQsp.NativeChebyshevUniformAcceptance
import Qatlib.Concepts.MatrixAccess.MatrixBackend.PolynomialArrays.Public
import Qatlib.Concepts.MatrixAccess.MatrixBackend.PolynomialArrays.Verifier
import Qatlib.Concepts.MatrixAccess.MatrixBackend.NativeWords.RationalCircle
import Qatlib.Concepts.MatrixAccess.MatrixBackend.NativeWords.HouseholderRotationTable
import Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords.NativeHouseholder
import Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords.NativePhasePrecision

set_option backward.isDefEq.respectTransparency false

open Qatlib.Concepts.PhaseGeometry.RationalCayleyPhase

/-! The complete residual is computed from the same actual packet, not supplied
as a certificate. Exact zero tails remain represented and charged. This does
not prove a numerical phase producer succeeds or bound all execution bit costs. -/
set_option autoImplicit false
set_option maxHeartbeats 3000000
noncomputable section
namespace Qatlib.Concepts.MatrixAccess.MatrixBackend.RationalQsp.Data
open Qatlib.Concepts.MatrixAccess.MatrixBackend.PolynomialArrays Qatlib.Concepts.MatrixAccess.MatrixBackend.PolynomialArrays.SourceInput Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords.Prep Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords.Data Qatlib.Concepts.MatrixAccess.MatrixBackend.NativeWords

open Polynomial
open Qatlib.Concepts.NativeNumerics.PhaseSynthesis
open Qatlib.Concepts.SignalPrimitive.PhaseFrontend
open Qatlib.Concepts.TrotterFormula.SuzukiFourth

/-- The same emitted instruction list satisfies `ratAdd_length` with the displayed gate and query accounting. -/
private theorem ratAdd_length (xs ys : List ℚ) :
    (ratAddList xs ys).length=max xs.length ys.length := by
  induction xs generalizing ys with
  | nil => simp [ratAddList]
  | cons c cs ih => cases ys <;> simp [ratAddList,ih]

/-- The same emitted instruction list satisfies `ratSub_length` with the displayed gate and query accounting. -/
private theorem ratSub_length (xs ys : List ℚ) :
    (ratSubList xs ys).length=max xs.length ys.length := by
  induction xs generalizing ys with
  | nil => simp [ratSubList]
  | cons c cs ih => cases ys <;> simp [ratSubList,ih]

/-- The finite construction in `NativeGeneratedChebyshevResidual` satisfies `chebPoly_add` under the displayed hypotheses. -/
private theorem chebPoly_add (xs ys : List ℚ) (j : ℕ) :
    nativeChebyshevPolynomialFrom j (ratAddList xs ys)=
      nativeChebyshevPolynomialFrom j xs+nativeChebyshevPolynomialFrom j ys := by
  induction xs generalizing ys j with
  | nil => simp [ratAddList,nativeChebyshevPolynomialFrom]
  | cons c cs ih =>
    cases ys with
    | nil => simp [ratAddList,nativeChebyshevPolynomialFrom]
    | cons d ds =>
      simp only [ratAddList,nativeChebyshevPolynomialFrom,ih,Rat.cast_add,C_add]
      ring

/-- The finite construction in `NativeGeneratedChebyshevResidual` satisfies `chebPoly_scale` under the displayed hypotheses. -/
private theorem chebPoly_scale (cs : List ℚ) (a : ℚ) (j : ℕ) :
    nativeChebyshevPolynomialFrom j (cs.map (fun c => a*c))=
      C (a : ℝ)*nativeChebyshevPolynomialFrom j cs := by
  induction cs generalizing j with
  | nil => simp [nativeChebyshevPolynomialFrom]
  | cons c cs ih =>
    simp only [List.map_cons,nativeChebyshevPolynomialFrom,ih,Rat.cast_mul,C_mul]
    ring

/-- The finite construction in `NativeGeneratedChebyshevResidual` satisfies `chebPoly_three_term` under the displayed hypotheses. -/
private theorem chebPoly_three_term (cs : List ℚ) (j : ℕ) :
    2*X*nativeChebyshevPolynomialFrom (j+1) cs=
      nativeChebyshevPolynomialFrom j cs+nativeChebyshevPolynomialFrom (j+2) cs := by
  induction cs generalizing j with
  | nil => simp [nativeChebyshevPolynomialFrom]
  | cons c cs ih =>
    have h1 : ((j+1 : ℕ) : ℤ)=(j : ℤ)+1 := by omega
    have h2 : ((j+2 : ℕ) : ℤ)=(j : ℤ)+2 := by omega
    simp only [nativeChebyshevPolynomialFrom,h1,h2,Polynomial.Chebyshev.T_add_two]
    have ht := ih (j+1)
    linear_combination (norm := ring_nf) ht

/-- Exact multiplication by X in the actual Chebyshev coefficient basis. -/
def nativeChebyshevMulX : List ℚ → List ℚ
  | [] => []
  | c::cs => ratAddList (0::c::cs.map (fun q => (1/2 : ℚ)*q))
      (cs.map (fun q => (1/2 : ℚ)*q))

/-- The finite construction in `NativeGeneratedChebyshevResidual` satisfies `nativeChebyshevMulX_semantics` under the displayed hypotheses. -/
theorem nativeChebyshevMulX_semantics (cs : List ℚ) :
    nativeChebyshevPolynomialFrom 0 (nativeChebyshevMulX cs)=
      X*nativeChebyshevPolynomialFrom 0 cs := by
  cases cs with
  | nil => simp [nativeChebyshevMulX,nativeChebyshevPolynomialFrom]
  | cons c cs =>
    have h := chebPoly_three_term cs 0
    norm_num only [Nat.zero_add] at h
    have hC2 : (C (2 : ℝ) : Polynomial ℝ)=2 := by
      rw [show (2 : ℝ)=1+1 by norm_num,Polynomial.C_add]
      simp only [Polynomial.C_1]
      ring
    have hC : (C (1/2 : ℝ) : Polynomial ℝ)*2=1 := by
      calc
        _ = C (1/2 : ℝ)*C (2 : ℝ) := by rw [hC2]
        _ = C ((1/2 : ℝ)*2) := C_mul.symm
        _ = 1 := by norm_num
    have hh : X*nativeChebyshevPolynomialFrom 1 cs=
        C (1/2 : ℝ)*nativeChebyshevPolynomialFrom 0 cs+
        C (1/2 : ℝ)*nativeChebyshevPolynomialFrom 2 cs := by
      calc
        _ = (C (1/2 : ℝ)*2)*(X*nativeChebyshevPolynomialFrom 1 cs) := by rw [hC]; simp
        _ = C (1/2 : ℝ)*(2*X*nativeChebyshevPolynomialFrom 1 cs) := by ring
        _ = C (1/2 : ℝ)*(nativeChebyshevPolynomialFrom 0 cs+
          nativeChebyshevPolynomialFrom 2 cs) := by rw [h]
        _ = _ := by ring
    rw [nativeChebyshevMulX,chebPoly_add]
    simp only [nativeChebyshevPolynomialFrom,Rat.cast_zero,C_0,
      zero_mul,zero_add,chebPoly_scale]
    norm_num only [Rat.cast_div,Rat.cast_one,Rat.cast_ofNat,
      Polynomial.Chebyshev.T_one,Polynomial.Chebyshev.T_zero,mul_one]
    rw [mul_add,hh]
    ring

/-- The same emitted instruction list satisfies `nativeChebyshevMulX_length_le` with the displayed gate and query accounting. -/
theorem nativeChebyshevMulX_length_le (cs : List ℚ) :
    (nativeChebyshevMulX cs).length≤cs.length+1 := by
  cases cs with
  | nil => simp [nativeChebyshevMulX]
  | cons c cs =>
    rw [nativeChebyshevMulX,ratAdd_length]
    simp only [List.length_cons,List.length_map]
    omega

/-- Horner conversion of the entire actual power array, with no truncation. -/
def nativeChebyshevFromPower : List ℚ → List ℚ
  | [] => []
  | c::cs => ratAddList [c] (nativeChebyshevMulX (nativeChebyshevFromPower cs))

/-- The finite construction in `NativeGeneratedChebyshevResidual` satisfies `nativeChebyshevFromPower_semantics` under the displayed hypotheses. -/
theorem nativeChebyshevFromPower_semantics (cs : List ℚ) :
    nativeChebyshevPolynomialFrom 0 (nativeChebyshevFromPower cs)=realTarget cs := by
  induction cs with
  | nil => simp [nativeChebyshevFromPower,nativeChebyshevPolynomialFrom]
  | cons c cs ih =>
    rw [nativeChebyshevFromPower,chebPoly_add,nativeChebyshevMulX_semantics,ih,realTarget_cons]
    simp [nativeChebyshevPolynomialFrom]

/-- The same emitted instruction list satisfies `nativeChebyshevFromPower_length_le` with the displayed gate and query accounting. -/
theorem nativeChebyshevFromPower_length_le (cs : List ℚ) :
    (nativeChebyshevFromPower cs).length≤cs.length := by
  induction cs with
  | nil => simp [nativeChebyshevFromPower]
  | cons c cs ih =>
    rw [nativeChebyshevFromPower,ratAdd_length]
    have h := nativeChebyshevMulX_length_le (nativeChebyshevFromPower cs)
    simp only [List.length_cons,List.length_nil]
    omega

/-- The same emitted instruction list satisfies `gadd_length` with the displayed gate and query accounting. -/
private theorem gadd_length (xs ys : List GaussianRat) :
    (gaddList xs ys).length=max xs.length ys.length := by
  induction xs generalizing ys with
  | nil => simp [gaddList]
  | cons c cs ih => cases ys <;> simp [gaddList,ih]

/-- The same emitted instruction list satisfies `gsub_length` with the displayed gate and query accounting. -/
private theorem gsub_length (xs ys : List GaussianRat) :
    (gsubList xs ys).length=max xs.length ys.length := by
  induction xs generalizing ys with
  | nil => simp [gsubList]
  | cons c cs ih => cases ys <;> simp [gsubList,ih]

/-- The same emitted instruction list satisfies `nativeResponseRealCoefficients_length` with the displayed gate and query accounting. -/
theorem nativeResponseRealCoefficients_length (data : PhaseData) :
    (nativeResponseRealCoefficients data).length=data.phases.length+1 := by
  have hr (base : GaussianRat) (zs : List GaussianRat) :
      (responseData base zs).1.1.length=zs.length+1 ∧
      (responseData base zs).1.2.length=zs.length := by
    induction zs with
    | nil => simp [responseData]
    | cons z zs ih =>
      simp only [responseData,gscale,gshift,List.length_map,List.length_cons,
        gadd_length,gsub_length,ih.1,ih.2]
      constructor <;> omega
  simpa only [nativeResponseRealCoefficients,List.length_map] using (hr data.base data.phases).1

/-- The same emitted instruction list satisfies `chebPower_length` with the displayed gate and query accounting. -/
private theorem chebPower_length (n : ℕ) : (nativeChebyshevPower n).length=n+1 := by
  have hp (n : ℕ) : (nativeChebyshevPowerPair n).1.length=n+1 ∧
      (nativeChebyshevPowerPair n).2.length=n+2 := by
    induction n with
    | zero => simp [nativeChebyshevPowerPair]
    | succ n ih =>
      change (nativeChebyshevPowerPair n).2.length=(n+1)+1 ∧
        (ratSubList (0::(nativeChebyshevPowerPair n).2.map (fun q => 2*q))
          (nativeChebyshevPowerPair n).1).length=(n+1)+2
      constructor
      · exact ih.2
      · rw [ratSub_length,List.length_cons,List.length_map,ih.1,ih.2]
        omega
  exact (hp n).1

/-- The same emitted instruction list satisfies `chebPowerSum_length_le` with the displayed gate and query accounting. -/
private theorem chebPowerSum_length_le (cs : List ℚ) (j : ℕ) :
    (nativeChebyshevPowerSumFrom j cs).length≤j+cs.length := by
  induction cs generalizing j with
  | nil => simp [nativeChebyshevPowerSumFrom]
  | cons c cs ih =>
    rw [nativeChebyshevPowerSumFrom,ratAdd_length,List.length_map,chebPower_length]
    have h := ih (j+1)
    simp only [List.length_cons]
    omega

/-- Construction for native Generated Chebyshev Residual in the native generated chebyshev residual model. -/
def nativeGeneratedChebyshevResidual (target : List ℚ) (data : PhaseData) : List ℚ :=
  nativeChebyshevFromPower (ratSubList
    (nativeResponseRealCoefficients (nativePacketFromStandard data))
    (nativeChebyshevPowerSumFrom 0 target))

/-- The finite construction in `NativeGeneratedChebyshevResidual` satisfies `nativeGeneratedChebyshevResidual_identity` under the displayed hypotheses. -/
theorem nativeGeneratedChebyshevResidual_identity (target : List ℚ) (data : PhaseData) :
    realTarget (nativeResponseRealCoefficients (nativePacketFromStandard data))-
      nativeChebyshevPolynomialFrom 0 target=
    nativeChebyshevPolynomialFrom 0 (nativeGeneratedChebyshevResidual target data) := by
  rw [nativeGeneratedChebyshevResidual,nativeChebyshevFromPower_semantics,realTarget_sub,
    nativeChebyshevPowerSumFrom_semantics]

/-- The same emitted instruction list satisfies `nativeGeneratedChebyshevResidual_length_le` with the displayed gate and query accounting. -/
theorem nativeGeneratedChebyshevResidual_length_le (target : List ℚ) (data : PhaseData) :
    (nativeGeneratedChebyshevResidual target data).length≤
      max (data.phases.length+1) target.length := by
  have h := nativeChebyshevFromPower_length_le (ratSubList
    (nativeResponseRealCoefficients (nativePacketFromStandard data))
    (nativeChebyshevPowerSumFrom 0 target))
  rw [ratSub_length,nativeResponseRealCoefficients_length,nativePacketFromStandard_length] at h
  have ht := chebPowerSum_length_le target 0
  dsimp only [nativeGeneratedChebyshevResidual]
  exact h.trans (max_le_max (le_refl _) (by simpa using ht))

/-- All residual coefficients and the Boolean check come from this same actual
packet. The only scalar error premise is the backend uniform guarantee. -/
theorem nativeGeneratedChebyshevPacketCheck_of_uniform (target : List ℚ) (data : PhaseData)
    (E : ℚ) (u : ℝ) (hu : 0≤u)
    (hb : ‖gaussianRatComplex data.base‖=1)
    (hz : ∀ z∈data.phases,‖gaussianRatComplex z‖=1)
    (haccuracy : ∀ x∈Set.Icc (-1 : ℝ) 1,
      |((standardResponseP (gaussianRatComplex data.base)
        (data.phases.map gaussianRatComplex)).eval (x : ℂ)).im-
          (nativeChebyshevPolynomialFrom 0 target).eval x|≤u)
    (hbudget : 2*(max (data.phases.length+1) target.length : ℝ)*u≤(E : ℝ)) :
    nativeChebyshevPacketCheck target (nativeGeneratedChebyshevResidual target data) data E=true := by
  apply nativeChebyshevPacketCheck_of_uniform target _ data E u hb hz
    (nativeGeneratedChebyshevResidual_identity target data) haccuracy
  have hlen : ((nativeGeneratedChebyshevResidual target data).length : ℝ)≤
      (max (data.phases.length+1) target.length : ℝ) := by
    exact_mod_cast nativeGeneratedChebyshevResidual_length_le target data
  exact (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hlen (by norm_num)) hu).trans hbudget

/-- Requested backend tolerance from actual lengths, with a nonzero divisor
even for an empty phase/target table. No supplied successful budget. -/
def nativeGeneratedChebyshevTolerance (target : List ℚ) (data : PhaseData) (E : ℚ) : ℚ :=
  E/(2*(max (data.phases.length+1) target.length : ℚ))

/-- The estimate `nativeGeneratedChebyshevPacketCheck_precision` retains the actual parameter, input-error and normalization budgets. -/
theorem nativeGeneratedChebyshevPacketCheck_precision (target : List ℚ) (data : PhaseData)
    (E : ℚ) (hE : 0≤E)
    (hb : ‖gaussianRatComplex data.base‖=1)
    (hz : ∀ z∈data.phases,‖gaussianRatComplex z‖=1)
    (haccuracy : ∀ x∈Set.Icc (-1 : ℝ) 1,
      |((standardResponseP (gaussianRatComplex data.base)
        (data.phases.map gaussianRatComplex)).eval (x : ℂ)).im-
          (nativeChebyshevPolynomialFrom 0 target).eval x|≤
            (nativeGeneratedChebyshevTolerance target data E : ℝ)) :
    nativeChebyshevPacketCheck target (nativeGeneratedChebyshevResidual target data) data E=true := by
  have hmN : 0< max (data.phases.length+1) target.length :=
    lt_of_lt_of_le (Nat.succ_pos _) (le_max_left _ _)
  have hmQ : (0 : ℚ)<(max (data.phases.length+1) target.length : ℚ) := by exact_mod_cast hmN
  have huQ : 0≤nativeGeneratedChebyshevTolerance target data E :=
    div_nonneg hE (by positivity)
  apply nativeGeneratedChebyshevPacketCheck_of_uniform target data E _
    (by exact_mod_cast huQ) hb hz haccuracy
  have hbudget : 2*(max (data.phases.length+1) target.length : ℚ)*
      nativeGeneratedChebyshevTolerance target data E=E := by
    dsimp only [nativeGeneratedChebyshevTolerance]
    field_simp [ne_of_gt hmQ]
  exact_mod_cast le_of_eq hbudget

/-- Before the backend returns: choose tolerance from a planned phase-count
bound. The actual returned packet must then meet that bound. -/
def nativeChebyshevToleranceForDegree (target : List ℚ) (n : ℕ) (E : ℚ) : ℚ :=
  E/(2*(max (n+1) target.length : ℚ))

/-- The estimate `nativeGeneratedChebyshevPacketCheck_degree_precision` retains the actual parameter, input-error and normalization budgets. -/
theorem nativeGeneratedChebyshevPacketCheck_degree_precision
    (target : List ℚ) (n : ℕ) (data : PhaseData) (E : ℚ) (hE : 0≤E)
    (hlen : data.phases.length≤n)
    (hb : ‖gaussianRatComplex data.base‖=1)
    (hz : ∀ z∈data.phases,‖gaussianRatComplex z‖=1)
    (haccuracy : ∀ x∈Set.Icc (-1 : ℝ) 1,
      |((standardResponseP (gaussianRatComplex data.base)
        (data.phases.map gaussianRatComplex)).eval (x : ℂ)).im-
          (nativeChebyshevPolynomialFrom 0 target).eval x|≤
            (nativeChebyshevToleranceForDegree target n E : ℝ)) :
    nativeChebyshevPacketCheck target (nativeGeneratedChebyshevResidual target data) data E=true := by
  have hmN : 0< max (n+1) target.length := lt_of_lt_of_le (Nat.succ_pos _) (le_max_left _ _)
  have hmQ : (0 : ℚ)<(max (n+1) target.length : ℚ) := by exact_mod_cast hmN
  have huQ : 0≤nativeChebyshevToleranceForDegree target n E := div_nonneg hE (by positivity)
  have huR : (0 : ℝ)≤(nativeChebyshevToleranceForDegree target n E : ℝ) := by exact_mod_cast huQ
  apply nativeGeneratedChebyshevPacketCheck_of_uniform target data E _ huR hb hz haccuracy
  have hm : max (data.phases.length+1) target.length≤ max (n+1) target.length :=
    max_le_max (by omega) (le_refl _)
  have hmR : (max (data.phases.length+1) target.length : ℝ)≤(max (n+1) target.length : ℝ) := by
    exact_mod_cast hm
  have hbudget : 2*(max (n+1) target.length : ℚ)*nativeChebyshevToleranceForDegree target n E=E := by
    dsimp only [nativeChebyshevToleranceForDegree]
    field_simp [ne_of_gt hmQ]
  calc
    _ ≤ 2*(max (n+1) target.length : ℝ)*(nativeChebyshevToleranceForDegree target n E : ℝ) :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hmR (by norm_num)) huR
    _ = (E : ℝ) := by exact_mod_cast hbudget

end Qatlib.Concepts.MatrixAccess.MatrixBackend.RationalQsp.Data
