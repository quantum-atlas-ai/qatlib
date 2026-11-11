/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.MatrixAccess.MatrixBackend.RationalQsp.NativeSourceStoredResponse
import Qatlib.Concepts.MatrixAccess.MatrixBackend.RationalQsp.NativeStandardPhaseStability
import Mathlib.Analysis.Fourier.AddCircle
import Qatlib.Concepts.MatrixAccess.MatrixBackend.PolynomialArrays.Public
import Qatlib.Concepts.MatrixAccess.MatrixBackend.PolynomialArrays.Verifier
import Qatlib.Concepts.MatrixAccess.MatrixBackend.NativeWords.RationalCircle
import Qatlib.Concepts.MatrixAccess.MatrixBackend.NativeWords.HouseholderRotationTable
import Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords.NativeHouseholder
import Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords.NativePhasePrecision

set_option backward.isDefEq.respectTransparency false

/-! Same original-input spectral completion: CompletionMatrix.
This does not certify the full proposer, iterative deflation, interpreter or fees. -/
set_option autoImplicit false
noncomputable section
namespace Qatlib.Concepts.MatrixAccess.MatrixBackend.RationalQsp.Data.SourceInput
open Qatlib.Concepts.MatrixAccess.MatrixBackend.PolynomialArrays Qatlib.Concepts.MatrixAccess.MatrixBackend.PolynomialArrays.SourceInput Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords.Prep Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords.Data Qatlib.Concepts.MatrixAccess.MatrixBackend.NativeWords


section CompletionPoint

open Qatlib.Concepts.MatrixAccess.MatrixBackend.RationalQsp.Data
open Qatlib.Concepts.MatrixAccess.MatrixBackend.RationalQsp.Data.SourceInput
open Qatlib.Concepts.BlockEncoding.Encoding
open scoped Matrix.Norms.L2Operator

/-- Construction for source Completion Point Matrix in the native source completion matrix model. -/
def sourceCompletionPointMatrix (a : ℝ) (v : ℂ) : Matrix Bool Bool ℂ :=
  (-(v.re : ℂ)) • (1 : Matrix Bool Bool ℂ)+
    (a : ℂ) • standardPhaseMatrix Complex.I+(v.im : ℂ) • standardSignalMatrix 0 1

/-- The finite construction in `NativeSourceCompletionMatrix` satisfies `sourceCompletionPointMatrix_entries` under the displayed hypotheses. -/
private theorem sourceCompletionPointMatrix_entries (a : ℝ) (v : ℂ) :
    sourceCompletionPointMatrix a v false false=-(v.re : ℂ)+Complex.I*(a : ℂ) ∧
      sourceCompletionPointMatrix a v false true=Complex.I*(v.im : ℂ) ∧
      sourceCompletionPointMatrix a v true false=Complex.I*(v.im : ℂ) ∧
      sourceCompletionPointMatrix a v true true=-(v.re : ℂ)-Complex.I*(a : ℂ) := by
  refine ⟨?_,?_,?_,?_⟩
  all_goals simp [sourceCompletionPointMatrix,standardPhaseMatrix,standardSignalMatrix]
  all_goals ring

/-- The estimate `sourceCompletionPointMatrix_error` retains the actual parameter, input-error and normalization budgets. -/
private theorem sourceCompletionPointMatrix_error (a : ℝ) (v w : ℂ) :
    ‖sourceCompletionPointMatrix a v-sourceCompletionPointMatrix a w‖ ≤ 2*‖v-w‖ := by
  have he : sourceCompletionPointMatrix a v-sourceCompletionPointMatrix a w=
      (-((v-w).re : ℂ)) • (1 : Matrix Bool Bool ℂ)+
        ((v-w).im : ℂ) • standardSignalMatrix 0 1 := by
    ext i j
    cases i <;> cases j <;>
      simp [sourceCompletionPointMatrix,standardPhaseMatrix,standardSignalMatrix,Matrix.smul_apply]
    all_goals ring
  have hJ : ‖standardSignalMatrix 0 1‖ ≤ 1 :=
    unitary_norm_le_one (standardSignalMatrix_unitary 0 1 (by norm_num))
  rw [he]
  calc
    _ ≤ ‖(-((v-w).re : ℂ)) • (1 : Matrix Bool Bool ℂ)‖+
        ‖((v-w).im : ℂ) • standardSignalMatrix 0 1‖ := norm_add_le _ _
    _ = |(v-w).re| *‖(1 : Matrix Bool Bool ℂ)‖+|(v-w).im| *‖standardSignalMatrix 0 1‖ := by
      rw [norm_smul,norm_smul,norm_neg,Complex.norm_real,Real.norm_eq_abs,
        Complex.norm_real,Real.norm_eq_abs]
    _ ≤ |(v-w).re|+|(v-w).im| := by
      have hI := matrix_one_norm_le (I := Bool)
      nlinarith [mul_le_mul_of_nonneg_left hI (abs_nonneg (v-w).re),
        mul_le_mul_of_nonneg_left hJ (abs_nonneg (v-w).im)]
    _ ≤ 2*‖v-w‖ := by linarith [Complex.abs_re_le_norm (v-w),Complex.abs_im_le_norm (v-w)]

/-- The actual finite word or frame satisfies `sourceCompletionPointMatrix_unitary` with all displayed legality, input and workspace hypotheses. -/
private theorem sourceCompletionPointMatrix_unitary (a : ℝ) (v : ℂ) (h : a^2+‖v‖^2=1) :
    sourceCompletionPointMatrix a v∈Matrix.unitaryGroup Bool ℂ := by
  have hs : a^2+v.re^2+v.im^2=1 := by
    rw [Complex.sq_norm,Complex.normSq_apply] at h
    nlinarith
  rw [Matrix.mem_unitaryGroup_iff,Matrix.star_eq_conjTranspose]
  ext i j
  cases i <;> cases j <;>
    simp [sourceCompletionPointMatrix,standardPhaseMatrix,standardSignalMatrix,Matrix.mul_apply,
      Matrix.conjTranspose_apply]
  all_goals apply Complex.ext
  all_goals simp [Complex.mul_re,Complex.mul_im]
  all_goals nlinarith

/-- Construction for source Completion Signal in the native source completion matrix model. -/
def sourceCompletionSignal (theta : ℝ) : ℂ := Complex.exp ((theta : ℂ)*Complex.I)
/-- Construction for source Ideal Completion Phase in the native source completion matrix model. -/
def sourceIdealCompletionPhase (cs : List ℚ) (N : ℕ) (E : ℚ) (theta : ℝ) : ℂ :=
  sourceIdealScaledResponse cs N E ((sourceCompletionSignal theta)^2)/(sourceCompletionSignal theta)^sourceDegree cs N E
/-- Construction for source Stored Completion Phase in the native source completion matrix model. -/
def sourceStoredCompletionPhase {m : ℕ} (cs : List ℚ) (N : ℕ) (E : ℚ)
    (f : Fin m → RootIntegerFactorData) (theta : ℝ) : ℂ :=
  sourceStoredScaledResponse cs N E f ((sourceCompletionSignal theta)^2)/(sourceCompletionSignal theta)^sourceDegree cs N E
/-- Construction for source Completion Response A in the native source completion matrix model. -/
def sourceCompletionResponseA (cs : List ℚ) (N : ℕ) (E : ℚ) (theta : ℝ) : ℝ :=
  (nativeChebyshevPolynomialFrom 0 (sourceOutputList cs N E)).eval (Real.cos theta)

/-- The finite construction in `NativeSourceCompletionMatrix` satisfies `signal_norm` under the displayed hypotheses. -/
private theorem signal_norm (theta : ℝ) : ‖sourceCompletionSignal theta‖=1 :=
  Complex.norm_exp_ofReal_mul_I theta

/-- The finite construction in `NativeSourceCompletionMatrix` satisfies `sourceIdealPhase_balance` under the displayed hypotheses. -/
theorem sourceIdealPhase_balance (cs : List ℚ) (N : ℕ) (E : ℚ) (hE : 0<E)
    (htail : ∀ k,N+1 ≤ k → cs.getD k 0=0)
    (hparity : ∀ j : Fin (N+1),j.val%2≠N%2 → cs.getD j.val 0=0)
    (hd : 0<sourceDegree cs N E)
    (hnorm : ∀ x∈Set.Icc (-1 : ℝ) 1,|(nativeChebyshevPolynomialFrom 0 cs).eval x| ≤ 1)
    (theta : ℝ) : (sourceCompletionResponseA cs N E theta)^2+‖sourceIdealCompletionPhase cs N E theta‖^2=1 := by
  let z : ℂ := Complex.exp (2*((theta : ℂ)*Complex.I))
  let phase : ℂ := Complex.exp ((sourceDegree cs N E : ℂ)*((theta : ℂ)*Complex.I))^2
  have hz2 : (sourceCompletionSignal theta)^2=z := by
    exact (Complex.exp_nat_mul ((theta : ℂ)*Complex.I) 2).symm
  have hz : ‖z‖=1 := by rw [← hz2,norm_pow,signal_norm,one_pow]
  have hp : z^sourceDegree cs N E=phase := by
    dsimp [z,phase]
    rw [← Complex.exp_nat_mul,← Complex.exp_nat_mul]
    congr 1
    ring
  have hn := sourceNormalizedSpectralIdentity cs N E hE htail hparity hd hnorm z hz
  rw [hp] at hn
  have he := sourceF_exp cs N E hparity hd theta
  have hphase : phase≠0 := pow_ne_zero 2 (Complex.exp_ne_zero _)
  have hc : (((sourceActualH1 cs N E : ℝ)*
      ‖sourceIdealProduct cs N E z/sourceIdealProduct cs N E 1‖^2 : ℝ) : ℂ)=
      ((1-(sourceCompletionResponseA cs N E theta)^2 : ℝ) : ℂ) := by
    apply mul_left_cancel₀ hphase
    push_cast
    calc
      _ = (sourceActualH1 cs N E : ℂ)*phase*
          ((‖sourceIdealProduct cs N E z/sourceIdealProduct cs N E 1‖^2 : ℝ) : ℂ) := by push_cast; ring
      _ = (sourceF cs N E).eval z := hn.symm
      _ = _ := by
        simpa only [sourceCompletionResponseA,Complex.ofReal_sub,Complex.ofReal_one,Complex.ofReal_pow] using he
  have hr : (sourceActualH1 cs N E : ℝ)*
      ‖sourceIdealProduct cs N E z/sourceIdealProduct cs N E 1‖^2=
      1-(sourceCompletionResponseA cs N E theta)^2 := Complex.ofReal_injective hc
  have hpos : (0 : ℝ) ≤ (sourceActualH1 cs N E : ℝ) := by
    exact_mod_cast (sourceActualH1_pos cs N E hE htail hnorm).le
  have hv : ‖sourceIdealCompletionPhase cs N E theta‖^2=(sourceActualH1 cs N E : ℝ)*
      ‖sourceIdealProduct cs N E z/sourceIdealProduct cs N E 1‖^2 := by
    unfold sourceIdealCompletionPhase sourceIdealScaledResponse
    rw [norm_div,norm_pow,signal_norm,one_pow,div_one,hz2,norm_div,norm_mul,
      Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (Real.sqrt_nonneg _),
      Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (norm_nonneg _),norm_div]
    rw [mul_div_assoc,mul_pow,Real.sq_sqrt hpos]
  rw [hv]
  linarith

/-- The actual finite word or frame satisfies `sourceIdealPoint_unitary` with all displayed legality, input and workspace hypotheses. -/
theorem sourceIdealPoint_unitary (cs : List ℚ) (N : ℕ) (E : ℚ) (hE : 0<E)
    (htail : ∀ k,N+1 ≤ k → cs.getD k 0=0)
    (hparity : ∀ j : Fin (N+1),j.val%2≠N%2 → cs.getD j.val 0=0)
    (hd : 0<sourceDegree cs N E)
    (hnorm : ∀ x∈Set.Icc (-1 : ℝ) 1,|(nativeChebyshevPolynomialFrom 0 cs).eval x| ≤ 1)
    (theta : ℝ) :
    sourceCompletionPointMatrix (sourceCompletionResponseA cs N E theta) (sourceIdealCompletionPhase cs N E theta)∈
      Matrix.unitaryGroup Bool ℂ :=
  sourceCompletionPointMatrix_unitary _ _ (sourceIdealPhase_balance cs N E hE htail hparity hd hnorm theta)

/-- The estimate `sourcePreRoundPoint_error` retains the actual parameter, input-error and normalization budgets. -/
theorem sourcePreRoundPoint_error (cs : List ℚ) (N : ℕ) (E : ℚ) (hE : 0<E)
    (htail : ∀ k,N+1 ≤ k → cs.getD k 0=0)
    (hparity : ∀ j : Fin (N+1),j.val%2≠N%2 → cs.getD j.val 0=0)
    (hd : 0<sourceDegree cs N E)
    (hnorm : ∀ x∈Set.Icc (-1 : ℝ) 1,|(nativeChebyshevPolynomialFrom 0 cs).eval x| ≤ 1)
    (m : ℕ) (content : ℤ) (f : Fin m → RootIntegerFactorData)
    (hcontent : content≠0)
    (hguard : rootIntegerFactorProduct content
      (List.ofFn (fun j => (List.ofFn (f j).coefficients,(f j).exponent)))=
        rootCanonicalCoefficients (sourceIntegerComplement cs N E))
    (haccepted : ∀ j,RootIntegerFactorGuards (f j) (sourceInputEta cs N E))
    (theta : ℝ) :
    ‖sourceCompletionPointMatrix (sourceCompletionResponseA cs N E theta) (sourceStoredCompletionPhase cs N E f theta)-
      sourceCompletionPointMatrix (sourceCompletionResponseA cs N E theta) (sourceIdealCompletionPhase cs N E theta)‖ ≤
      16*(((rootDecodedReturnList f (sourceInputEta cs N E)).length : ℝ)*
        (sourceInputEta cs N E : ℝ)/(rootDecodedCertificateGap f : ℝ))+
      (sourceInputEta cs N E : ℝ) := by
  have h := (sourceStoredScaled_error cs N E hE htail hparity hd hnorm m content f hcontent hguard haccepted).2
    ((sourceCompletionSignal theta)^2) (by rw [norm_pow,signal_norm,one_pow])
  have he : ‖sourceStoredCompletionPhase cs N E f theta-sourceIdealCompletionPhase cs N E theta‖=
      ‖sourceStoredScaledResponse cs N E f ((sourceCompletionSignal theta)^2)-sourceIdealScaledResponse cs N E ((sourceCompletionSignal theta)^2)‖ := by
    unfold sourceStoredCompletionPhase sourceIdealCompletionPhase
    rw [← sub_div,norm_div,norm_pow,signal_norm,one_pow,div_one]
  have hb := sourceCompletionPointMatrix_error (sourceCompletionResponseA cs N E theta)
    (sourceStoredCompletionPhase cs N E f theta) (sourceIdealCompletionPhase cs N E theta)
  rw [he] at hb
  linarith

end CompletionPoint

section Laurent

open Qatlib.Concepts.MatrixAccess.MatrixBackend.RationalQsp.Data
open Qatlib.Concepts.MatrixAccess.MatrixBackend.RationalQsp.Data.SourceInput
open scoped BigOperators

/-- Construction for source Completion Frequency in the native source completion matrix model. -/
def sourceCompletionFrequency {d : ℕ} (j : Fin (d+1)) : ℤ := 2*(j.val : ℤ)-(d : ℤ)
/-- Construction for character in the native source completion matrix model. -/
private def character (k : ℤ) (theta : ℝ) : ℂ :=
  Complex.exp ((k : ℂ)*((theta : ℂ)*Complex.I))
/-- Construction for laurent Value in the native source completion matrix model. -/
private def laurentValue {d : ℕ} (a : Fin (d+1) → ℂ) (theta : ℝ) : ℂ :=
  ∑ j, a j*character (sourceCompletionFrequency j) theta

/-- The finite construction in `NativeSourceCompletionMatrix` satisfies `frequency_rev` under the displayed hypotheses. -/
private theorem frequency_rev {d : ℕ} (j : Fin (d+1)) : sourceCompletionFrequency j.rev= -sourceCompletionFrequency j := by
  simp only [sourceCompletionFrequency,Fin.val_rev]
  omega

/-- The finite construction in `NativeSourceCompletionMatrix` satisfies `character_neg` under the displayed hypotheses. -/
private theorem character_neg (k : ℤ) (theta : ℝ) :
    character (-k) theta=star (character k theta) := by
  change Complex.exp _=(starRingEnd ℂ) (Complex.exp _)
  rw [← Complex.exp_conj]
  congr 1
  simp

/-- The finite construction in `NativeSourceCompletionMatrix` satisfies `laurentValue_reflect` under the displayed hypotheses. -/
private theorem laurentValue_reflect {d : ℕ} (a : Fin (d+1) → ℂ) (theta : ℝ) :
    laurentValue (fun j => star (a j.rev)) theta=star (laurentValue a theta) := by
  unfold laurentValue
  change (∑ j, star (a j.rev)*character (sourceCompletionFrequency j) theta)=
    (starRingEnd ℂ) (∑ j, a j*character (sourceCompletionFrequency j) theta)
  rw [map_sum]
  calc
    _ = ∑ j : Fin (d+1), star (a j)*character (sourceCompletionFrequency j.rev) theta := by
      exact Fintype.sum_equiv Fin.revPerm _ _ (fun j => by simp)
    _ = _ := by
      apply Finset.sum_congr rfl
      intro j _
      rw [frequency_rev,character_neg,map_mul]
      rfl

/-- The finite construction in `NativeSourceCompletionMatrix` satisfies `laurentValue_polynomial` under the displayed hypotheses. -/
private theorem laurentValue_polynomial {d : ℕ} (a : Fin (d+1) → ℂ) (theta : ℝ) :
    laurentValue a theta=(Polynomial.ofFn (d+1) a).eval ((sourceCompletionSignal theta)^2)/
      (sourceCompletionSignal theta)^d := by
  have hs : sourceCompletionSignal theta≠0 := Complex.exp_ne_zero _
  apply (eq_div_iff (pow_ne_zero d hs)).mpr
  rw [Polynomial.ofFn_eq_sum_monomial,Polynomial.eval_finsetSum]
  unfold laurentValue
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro j _
  simp only [Polynomial.eval_monomial,← pow_mul]
  have hx : character (sourceCompletionFrequency j) theta*(sourceCompletionSignal theta)^d=(sourceCompletionSignal theta)^(2*j.val) := by
    unfold character sourceCompletionSignal
    rw [← Complex.exp_nat_mul,← Complex.exp_nat_mul,← Complex.exp_add]
    congr 1
    simp only [sourceCompletionFrequency,Int.cast_sub,Int.cast_mul,Int.cast_ofNat,Int.cast_natCast,Nat.cast_mul,Nat.cast_ofNat]
    ring
  rw [mul_assoc,hx]

end Laurent

section CompletionArrays

open Qatlib.Concepts.MatrixAccess.MatrixBackend.RationalQsp.Data
open Qatlib.Concepts.MatrixAccess.MatrixBackend.RationalQsp.Data.SourceInput
open scoped BigOperators

/-- Construction for source Monic Array in the native source completion matrix model. -/
def sourceMonicArray {m : ℕ} (cs : List ℚ) (N : ℕ) (E : ℚ)
    (f : Fin m → RootIntegerFactorData) (j : Fin (sourceDegree cs N E+1)) : ℚ×ℚ :=
  (rootCompletionMonicCoefficients (rootDecodedReturnList f (sourceInputEta cs N E))).getD j.val (0,0)

/-- Construction for source Stored E in the native source completion matrix model. -/
def sourceStoredE {m : ℕ} (cs : List ℚ) (N : ℕ) (E : ℚ)
    (f : Fin m → RootIntegerFactorData) (j : Fin (sourceDegree cs N E+1)) : ℚ×ℚ :=
  (sourceStoredCompletionScale cs N E f*(sourceMonicArray cs N E f j).1,
    sourceStoredCompletionScale cs N E f*(sourceMonicArray cs N E f j).2)

/-- Construction for source Real Array in the native source completion matrix model. -/
def sourceRealArray (cs : List ℚ) (N : ℕ) (E : ℚ) : Fin (sourceDegree cs N E+1) → ℚ :=
  sourceP (sourceLiftedArray cs N E)

/-- The finite construction in `NativeSourceCompletionMatrix` satisfies `getD_polynomial` under the displayed hypotheses. -/
private theorem getD_polynomial (a : List (ℚ×ℚ)) (n : ℕ) (hlen : a.length=n) :
    Polynomial.ofFn n (fun j => rootRationalCoordinate (a.getD j.val (0,0)))=
      rootCompletionListPolynomial a := by
  subst n
  unfold rootCompletionListPolynomial rootCompletionStatePolynomial
  congr 1
  funext j
  rw [List.getD_eq_get a (0,0) j]

/-- The finite construction in `NativeSourceCompletionMatrix` satisfies `scale_decode` under the displayed hypotheses. -/
private theorem scale_decode (s : ℚ) (v : ℚ×ℚ) :
    rootRationalCoordinate (s*v.1,s*v.2)=(s : ℂ)*rootRationalCoordinate v := by
  apply Complex.ext <;> simp [rootRationalCoordinate]

/-- The finite construction in `NativeSourceCompletionMatrix` satisfies `eval_real_array` under the displayed hypotheses. -/
private theorem eval_real_array (cs : List ℚ) (N : ℕ) (E : ℚ) (z : ℂ) :
    (Polynomial.ofFn (sourceDegree cs N E+1) (fun j => (sourceRealArray cs N E j : ℂ))).eval z=
      (sourceInputP cs N E).eval₂ (Rat.castHom ℂ) z := by
  unfold sourceInputP sourceRealArray
  rw [Polynomial.ofFn_eq_sum_monomial,Polynomial.ofFn_eq_sum_monomial,
    Polynomial.eval_finsetSum,Polynomial.eval₂_finsetSum]
  simp only [Polynomial.eval_monomial,Polynomial.eval₂_monomial]
  rfl

/-- The finite construction in `NativeSourceCompletionMatrix` satisfies `sourceRealArray_value` under the displayed hypotheses. -/
private theorem sourceRealArray_value (cs : List ℚ) (N : ℕ) (E : ℚ)
    (hparity : ∀ j : Fin (N+1),j.val%2≠N%2 → cs.getD j.val 0=0)
    (hd : 0<sourceDegree cs N E) (theta : ℝ) :
    laurentValue (fun j => (sourceRealArray cs N E j : ℂ)) theta=(sourceCompletionResponseA cs N E theta : ℂ) := by
  rw [laurentValue_polynomial,eval_real_array]
  have hz : (sourceCompletionSignal theta)^2=Complex.exp (2*((theta : ℂ)*Complex.I)) :=
    (Complex.exp_nat_mul ((theta : ℂ)*Complex.I) 2).symm
  rw [hz,sourceInputP_circle cs N E hparity hd theta,sourceCompletionSignal,← Complex.exp_nat_mul]
  exact mul_div_cancel_left₀ _ (Complex.exp_ne_zero _)

/-- The finite construction in `NativeSourceCompletionMatrix` satisfies `sourceStoredE_value` under the displayed hypotheses. -/
private theorem sourceStoredE_value (cs : List ℚ) (N : ℕ) (E : ℚ) (hE : 0<E)
    (htail : ∀ k,N+1 ≤ k → cs.getD k 0=0)
    (hparity : ∀ j : Fin (N+1),j.val%2≠N%2 → cs.getD j.val 0=0)
    (hd : 0<sourceDegree cs N E)
    (hnorm : ∀ x∈Set.Icc (-1 : ℝ) 1,|(nativeChebyshevPolynomialFrom 0 cs).eval x| ≤ 1)
    (m : ℕ) (content : ℤ) (f : Fin m → RootIntegerFactorData)
    (hcontent : content≠0)
    (hguard : rootIntegerFactorProduct content
      (List.ofFn (fun j => (List.ofFn (f j).coefficients,(f j).exponent)))=
        rootCanonicalCoefficients (sourceIntegerComplement cs N E))
    (haccepted : ∀ j,RootIntegerFactorGuards (f j) (sourceInputEta cs N E))
    (theta : ℝ) :
    laurentValue (fun j => rootRationalCoordinate (sourceStoredE cs N E f j)) theta=
      sourceStoredCompletionPhase cs N E f theta := by
  have hlen : (rootCompletionMonicCoefficients
      (rootDecodedReturnList f (sourceInputEta cs N E))).length=sourceDegree cs N E+1 := by
    rw [rootCompletionMonicCoefficients_length,
      source_returned_length cs N E hE htail hparity hd hnorm m content f hcontent hguard haccepted]
  have he : laurentValue (fun j => rootRationalCoordinate (sourceStoredE cs N E f j)) theta=
      (sourceStoredCompletionScale cs N E f : ℂ)*laurentValue (fun j => rootRationalCoordinate (sourceMonicArray cs N E f j)) theta := by
    simp only [laurentValue,sourceStoredE,scale_decode,Finset.mul_sum,mul_assoc]
  rw [he,laurentValue_polynomial]
  unfold sourceMonicArray
  rw [getD_polynomial _ _ hlen]
  unfold sourceStoredCompletionPhase sourceStoredScaledResponse sourceReturnedRootProduct
  ring

end CompletionArrays

section CompletionRawMatrix

open Qatlib.Concepts.MatrixAccess.MatrixBackend.RationalQsp.Data
open Qatlib.Concepts.MatrixAccess.MatrixBackend.RationalQsp.Data.SourceInput
open scoped BigOperators Matrix.Norms.L2Operator

/-- Construction for qscale in the native source completion matrix model. -/
private def qscale (a : ℚ) (v : ℚ×ℚ) : ℚ×ℚ := (a*v.1,a*v.2)
/-- Construction for qconj in the native source completion matrix model. -/
private def qconj (v : ℚ×ℚ) : ℚ×ℚ := (v.1,-v.2)
/-- Construction for qraw in the native source completion matrix model. -/
private def qraw (a : ℚ) (v w : ℚ×ℚ) : Matrix Bool Bool (ℚ×ℚ) :=
  let C := qscale (1/2) (v+w)
  let S := gaussianRatMul (0,-1/2) (v-w)
  let upper := (a,0)+gaussianRatMul (0,1) C
  let lower := (a,0)-gaussianRatMul (0,1) C
  fun i j => match i,j with
    | false,false => gaussianRatMul (0,1) upper
    | true,true => gaussianRatMul (0,-1) lower
    | _,_ => gaussianRatMul (0,1) S

/-- Construction for raw Entry in the native source completion matrix model. -/
private def rawEntry (a v w : ℂ) : Matrix Bool Bool ℂ :=
  fun i j => match i,j with
    | false,false => Complex.I*a-(v+w)/2
    | true,true => -Complex.I*a-(v+w)/2
    | _,_ => (v-w)/2

/-- Construction for source Completion Laurent Matrix in the native source completion matrix model. -/
def sourceCompletionLaurentMatrix {d : ℕ} (a : Fin (d+1) → Matrix Bool Bool ℂ) (theta : ℝ) :
    Matrix Bool Bool ℂ := ∑ j,character (sourceCompletionFrequency j) theta • a j

/-- Construction for source Raw Matrix in the native source completion matrix model. -/
def sourceRawMatrix {m : ℕ} (cs : List ℚ) (N : ℕ) (E : ℚ)
    (f : Fin m → RootIntegerFactorData) (j : Fin (sourceDegree cs N E+1)) :
    Matrix Bool Bool (ℚ×ℚ) :=
  qraw (sourceRealArray cs N E j) (sourceStoredE cs N E f j) (qconj (sourceStoredE cs N E f j.rev))

/-- The finite construction in `NativeSourceCompletionMatrix` satisfies `qraw_decode` under the displayed hypotheses. -/
private theorem qraw_decode (a : ℚ) (v w : ℚ×ℚ) :
    (fun i j => rootRationalCoordinate (qraw a v w i j))=
      rawEntry (a : ℂ) (rootRationalCoordinate v) (rootRationalCoordinate w) := by
  ext i j
  cases i <;> cases j <;>
    apply Complex.ext <;>
    simp [qraw,qscale,rawEntry,gaussianRatMul,rootRationalCoordinate] <;> ring

/-- The finite construction in `NativeSourceCompletionMatrix` satisfies `qconj_decode` under the displayed hypotheses. -/
private theorem qconj_decode (v : ℚ×ℚ) : rootRationalCoordinate (qconj v)=star (rootRationalCoordinate v) := by
  apply Complex.ext <;> simp [qconj,rootRationalCoordinate]

/-- The finite construction in `NativeSourceCompletionMatrix` satisfies `rawEntry_conj` under the displayed hypotheses. -/
private theorem rawEntry_conj (a : ℝ) (v : ℂ) :
    rawEntry (a : ℂ) v (star v)=sourceCompletionPointMatrix a v := by
  ext i j
  cases i <;> cases j <;>
    apply Complex.ext <;>
    simp [rawEntry,sourceCompletionPointMatrix,standardPhaseMatrix,standardSignalMatrix]

/-- The finite construction in `NativeSourceCompletionMatrix` satisfies `rawEntry_value` under the displayed hypotheses. -/
private theorem rawEntry_value {d : ℕ} (a v w : Fin (d+1) → ℂ) (theta : ℝ) :
    sourceCompletionLaurentMatrix (fun j => rawEntry (a j) (v j) (w j)) theta=
      rawEntry (laurentValue a theta) (laurentValue v theta) (laurentValue w theta) := by
  ext i j
  cases i <;> cases j <;>
    simp [sourceCompletionLaurentMatrix,rawEntry,laurentValue,Matrix.sum_apply,Matrix.smul_apply,smul_eq_mul,
      div_eq_mul_inv,mul_add,add_mul,mul_sub,sub_mul,Finset.sum_add_distrib,
      Finset.sum_sub_distrib,Finset.mul_sum,mul_assoc,mul_comm,mul_left_comm]

/-- The finite construction in `NativeSourceCompletionMatrix` satisfies `sourceRawMatrix_value` under the displayed hypotheses. -/
theorem sourceRawMatrix_value (cs : List ℚ) (N : ℕ) (E : ℚ) (hE : 0<E)
    (htail : ∀ k,N+1 ≤ k → cs.getD k 0=0)
    (hparity : ∀ j : Fin (N+1),j.val%2≠N%2 → cs.getD j.val 0=0)
    (hd : 0<sourceDegree cs N E)
    (hnorm : ∀ x∈Set.Icc (-1 : ℝ) 1,|(nativeChebyshevPolynomialFrom 0 cs).eval x| ≤ 1)
    (m : ℕ) (content : ℤ) (f : Fin m → RootIntegerFactorData)
    (hcontent : content≠0)
    (hguard : rootIntegerFactorProduct content
      (List.ofFn (fun j => (List.ofFn (f j).coefficients,(f j).exponent)))=
        rootCanonicalCoefficients (sourceIntegerComplement cs N E))
    (haccepted : ∀ j,RootIntegerFactorGuards (f j) (sourceInputEta cs N E))
    (theta : ℝ) :
    sourceCompletionLaurentMatrix (fun j i k => rootRationalCoordinate (sourceRawMatrix cs N E f j i k)) theta=
      sourceCompletionPointMatrix (sourceCompletionResponseA cs N E theta) (sourceStoredCompletionPhase cs N E f theta) := by
  have he := sourceStoredE_value cs N E hE htail hparity hd hnorm m content f hcontent hguard haccepted theta
  have ha := sourceRealArray_value cs N E hparity hd theta
  have hw : laurentValue (fun j => star (rootRationalCoordinate (sourceStoredE cs N E f j.rev))) theta=
      star (sourceStoredCompletionPhase cs N E f theta) := by
    rw [laurentValue_reflect (fun j => rootRationalCoordinate (sourceStoredE cs N E f j)),he]
  have hraw : (fun j i k => rootRationalCoordinate (sourceRawMatrix cs N E f j i k))=
      (fun j => rawEntry (sourceRealArray cs N E j : ℂ) (rootRationalCoordinate (sourceStoredE cs N E f j))
        (star (rootRationalCoordinate (sourceStoredE cs N E f j.rev)))) := by
    funext j
    rw [sourceRawMatrix,qraw_decode,qconj_decode]
  rw [hraw,rawEntry_value,ha,he,hw,rawEntry_conj]

/-- The estimate `sourceRawMatrix_point_error` retains the actual parameter, input-error and normalization budgets. -/
theorem sourceRawMatrix_point_error (cs : List ℚ) (N : ℕ) (E : ℚ) (hE : 0<E)
    (htail : ∀ k,N+1 ≤ k → cs.getD k 0=0)
    (hparity : ∀ j : Fin (N+1),j.val%2≠N%2 → cs.getD j.val 0=0)
    (hd : 0<sourceDegree cs N E)
    (hnorm : ∀ x∈Set.Icc (-1 : ℝ) 1,|(nativeChebyshevPolynomialFrom 0 cs).eval x| ≤ 1)
    (m : ℕ) (content : ℤ) (f : Fin m → RootIntegerFactorData)
    (hcontent : content≠0)
    (hguard : rootIntegerFactorProduct content
      (List.ofFn (fun j => (List.ofFn (f j).coefficients,(f j).exponent)))=
        rootCanonicalCoefficients (sourceIntegerComplement cs N E))
    (haccepted : ∀ j,RootIntegerFactorGuards (f j) (sourceInputEta cs N E))
    (theta : ℝ) :
    ‖sourceCompletionLaurentMatrix (fun j i k => rootRationalCoordinate (sourceRawMatrix cs N E f j i k)) theta-
      sourceCompletionPointMatrix (sourceCompletionResponseA cs N E theta) (sourceIdealCompletionPhase cs N E theta)‖ ≤
      16*(((rootDecodedReturnList f (sourceInputEta cs N E)).length : ℝ)*
        (sourceInputEta cs N E : ℝ)/(rootDecodedCertificateGap f : ℝ))+
      (sourceInputEta cs N E : ℝ) := by
  rw [sourceRawMatrix_value cs N E hE htail hparity hd hnorm m content f hcontent hguard haccepted theta]
  exact sourcePreRoundPoint_error cs N E hE htail hparity hd hnorm m content f hcontent hguard haccepted theta

end CompletionRawMatrix

section FourierCoefficient

open MeasureTheory
open scoped BigOperators
/-- Typeclass instance for spectral Fourier Period Positive in the native source completion matrix model. -/
local instance spectralFourierPeriodPositive : Fact (0<2*Real.pi) := ⟨Real.two_pi_pos⟩

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V] [CompleteSpace V]

/-- Construction for circle Value in the native source completion matrix model. -/
private def circleValue {d : ℕ} (a : Fin (d+1) → V) (t : AddCircle (2*Real.pi)) : V :=
  ∑ j, fourier (sourceCompletionFrequency j) t • a j

/-- The finite construction in `NativeSourceCompletionMatrix` satisfies `frequency_injective` under the displayed hypotheses. -/
private theorem frequency_injective {d : ℕ} : Function.Injective (@sourceCompletionFrequency d) := by
  intro i j h
  apply Fin.ext
  dsimp [sourceCompletionFrequency] at h
  omega

omit [CompleteSpace V] in
/-- The finite construction in `NativeSourceCompletionMatrix` satisfies `continuous_term` under the displayed hypotheses. -/
private theorem continuous_term (k : ℤ) (a : V) :
    Continuous (fun t : AddCircle (2*Real.pi) => fourier k t • a) :=
  (map_continuous (fourier k)).smul continuous_const

omit [CompleteSpace V] in
/-- The finite construction in `NativeSourceCompletionMatrix` satisfies `term_integrable` under the displayed hypotheses. -/
private theorem term_integrable (k : ℤ) (a : V) :
    Integrable (fun t : AddCircle (2*Real.pi) => fourier k t • a) AddCircle.haarAddCircle :=
  (continuous_term k a).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)

/-- The finite construction in `NativeSourceCompletionMatrix` satisfies `term_coefficient` under the displayed hypotheses. -/
private theorem term_coefficient (k n : ℤ) (a : V) :
    fourierCoeff (fun t : AddCircle (2*Real.pi) => fourier k t • a) n=
      if n=k then a else 0 := by
  have he : fourierCoeff (fun t : AddCircle (2*Real.pi) => fourier k t • a) n=
      (fourierCoeff (T := 2*Real.pi) (fourier k) n) • a := by
    unfold fourierCoeff
    simp only [← smul_assoc,smul_eq_mul]
    rw [integral_smul_const]
  rw [he,fourierCoeff_fourier]
  by_cases h : n=k
  · subst n; simp
  · simp [h]

omit [CompleteSpace V] in
/-- The finite construction in `NativeSourceCompletionMatrix` satisfies `circleValue_integrable` under the displayed hypotheses. -/
private theorem circleValue_integrable {d : ℕ} (a : Fin (d+1) → V) :
    Integrable (circleValue a) AddCircle.haarAddCircle := by
  exact integrable_finsetSum _ (fun j _ => term_integrable (sourceCompletionFrequency j) (a j))

/-- The finite construction in `NativeSourceCompletionMatrix` satisfies `circleValue_coefficient` under the displayed hypotheses. -/
private theorem circleValue_coefficient {d : ℕ} (a : Fin (d+1) → V) (j : Fin (d+1)) :
    fourierCoeff (circleValue a) (sourceCompletionFrequency j)=a j := by
  have he : circleValue a=∑ i : Fin (d+1),fun t : AddCircle (2*Real.pi) => fourier (sourceCompletionFrequency i) t • a i := by
    funext t
    simp [circleValue]
  rw [he,fourierCoeff.sum _ _ (fun i _ => term_integrable (sourceCompletionFrequency i) (a i))]
  simp only [Finset.sum_apply,term_coefficient,frequency_injective.eq_iff]
  simp

/-- The finite construction in `NativeSourceCompletionMatrix` satisfies `fourier_character` under the displayed hypotheses. -/
private theorem fourier_character (k : ℤ) (theta : ℝ) :
    fourier (T := 2*Real.pi) k (theta : AddCircle (2*Real.pi))=character k theta := by
  rw [fourier_coe_apply]
  unfold character
  congr 1
  push_cast
  field_simp [Complex.ofReal_ne_zero.mpr Real.pi_ne_zero]

/-- The estimate `coefficient_error` retains the actual parameter, input-error and normalization budgets. -/
private theorem coefficient_error {d : ℕ} (a : Fin (d+1) → V)
    (g : AddCircle (2*Real.pi) → V) (hg : Integrable g AddCircle.haarAddCircle)
    (b : ℝ) (h : ∀ t : AddCircle (2*Real.pi),‖circleValue a t-g t‖ ≤ b)
    (j : Fin (d+1)) : ‖a j-fourierCoeff g (sourceCompletionFrequency j)‖ ≤ b := by
  have hi : ∀ᵐ t : AddCircle (2*Real.pi) ∂AddCircle.haarAddCircle,
      ‖fourier (-sourceCompletionFrequency j) t • (circleValue a t-g t)‖ ≤ b := by
    apply ae_of_all
    intro t
    rw [norm_smul,fourier_apply,Circle.norm_coe,one_mul]
    exact h t
  have hb : ‖∫ t : AddCircle (2*Real.pi), fourier (-sourceCompletionFrequency j) t •
      (circleValue a t-g t) ∂AddCircle.haarAddCircle‖ ≤ b := by
    simpa using norm_integral_le_of_norm_le_const hi
  simp only [smul_sub] at hb
  rw [integral_sub ((circleValue_integrable a).fourier_smul _) (hg.fourier_smul _)] at hb
  change ‖fourierCoeff (circleValue a) (sourceCompletionFrequency j)-fourierCoeff g (sourceCompletionFrequency j)‖ ≤ b at hb
  rwa [circleValue_coefficient] at hb

end FourierCoefficient

section MatrixRounding

open Qatlib.Concepts.MatrixAccess.MatrixBackend.RationalQsp.Data
open Qatlib.Concepts.BlockEncoding.Encoding
open scoped Matrix.Norms.L2Operator

/-- Construction for round Matrix in the native source completion matrix model. -/
private def roundMatrix (a : Matrix Bool Bool (ℚ×ℚ)) (eta : ℚ) : Matrix Bool Bool (ℚ×ℚ) :=
  fun i j => rootGridPoint (a i j) (eta/8)

/-- Construction for source Decode Completion Matrix in the native source completion matrix model. -/
def sourceDecodeCompletionMatrix (a : Matrix Bool Bool (ℚ×ℚ)) : Matrix Bool Bool ℂ :=
  fun i j => rootRationalCoordinate (a i j)

/-- The estimate `matrix_entry_bound` retains the actual parameter, input-error and normalization budgets. -/
private theorem matrix_entry_bound (a : Matrix Bool Bool ℂ) (b : ℝ) (hb : 0 ≤ b)
    (h : ∀ i j,‖a i j‖ ≤ b) : ‖a‖ ≤ 2*b := by
  let J : Matrix Bool Bool ℂ := (-Complex.I) • standardSignalMatrix 0 1
  have hJ : ‖J‖ ≤ 1 := by
    dsimp [J]
    rw [norm_smul,norm_neg,Complex.norm_I,one_mul]
    exact unitary_norm_le_one (standardSignalMatrix_unitary 0 1 (by norm_num))
  have he : a=Matrix.diagonal (fun i => a i i)+Matrix.diagonal (fun i => a i (!i))*J := by
    ext i j
    cases i <;> cases j <;>
      simp [J,standardSignalMatrix,Matrix.mul_apply] <;> ring_nf <;> simp [Complex.I_sq]
  have hd : ‖Matrix.diagonal (fun i => a i i)‖ ≤ b := by
    rw [Matrix.l2_opNorm_diagonal]
    exact (pi_norm_le_iff_of_nonneg hb).mpr (fun i => h i i)
  have ho : ‖Matrix.diagonal (fun i => a i (!i))‖ ≤ b := by
    rw [Matrix.l2_opNorm_diagonal]
    exact (pi_norm_le_iff_of_nonneg hb).mpr (fun i => h i (!i))
  calc
    _ = ‖Matrix.diagonal (fun i => a i i)+Matrix.diagonal (fun i => a i (!i))*J‖ := by rw [← he]
    _ ≤ ‖Matrix.diagonal (fun i => a i i)‖+‖Matrix.diagonal (fun i => a i (!i))*J‖ := norm_add_le _ _
    _ ≤ b+b*1 := add_le_add hd ((norm_mul_le _ _).trans (mul_le_mul ho hJ (norm_nonneg _) hb))
    _ = 2*b := by ring

/-- The estimate `roundMatrix_error` retains the actual parameter, input-error and normalization budgets. -/
private theorem roundMatrix_error (a : Matrix Bool Bool (ℚ×ℚ)) (eta : ℚ) (heta : 0<eta) :
    ‖sourceDecodeCompletionMatrix (roundMatrix a eta)-sourceDecodeCompletionMatrix a‖ ≤ (eta : ℝ) := by
  have he : ∀ i j,‖(sourceDecodeCompletionMatrix (roundMatrix a eta)-sourceDecodeCompletionMatrix a) i j‖ ≤ (eta : ℝ)/4 := by
    intro i j
    have h := rootGridPoint_component_error (a i j) (eta/8) (by positivity)
    have hn := Complex.norm_le_abs_re_add_abs_im
      (rootRationalCoordinate (rootGridPoint (a i j) (eta/8))-rootRationalCoordinate (a i j))
    change ‖rootRationalCoordinate (rootGridPoint (a i j) (eta/8))-rootRationalCoordinate (a i j)‖ ≤ _
    push_cast at h
    linarith
  have hp : (0 : ℝ) ≤ (eta : ℝ)/4 := by exact_mod_cast (show (0 : ℚ) ≤ eta/4 by positivity)
  have h := matrix_entry_bound (sourceDecodeCompletionMatrix (roundMatrix a eta)-sourceDecodeCompletionMatrix a) _ hp he
  have hetaR : (0 : ℝ)<(eta : ℝ) := by exact_mod_cast heta
  linarith

end MatrixRounding

section CompletionCoefficient

open Qatlib.Concepts.MatrixAccess.MatrixBackend.RationalQsp.Data
open Qatlib.Concepts.MatrixAccess.MatrixBackend.RationalQsp.Data.SourceInput
open MeasureTheory
open scoped BigOperators Matrix.Norms.L2Operator
/-- Typeclass instance for spectral Coefficient Period Positive in the native source completion matrix model. -/
local instance spectralCoefficientPeriodPositive : Fact (0<2*Real.pi) := ⟨Real.two_pi_pos⟩

/-- Construction for source Ideal Completion Circle in the native source completion matrix model. -/
def sourceIdealCompletionCircle (cs : List ℚ) (N : ℕ) (E : ℚ) (t : AddCircle (2*Real.pi)) : Matrix Bool Bool ℂ :=
  sourceCompletionPointMatrix ((circleValue (fun j => (sourceRealArray cs N E j : ℂ)) t).re)
    (sourceIdealScaledResponse cs N E ((fourier 1 t)^2)/(fourier 1 t)^sourceDegree cs N E)

/-- Construction for source Ideal Matrix Coefficient in the native source completion matrix model. -/
def sourceIdealMatrixCoefficient (cs : List ℚ) (N : ℕ) (E : ℚ)
    (j : Fin (sourceDegree cs N E+1)) : Matrix Bool Bool ℂ :=
  fourierCoeff (sourceIdealCompletionCircle cs N E) (sourceCompletionFrequency j)

/-- Construction for source Rounded Matrix in the native source completion matrix model. -/
def sourceRoundedMatrix {m : ℕ} (cs : List ℚ) (N : ℕ) (E : ℚ)
    (f : Fin m → RootIntegerFactorData) (j : Fin (sourceDegree cs N E+1)) :
    Matrix Bool Bool (ℚ×ℚ) :=
  roundMatrix (sourceRawMatrix cs N E f j) (sourceInputEta cs N E)

/-- The finite construction in `NativeSourceCompletionMatrix` satisfies `scalar_coe` under the displayed hypotheses. -/
private theorem scalar_coe {d : ℕ} (a : Fin (d+1) → ℂ) (theta : ℝ) :
    circleValue a (theta : AddCircle (2*Real.pi))=laurentValue a theta := by
  simp only [circleValue,laurentValue,fourier_character,smul_eq_mul,mul_comm]

/-- The finite construction in `NativeSourceCompletionMatrix` satisfies `matrix_coe` under the displayed hypotheses. -/
private theorem matrix_coe {d : ℕ} (a : Fin (d+1) → Matrix Bool Bool ℂ) (theta : ℝ) :
    circleValue a (theta : AddCircle (2*Real.pi))=sourceCompletionLaurentMatrix a theta := by
  simp only [circleValue,sourceCompletionLaurentMatrix,fourier_character]

/-- The finite construction in `NativeSourceCompletionMatrix` satisfies `idealCircle_coe` under the displayed hypotheses. -/
private theorem idealCircle_coe (cs : List ℚ) (N : ℕ) (E : ℚ)
    (hparity : ∀ j : Fin (N+1),j.val%2≠N%2 → cs.getD j.val 0=0)
    (hd : 0<sourceDegree cs N E) (theta : ℝ) :
    sourceIdealCompletionCircle cs N E (theta : AddCircle (2*Real.pi))=
      sourceCompletionPointMatrix (sourceCompletionResponseA cs N E theta) (sourceIdealCompletionPhase cs N E theta) := by
  have hf : fourier (T := 2*Real.pi) 1 (theta : AddCircle (2*Real.pi))=sourceCompletionSignal theta := by
    rw [fourier_character]
    simp [character,sourceCompletionSignal]
  unfold sourceIdealCompletionCircle sourceIdealCompletionPhase
  rw [scalar_coe,sourceRealArray_value cs N E hparity hd theta,hf]
  simp

/-- The finite construction in `NativeSourceCompletionMatrix` satisfies `idealCircle_continuous` under the displayed hypotheses. -/
private theorem idealCircle_continuous (cs : List ℚ) (N : ℕ) (E : ℚ) : Continuous (sourceIdealCompletionCircle cs N E) := by
  have hf : Continuous (fun t : AddCircle (2*Real.pi) => fourier 1 t) := map_continuous _
  have hn (t : AddCircle (2*Real.pi)) : fourier (T := 2*Real.pi) 1 t≠0 := by
    have h : ‖fourier (T := 2*Real.pi) 1 t‖=1 := by rw [fourier_apply,Circle.norm_coe]
    exact norm_ne_zero_iff.mp (by rw [h]; norm_num)
  have hp : Continuous (sourceIdealProduct cs N E) :=
    continuous_multiset_prod _ (fun r _ => continuous_id.sub continuous_const)
  have hv : Continuous (fun t : AddCircle (2*Real.pi) =>
      sourceIdealScaledResponse cs N E ((fourier 1 t)^2)/(fourier 1 t)^sourceDegree cs N E) := by
    unfold sourceIdealScaledResponse
    exact ((continuous_const.mul (hp.comp (hf.pow 2))).div_const _).div
      (hf.pow _) (fun t => pow_ne_zero _ (hn t))
  have hreal : Continuous (fun t : AddCircle (2*Real.pi) =>
      (circleValue (fun j => (sourceRealArray cs N E j : ℂ)) t).re) := by
    apply Complex.continuous_re.comp
    unfold circleValue
    exact continuous_finsetSum _ (fun j _ => (map_continuous (fourier (sourceCompletionFrequency j))).smul continuous_const)
  unfold sourceIdealCompletionCircle sourceCompletionPointMatrix
  exact (((Complex.continuous_ofReal.comp (Complex.continuous_re.comp hv)).neg.smul continuous_const).add
    ((Complex.continuous_ofReal.comp hreal).smul continuous_const)).add
      ((Complex.continuous_ofReal.comp (Complex.continuous_im.comp hv)).smul continuous_const)

/-- The estimate `sourceRawMatrix_coefficient_error` retains the actual parameter, input-error and normalization budgets. -/
theorem sourceRawMatrix_coefficient_error (cs : List ℚ) (N : ℕ) (E : ℚ) (hE : 0<E)
    (htail : ∀ k,N+1 ≤ k → cs.getD k 0=0)
    (hparity : ∀ j : Fin (N+1),j.val%2≠N%2 → cs.getD j.val 0=0)
    (hd : 0<sourceDegree cs N E)
    (hnorm : ∀ x∈Set.Icc (-1 : ℝ) 1,|(nativeChebyshevPolynomialFrom 0 cs).eval x| ≤ 1)
    (m : ℕ) (content : ℤ) (f : Fin m → RootIntegerFactorData)
    (hcontent : content≠0)
    (hguard : rootIntegerFactorProduct content
      (List.ofFn (fun j => (List.ofFn (f j).coefficients,(f j).exponent)))=
        rootCanonicalCoefficients (sourceIntegerComplement cs N E))
    (haccepted : ∀ j,RootIntegerFactorGuards (f j) (sourceInputEta cs N E))
    (j : Fin (sourceDegree cs N E+1)) :
    ‖sourceDecodeCompletionMatrix (sourceRawMatrix cs N E f j)-sourceIdealMatrixCoefficient cs N E j‖ ≤
      16*(((rootDecodedReturnList f (sourceInputEta cs N E)).length : ℝ)*
        (sourceInputEta cs N E : ℝ)/(rootDecodedCertificateGap f : ℝ))+
      (sourceInputEta cs N E : ℝ) := by
  let a := fun j => sourceDecodeCompletionMatrix (sourceRawMatrix cs N E f j)
  have hg : Integrable (sourceIdealCompletionCircle cs N E) AddCircle.haarAddCircle :=
    (idealCircle_continuous cs N E).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  apply coefficient_error a (sourceIdealCompletionCircle cs N E) hg
  intro t
  obtain ⟨theta,rfl⟩ := QuotientAddGroup.mk_surjective t
  rw [matrix_coe,idealCircle_coe cs N E hparity hd theta]
  exact sourceRawMatrix_point_error cs N E hE htail hparity hd hnorm m content f hcontent hguard haccepted theta

/-- The estimate `sourceRoundedMatrix_coefficient_error` retains the actual parameter, input-error and normalization budgets. -/
theorem sourceRoundedMatrix_coefficient_error (cs : List ℚ) (N : ℕ) (E : ℚ) (hE : 0<E)
    (htail : ∀ k,N+1 ≤ k → cs.getD k 0=0)
    (hparity : ∀ j : Fin (N+1),j.val%2≠N%2 → cs.getD j.val 0=0)
    (hd : 0<sourceDegree cs N E)
    (hnorm : ∀ x∈Set.Icc (-1 : ℝ) 1,|(nativeChebyshevPolynomialFrom 0 cs).eval x| ≤ 1)
    (m : ℕ) (content : ℤ) (f : Fin m → RootIntegerFactorData)
    (hcontent : content≠0)
    (hguard : rootIntegerFactorProduct content
      (List.ofFn (fun j => (List.ofFn (f j).coefficients,(f j).exponent)))=
        rootCanonicalCoefficients (sourceIntegerComplement cs N E))
    (haccepted : ∀ j,RootIntegerFactorGuards (f j) (sourceInputEta cs N E))
    (j : Fin (sourceDegree cs N E+1)) :
    ‖sourceDecodeCompletionMatrix (sourceRoundedMatrix cs N E f j)-sourceIdealMatrixCoefficient cs N E j‖ ≤
      16*(((rootDecodedReturnList f (sourceInputEta cs N E)).length : ℝ)*
        (sourceInputEta cs N E : ℝ)/(rootDecodedCertificateGap f : ℝ))+
      2*(sourceInputEta cs N E : ℝ) := by
  have heta : 0<sourceInputEta cs N E := by unfold sourceInputEta; positivity
  have hr := roundMatrix_error (sourceRawMatrix cs N E f j) (sourceInputEta cs N E) heta
  have hc := sourceRawMatrix_coefficient_error cs N E hE htail hparity hd hnorm m content f hcontent hguard haccepted j
  have ht := norm_sub_le_norm_sub_add_norm_sub
    (sourceDecodeCompletionMatrix (sourceRoundedMatrix cs N E f j)) (sourceDecodeCompletionMatrix (sourceRawMatrix cs N E f j))
    (sourceIdealMatrixCoefficient cs N E j)
  change ‖sourceDecodeCompletionMatrix (sourceRoundedMatrix cs N E f j)-sourceDecodeCompletionMatrix (sourceRawMatrix cs N E f j)‖ ≤ _ at hr
  linarith

end CompletionCoefficient

section IdealArray

open Qatlib.Concepts.MatrixAccess.MatrixBackend.RationalQsp.Data
open Qatlib.Concepts.MatrixAccess.MatrixBackend.RationalQsp.Data.SourceInput
open Polynomial
open scoped BigOperators Matrix.Norms.L2Operator
/-- Typeclass instance for spectral Ideal Period Positive in the native source completion matrix model. -/
local instance spectralIdealPeriodPositive : Fact (0<2*Real.pi) := ⟨Real.two_pi_pos⟩

/-- Construction for source Ideal Monic Polynomial in the native source completion matrix model. -/
def sourceIdealMonicPolynomial (cs : List ℚ) (N : ℕ) (E : ℚ) : ℂ[X] :=
  ((sourceInsideRoots cs N E).map (fun r => Polynomial.X-Polynomial.C r)).prod

/-- Construction for source Ideal EArray in the native source completion matrix model. -/
def sourceIdealEArray (cs : List ℚ) (N : ℕ) (E : ℚ) (j : Fin (sourceDegree cs N E+1)) : ℂ :=
  (Real.sqrt (sourceActualH1 cs N E : ℝ) : ℂ)/(‖sourceIdealProduct cs N E 1‖ : ℂ)*
    (sourceIdealMonicPolynomial cs N E).coeff j.val

/-- Construction for source Ideal Matrix Array in the native source completion matrix model. -/
def sourceIdealMatrixArray (cs : List ℚ) (N : ℕ) (E : ℚ) (j : Fin (sourceDegree cs N E+1)) : Matrix Bool Bool ℂ :=
  rawEntry (sourceRealArray cs N E j : ℂ) (sourceIdealEArray cs N E j) (star (sourceIdealEArray cs N E j.rev))

/-- The finite construction in `NativeSourceCompletionMatrix` satisfies `idealMonic_eval` under the displayed hypotheses. -/
private theorem idealMonic_eval (cs : List ℚ) (N : ℕ) (E : ℚ) (z : ℂ) :
    (sourceIdealMonicPolynomial cs N E).eval z=sourceIdealProduct cs N E z := by
  simp [sourceIdealMonicPolynomial,sourceIdealProduct,Polynomial.eval_multiset_prod,Multiset.map_map]

/-- The finite construction in `NativeSourceCompletionMatrix` satisfies `idealE_value` under the displayed hypotheses. -/
private theorem idealE_value (cs : List ℚ) (N : ℕ) (E : ℚ)
    (hcard : (sourceInsideRoots cs N E).card=sourceDegree cs N E) (theta : ℝ) :
    laurentValue (sourceIdealEArray cs N E) theta=sourceIdealCompletionPhase cs N E theta := by
  have hdeg : (sourceIdealMonicPolynomial cs N E).natDegree<sourceDegree cs N E+1 := by
    rw [sourceIdealMonicPolynomial,Polynomial.natDegree_multiset_prod_X_sub_C_eq_card,hcard]
    omega
  have hof : Polynomial.ofFn (sourceDegree cs N E+1)
      (fun j => (sourceIdealMonicPolynomial cs N E).coeff j.val)=sourceIdealMonicPolynomial cs N E := by
    exact Polynomial.ofFn_comp_toFn_eq_id_of_natDegree_lt hdeg
  have he : laurentValue (sourceIdealEArray cs N E) theta=
      ((Real.sqrt (sourceActualH1 cs N E : ℝ) : ℂ)/(‖sourceIdealProduct cs N E 1‖ : ℂ))*
        laurentValue (fun j : Fin (sourceDegree cs N E+1) => (sourceIdealMonicPolynomial cs N E).coeff j.val) theta := by
    simp only [laurentValue,sourceIdealEArray,Finset.mul_sum,mul_assoc]
  rw [he,laurentValue_polynomial,hof,idealMonic_eval]
  unfold sourceIdealCompletionPhase sourceIdealScaledResponse
  ring

/-- The finite construction in `NativeSourceCompletionMatrix` satisfies `rawEntry_conjugate` under the displayed hypotheses. -/
private theorem rawEntry_conjugate (a : ℝ) (v : ℂ) :
    rawEntry (a : ℂ) v (star v)=sourceCompletionPointMatrix a v := by
  ext i j
  cases i <;> cases j <;> apply Complex.ext <;>
    simp [rawEntry,sourceCompletionPointMatrix,standardPhaseMatrix,standardSignalMatrix]

/-- The finite construction in `NativeSourceCompletionMatrix` satisfies `sourceIdealArray_value` under the displayed hypotheses. -/
theorem sourceIdealArray_value (cs : List ℚ) (N : ℕ) (E : ℚ) (hE : 0<E)
    (htail : ∀ k,N+1 ≤ k → cs.getD k 0=0)
    (hparity : ∀ j : Fin (N+1),j.val%2≠N%2 → cs.getD j.val 0=0)
    (hd : 0<sourceDegree cs N E)
    (hnorm : ∀ x∈Set.Icc (-1 : ℝ) 1,|(nativeChebyshevPolynomialFrom 0 cs).eval x| ≤ 1)
    (theta : ℝ) :
    sourceCompletionLaurentMatrix (sourceIdealMatrixArray cs N E) theta=
      sourceCompletionPointMatrix (sourceCompletionResponseA cs N E theta) (sourceIdealCompletionPhase cs N E theta) := by
  have hcard : (sourceInsideRoots cs N E).card=sourceDegree cs N E :=
    sourceIntegerComplement_inside_count cs N E hE htail hparity hd hnorm
  unfold sourceIdealMatrixArray
  rw [rawEntry_value,sourceRealArray_value cs N E hparity hd theta,
    idealE_value cs N E hcard theta,
    laurentValue_reflect (sourceIdealEArray cs N E),idealE_value cs N E hcard theta,rawEntry_conjugate]

/-- The finite construction in `NativeSourceCompletionMatrix` satisfies `sourceIdealArray_circle` under the displayed hypotheses. -/
private theorem sourceIdealArray_circle (cs : List ℚ) (N : ℕ) (E : ℚ) (hE : 0<E)
    (htail : ∀ k,N+1 ≤ k → cs.getD k 0=0)
    (hparity : ∀ j : Fin (N+1),j.val%2≠N%2 → cs.getD j.val 0=0)
    (hd : 0<sourceDegree cs N E)
    (hnorm : ∀ x∈Set.Icc (-1 : ℝ) 1,|(nativeChebyshevPolynomialFrom 0 cs).eval x| ≤ 1)
    (t : AddCircle (2*Real.pi)) : circleValue (sourceIdealMatrixArray cs N E) t=sourceIdealCompletionCircle cs N E t := by
  obtain ⟨theta,rfl⟩ := QuotientAddGroup.mk_surjective t
  have hf : fourier (T := 2*Real.pi) 1 (theta : AddCircle (2*Real.pi))=sourceCompletionSignal theta := by
    rw [fourier_character]
    simp [character,sourceCompletionSignal]
  have hm : circleValue (sourceIdealMatrixArray cs N E) (theta : AddCircle (2*Real.pi))=
      sourceCompletionLaurentMatrix (sourceIdealMatrixArray cs N E) theta := by
    simp only [circleValue,sourceCompletionLaurentMatrix,fourier_character]
  have ha : circleValue (fun j => (sourceRealArray cs N E j : ℂ)) (theta : AddCircle (2*Real.pi))=
      (sourceCompletionResponseA cs N E theta : ℂ) := by
    simp only [circleValue,fourier_character,smul_eq_mul,mul_comm]
    exact sourceRealArray_value cs N E hparity hd theta
  rw [hm,sourceIdealArray_value cs N E hE htail hparity hd hnorm theta]
  unfold sourceIdealCompletionCircle sourceIdealCompletionPhase
  rw [ha,hf]
  simp

/-- The finite construction in `NativeSourceCompletionMatrix` satisfies `sourceIdealArray_coefficient` under the displayed hypotheses. -/
private theorem sourceIdealArray_coefficient (cs : List ℚ) (N : ℕ) (E : ℚ) (hE : 0<E)
    (htail : ∀ k,N+1 ≤ k → cs.getD k 0=0)
    (hparity : ∀ j : Fin (N+1),j.val%2≠N%2 → cs.getD j.val 0=0)
    (hd : 0<sourceDegree cs N E)
    (hnorm : ∀ x∈Set.Icc (-1 : ℝ) 1,|(nativeChebyshevPolynomialFrom 0 cs).eval x| ≤ 1)
    (j : Fin (sourceDegree cs N E+1)) :
    sourceIdealMatrixCoefficient cs N E j=sourceIdealMatrixArray cs N E j := by
  have h : sourceIdealCompletionCircle cs N E=circleValue (sourceIdealMatrixArray cs N E) := by
    funext t
    exact (sourceIdealArray_circle cs N E hE htail hparity hd hnorm t).symm
  rw [sourceIdealMatrixCoefficient,h,circleValue_coefficient]

/-- The estimate `sourceRoundedMatrix_error_to_ideal_array` retains the actual parameter, input-error and normalization budgets. -/
theorem sourceRoundedMatrix_error_to_ideal_array (cs : List ℚ) (N : ℕ) (E : ℚ) (hE : 0<E)
    (htail : ∀ k,N+1 ≤ k → cs.getD k 0=0)
    (hparity : ∀ j : Fin (N+1),j.val%2≠N%2 → cs.getD j.val 0=0)
    (hd : 0<sourceDegree cs N E)
    (hnorm : ∀ x∈Set.Icc (-1 : ℝ) 1,|(nativeChebyshevPolynomialFrom 0 cs).eval x| ≤ 1)
    (m : ℕ) (content : ℤ) (f : Fin m → RootIntegerFactorData)
    (hcontent : content≠0)
    (hguard : rootIntegerFactorProduct content
      (List.ofFn (fun j => (List.ofFn (f j).coefficients,(f j).exponent)))=
        rootCanonicalCoefficients (sourceIntegerComplement cs N E))
    (haccepted : ∀ j,RootIntegerFactorGuards (f j) (sourceInputEta cs N E))
    (j : Fin (sourceDegree cs N E+1)) :
    ‖sourceDecodeCompletionMatrix (sourceRoundedMatrix cs N E f j)-sourceIdealMatrixArray cs N E j‖ ≤
      16*(((rootDecodedReturnList f (sourceInputEta cs N E)).length : ℝ)*
        (sourceInputEta cs N E : ℝ)/(rootDecodedCertificateGap f : ℝ))+
      2*(sourceInputEta cs N E : ℝ) := by
  rw [← sourceIdealArray_coefficient cs N E hE htail hparity hd hnorm j]
  exact sourceRoundedMatrix_coefficient_error cs N E hE htail hparity hd hnorm m content f hcontent hguard haccepted j

/-- The actual finite word or frame satisfies `sourceIdealArray_unitary` with all displayed legality, input and workspace hypotheses. -/
theorem sourceIdealArray_unitary (cs : List ℚ) (N : ℕ) (E : ℚ) (hE : 0<E)
    (htail : ∀ k,N+1 ≤ k → cs.getD k 0=0)
    (hparity : ∀ j : Fin (N+1),j.val%2≠N%2 → cs.getD j.val 0=0)
    (hd : 0<sourceDegree cs N E)
    (hnorm : ∀ x∈Set.Icc (-1 : ℝ) 1,|(nativeChebyshevPolynomialFrom 0 cs).eval x| ≤ 1)
    (theta : ℝ) :
    sourceCompletionLaurentMatrix (sourceIdealMatrixArray cs N E) theta∈
      Matrix.unitaryGroup Bool ℂ := by
  rw [sourceIdealArray_value cs N E hE htail hparity hd hnorm theta]
  exact sourceIdealPoint_unitary cs N E hE htail hparity hd hnorm theta

end IdealArray

section ContinuationInterfaces
open MeasureTheory
open scoped Matrix.Norms.L2Operator
local instance : Fact (0<2*Real.pi) := ⟨Real.two_pi_pos⟩

/-- Construction for source Round Completion Matrix in the native source completion matrix model. -/
def sourceRoundCompletionMatrix (A : Matrix Bool Bool (ℚ×ℚ)) (eta : ℚ) : Matrix Bool Bool (ℚ×ℚ) :=
  fun i j => rootGridPoint (A i j) (eta/8)

/-- The estimate `sourceRoundCompletionMatrix_error` retains the actual parameter, input-error and normalization budgets. -/
theorem sourceRoundCompletionMatrix_error (A : Matrix Bool Bool (ℚ×ℚ)) (eta : ℚ) (heta : 0<eta) :
    ‖sourceDecodeCompletionMatrix (sourceRoundCompletionMatrix A eta)-sourceDecodeCompletionMatrix A‖ ≤ (eta : ℝ) :=
  roundMatrix_error A eta heta

/-- Construction for source Completion Circle Value in the native source completion matrix model. -/
def sourceCompletionCircleValue {d : ℕ} (A : Fin (d+1) → Matrix Bool Bool ℂ)
    (t : AddCircle (2*Real.pi)) : Matrix Bool Bool ℂ :=
  ∑ j, fourier (sourceCompletionFrequency j) t • A j

/-- The finite construction in `NativeSourceCompletionMatrix` satisfies `sourceCompletionCircleValue_coefficient` under the displayed hypotheses. -/
theorem sourceCompletionCircleValue_coefficient {d : ℕ} (A : Fin (d+1) → Matrix Bool Bool ℂ)
    (j : Fin (d+1)) : fourierCoeff (sourceCompletionCircleValue A) (sourceCompletionFrequency j)=A j :=
  circleValue_coefficient A j

/-- The finite construction in `NativeSourceCompletionMatrix` satisfies `sourceCompletionCircleValue_real` under the displayed hypotheses. -/
theorem sourceCompletionCircleValue_real {d : ℕ} (A : Fin (d+1) → Matrix Bool Bool ℂ) (theta : ℝ) :
    sourceCompletionCircleValue A (theta : AddCircle (2*Real.pi))=sourceCompletionLaurentMatrix A theta := by
  simp only [sourceCompletionCircleValue,sourceCompletionLaurentMatrix,fourier_character]

end ContinuationInterfaces

/-- The finite construction in `NativeSourceCompletionMatrix` satisfies `sourceCompletionFourier_real` under the displayed hypotheses. -/
theorem sourceCompletionFourier_real (k : ℤ) (theta : ℝ) :
    fourier (T := 2*Real.pi) k (theta : AddCircle (2*Real.pi))=
      Complex.exp ((k : ℂ)*((theta : ℂ)*Complex.I)) :=
  fourier_character k theta

end Qatlib.Concepts.MatrixAccess.MatrixBackend.RationalQsp.Data.SourceInput
