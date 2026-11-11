/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.MatrixAccess.MatrixBackend.RationalQsp.NativeSourceGramTrace
import Mathlib.Analysis.Matrix.PosDef
import Qatlib.Concepts.MatrixAccess.MatrixBackend.RationalQsp.NativeSourceInitialPivot
import Qatlib.Concepts.MatrixAccess.MatrixBackend.RationalQsp.NativeSourceCompletionMatrix
import Qatlib.Concepts.MatrixAccess.MatrixBackend.PolynomialArrays.Public
import Qatlib.Concepts.MatrixAccess.MatrixBackend.PolynomialArrays.Verifier
import Qatlib.Concepts.MatrixAccess.MatrixBackend.NativeWords.RationalCircle
import Qatlib.Concepts.MatrixAccess.MatrixBackend.NativeWords.HouseholderRotationTable
import Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords.NativeHouseholder
import Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords.NativePhasePrecision

set_option backward.isDefEq.respectTransparency false

/-! Same original-input Gaussian Gram normalization and first deflation: GramNormalization.
This does not certify subsequent ideal preservation, the whole loop, interpreter or fees. -/
set_option autoImplicit false
set_option maxHeartbeats 1000000
noncomputable section
namespace Qatlib.Concepts.MatrixAccess.MatrixBackend.RationalQsp.Data.SourceInput
open Qatlib.Concepts.MatrixAccess.MatrixBackend.PolynomialArrays Qatlib.Concepts.MatrixAccess.MatrixBackend.PolynomialArrays.SourceInput Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords.Prep Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords.Data Qatlib.Concepts.MatrixAccess.MatrixBackend.NativeWords


section GramNorm

open Qatlib.Concepts.MatrixAccess.MatrixBackend.RationalQsp.Data
open Qatlib.Concepts.MatrixAccess.MatrixBackend.RationalQsp.Data.SourceInput
open Qatlib.Concepts.BlockEncoding.Encoding
open scoped BigOperators Matrix.Norms.L2Operator ComplexOrder

/-- The finite construction in `NativeSourceGramNormalization` satisfies `positive_norm_le_trace` under the displayed hypotheses. -/
private theorem positive_norm_le_trace (A : Matrix Bool Bool ℂ) (hA : A.PosSemidef) :
    ‖A‖ ≤ A.trace.re := by
  let U := hA.isHermitian.eigenvectorUnitary
  let D := Matrix.diagonal (fun i : Bool => (hA.isHermitian.eigenvalues i : ℂ))
  have htr : A.trace.re=∑ i : Bool,hA.isHermitian.eigenvalues i := by
    have h := congrArg Complex.re hA.isHermitian.trace_eq_sum_eigenvalues
    simpa using h
  have htr0 : 0 ≤ A.trace.re := by rw [htr]; exact Finset.sum_nonneg (fun i _ => hA.eigenvalues_nonneg i)
  have hd : ‖D‖ ≤ A.trace.re := by
    rw [Matrix.l2_opNorm_diagonal]
    apply (pi_norm_le_iff_of_nonneg htr0).mpr
    intro i
    rw [Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (hA.eigenvalues_nonneg i),htr]
    exact Finset.single_le_sum (fun k _ => hA.eigenvalues_nonneg k) (Finset.mem_univ i)
  have hU : ‖(U : Matrix Bool Bool ℂ)‖ ≤ 1 := unitary_norm_le_one U.property
  have he : A=(U : Matrix Bool Bool ℂ)*D*star (U : Matrix Bool Bool ℂ) := by
    simpa [U,D,Unitary.conjStarAlgAut_apply, Function.comp_def] using hA.isHermitian.spectral_theorem
  calc
    _ = ‖(U : Matrix Bool Bool ℂ)*D*star (U : Matrix Bool Bool ℂ)‖ := congrArg norm he
    _ ≤ (‖(U : Matrix Bool Bool ℂ)‖*‖D‖)*‖star (U : Matrix Bool Bool ℂ)‖ :=
      (norm_mul_le _ _).trans (mul_le_mul_of_nonneg_right (norm_mul_le _ _) (norm_nonneg _))
    _ ≤ (1*‖D‖)*1 := by
      rw [norm_star]
      exact mul_le_mul (mul_le_mul_of_nonneg_right hU (norm_nonneg _)) hU (norm_nonneg _) (by positivity)
    _ ≤ A.trace.re := by simpa using hd

/-- The finite construction in `NativeSourceGramNormalization` satisfies `sourceGaussianGram_decode` under the displayed hypotheses. -/
private theorem sourceGaussianGram_decode (A : Matrix Bool Bool (ℚ×ℚ)) :
    sourceDecodeCompletionMatrix (sourceGaussianGram A)=
      (sourceDecodeCompletionMatrix A).conjTranspose*sourceDecodeCompletionMatrix A := by
  ext i j
  cases i <;> cases j <;> apply Complex.ext <;>
    simp [sourceDecodeCompletionMatrix,sourceGaussianGram,sourceGaussianMatrixMul,sourceGaussianAdjoint,gaussianRatMul,rootRationalCoordinate,
      Matrix.mul_apply,Matrix.conjTranspose_apply] <;> ring

/-- The finite construction in `NativeSourceGramNormalization` satisfies `sourceGaussianGramTrace_re` under the displayed hypotheses. -/
private theorem sourceGaussianGramTrace_re (A : Matrix Bool Bool (ℚ×ℚ)) :
    ((sourceGaussianGramTrace A).1 : ℝ)=(sourceDecodeCompletionMatrix (sourceGaussianGram A)).trace.re := by
  simp [sourceGaussianGramTrace,sourceDecodeCompletionMatrix,Matrix.trace,rootRationalCoordinate]
  ring

/-- Construction for source Gram Normalize Unrounded in the native source gram normalization model. -/
def sourceGramNormalizeUnrounded (A : Matrix Bool Bool (ℚ×ℚ)) : Matrix Bool Bool (ℚ×ℚ) :=
  fun i j => ((1/(sourceGaussianGramTrace A).1)*(sourceGaussianGram A i j).1,
    (1/(sourceGaussianGramTrace A).1)*(sourceGaussianGram A i j).2)

/-- The finite construction in `NativeSourceGramNormalization` satisfies `sourceGramNormalizeUnrounded_decode` under the displayed hypotheses. -/
private theorem sourceGramNormalizeUnrounded_decode (A : Matrix Bool Bool (ℚ×ℚ)) :
    sourceDecodeCompletionMatrix (sourceGramNormalizeUnrounded A)=
      ((1/(sourceGaussianGramTrace A).1 : ℚ) : ℂ) • sourceDecodeCompletionMatrix (sourceGaussianGram A) := by
  have hdecode (s : ℚ) (v : ℚ×ℚ) : rootRationalCoordinate (s*v.1,s*v.2)=
      (s : ℂ)*rootRationalCoordinate v := by
    apply Complex.ext <;> simp [rootRationalCoordinate]
  ext i j
  exact hdecode _ _


/-- The finite construction in `NativeSourceGramNormalization` satisfies `sourceGramNormalizeUnrounded_norm` under the displayed hypotheses. -/
theorem sourceGramNormalizeUnrounded_norm (A : Matrix Bool Bool (ℚ×ℚ))
    (hn : ∃ i j,A i j≠(0,0)) : ‖sourceDecodeCompletionMatrix (sourceGramNormalizeUnrounded A)‖ ≤ 1 := by
  have hg := sourceGaussianGramTrace_guard A hn
  have ht : (0 : ℝ)<((sourceGaussianGramTrace A).1 : ℝ) := by exact_mod_cast hg.2
  have hb := positive_norm_le_trace _ (Matrix.posSemidef_conjTranspose_mul_self (sourceDecodeCompletionMatrix A))
  rw [← sourceGaussianGram_decode,← sourceGaussianGramTrace_re] at hb
  rw [sourceGramNormalizeUnrounded_decode,norm_smul,← Complex.ofReal_ratCast,Complex.norm_real,Real.norm_eq_abs]
  have hs : (0 : ℝ) ≤ ((1/(sourceGaussianGramTrace A).1 : ℚ) : ℝ) := by
    exact_mod_cast (one_div_pos.mpr hg.2).le
  rw [abs_of_nonneg hs,Rat.cast_div,Rat.cast_one]
  exact (mul_le_mul_of_nonneg_left hb (by positivity)).trans_eq (by field_simp)

end GramNorm

section GramStability

open Matrix
open scoped Matrix.Norms.L2Operator ComplexOrder

/-- Construction for source Complex Gram Normalize in the native source gram normalization model. -/
def sourceComplexGramNormalize (A : Matrix Bool Bool ℂ) : Matrix Bool Bool ℂ :=
  ((1/(A.conjTranspose*A).trace.re : ℝ) : ℂ) • (A.conjTranspose*A)

/-- The finite construction in `NativeSourceGramNormalization` satisfies `sourceCompletionMatrix_entry_norm` under the displayed hypotheses. -/
theorem sourceCompletionMatrix_entry_norm (A : Matrix Bool Bool ℂ) (i j : Bool) : ‖A i j‖ ≤ ‖A‖ := by
  let x : EuclideanSpace ℂ Bool := PiLp.single 2 j 1
  let y := (EuclideanSpace.equiv Bool ℂ).symm (A *ᵥ x)
  calc
    _ = ‖y i‖ := by simp [y,x]
    _ ≤ ‖y‖ := PiLp.norm_apply_le y i
    _ ≤ ‖A‖*‖x‖ := A.l2_opNorm_mulVec x
    _ = ‖A‖ := by simp [x]

/-- The estimate `trace_re_bound` retains the actual parameter, input-error and normalization budgets. -/
private theorem trace_re_bound (A : Matrix Bool Bool ℂ) : |A.trace.re| ≤ 2*‖A‖ := by
  have h0 := (Complex.abs_re_le_norm (A false false)).trans (sourceCompletionMatrix_entry_norm A false false)
  have h1 := (Complex.abs_re_le_norm (A true true)).trans (sourceCompletionMatrix_entry_norm A true true)
  have ht := abs_add_le (A true true).re (A false false).re
  have he : A.trace.re=(A true true).re+(A false false).re := by simp [Matrix.trace]
  rw [he]
  linarith

/-- The estimate `gram_difference_bound` retains the actual parameter, input-error and normalization budgets. -/
private theorem gram_difference_bound (A B : Matrix Bool Bool ℂ) (delta : ℝ) (he : ‖A-B‖ ≤ delta) :
    ‖A.conjTranspose*A-B.conjTranspose*B‖ ≤ delta*(2*‖B‖+delta) := by
  have hd : 0 ≤ delta := (norm_nonneg _).trans he
  have hA : ‖A‖ ≤ ‖B‖+delta := by
    have h := norm_le_norm_sub_add A B
    linarith
  have hid : A.conjTranspose*A-B.conjTranspose*B=
      (A-B).conjTranspose*A+B.conjTranspose*(A-B) := by
    rw [Matrix.conjTranspose_sub,sub_mul,mul_sub]
    abel
  rw [hid]
  calc
    _ ≤ ‖(A-B).conjTranspose*A‖+‖B.conjTranspose*(A-B)‖ := norm_add_le _ _
    _ ≤ ‖(A-B).conjTranspose‖*‖A‖+‖B.conjTranspose‖*‖A-B‖ := add_le_add (norm_mul_le _ _) (norm_mul_le _ _)
    _ = ‖A-B‖*‖A‖+‖B‖*‖A-B‖ := by rw [Matrix.l2_opNorm_conjTranspose,Matrix.l2_opNorm_conjTranspose]
    _ ≤ delta*(‖B‖+delta)+‖B‖*delta := add_le_add
      (mul_le_mul he hA (norm_nonneg _) hd) (mul_le_mul_of_nonneg_left he (norm_nonneg _))
    _ = _ := by ring

/-- The estimate `normalization_ratio_bound` retains the actual parameter, input-error and normalization budgets. -/
private theorem normalization_ratio_bound (c delta T : ℝ) (hc : 0<c) (hd : 0 ≤ delta)
    (hcap : delta ≤ c/4) (hlower : (c-delta)^2 ≤ T) :
    3*delta*(2*c+delta)/T ≤ 12*delta/c := by
  have hsmall : 0<c-delta := by linarith
  have hT : 0<T := lt_of_lt_of_le (sq_pos_of_pos hsmall) hlower
  apply (div_le_div_iff₀ hT hc).mpr
  have hprod : 0 ≤ (c-4*delta)*(2*c-delta)*delta :=
    mul_nonneg (mul_nonneg (by linarith) (by linarith)) hd
  have hm := mul_le_mul_of_nonneg_left hlower (show 0 ≤ 12*delta by positivity)
  nlinarith


/-- The finite construction in `NativeSourceGramNormalization` satisfies `complexGramNormalize_stability` under the displayed hypotheses. -/
private theorem complexGramNormalize_stability (A B : Matrix Bool Bool ℂ) (delta : ℝ)
    (hc : 0<‖B‖) (he : ‖A-B‖ ≤ delta) (hcap : delta ≤ ‖B‖/4)
    (hrank : (B.conjTranspose*B).trace.re=‖B‖^2) :
    0<(A.conjTranspose*A).trace.re ∧
      ‖sourceComplexGramNormalize A-sourceComplexGramNormalize B‖ ≤ 12*delta/‖B‖ := by
  let c := ‖B‖
  let T := (A.conjTranspose*A).trace.re
  let D := delta*(2*c+delta)
  have hc0 : c≠0 := hc.ne'
  have hd : 0 ≤ delta := (norm_nonneg _).trans he
  have hsmall : 0<c-delta := by dsimp [c]; linarith
  have hAn : c-delta ≤ ‖A‖ := by
    have h := norm_le_norm_sub_add B A
    rw [norm_sub_rev] at h
    dsimp [c]
    linarith
  have hnormsq : ‖A‖^2 ≤ T := by
    have h := positive_norm_le_trace _ (Matrix.posSemidef_conjTranspose_mul_self A)
    rw [Matrix.l2_opNorm_conjTranspose_mul_self] at h
    dsimp [T]
    nlinarith
  have hTlower : (c-delta)^2 ≤ T := by nlinarith [norm_nonneg A]
  have hT : 0<T := lt_of_lt_of_le (sq_pos_of_pos hsmall) hTlower
  refine ⟨hT,?_⟩
  have hdiff : ‖A.conjTranspose*A-B.conjTranspose*B‖ ≤ D := gram_difference_bound A B delta he
  have htr : |T-c^2| ≤ 2*D := by
    have h := trace_re_bound (A.conjTranspose*A-B.conjTranspose*B)
    have hid : (A.conjTranspose*A-B.conjTranspose*B).trace.re=T-c^2 := by
      rw [Matrix.trace_sub,Complex.sub_re,hrank]
    rw [hid] at h
    exact h.trans (mul_le_mul_of_nonneg_left hdiff (by norm_num))
  have hrecip : |1/T-1/c^2|=|T-c^2|/(T*c^2) := by
    have hid : 1/T-1/c^2=-(T-c^2)/(T*c^2) := by
      field_simp [hT.ne',hc0]
      ring
    rw [hid,abs_div,abs_neg,abs_of_pos (mul_pos hT (sq_pos_of_pos hc))]
  have hid : sourceComplexGramNormalize A-sourceComplexGramNormalize B=
      ((1/T : ℝ) : ℂ) • (A.conjTranspose*A-B.conjTranspose*B)+
        ((1/T-1/c^2 : ℝ) : ℂ) • (B.conjTranspose*B) := by
    unfold sourceComplexGramNormalize
    rw [hrank]
    change ((1/T : ℝ) : ℂ) • (A.conjTranspose*A)-((1/c^2 : ℝ) : ℂ) • (B.conjTranspose*B)=_
    ext i j
    simp only [Matrix.sub_apply,Matrix.add_apply,Matrix.smul_apply,smul_eq_mul,Complex.ofReal_sub]
    ring
  rw [hid]
  calc
    _ ≤ ‖((1/T : ℝ) : ℂ) • (A.conjTranspose*A-B.conjTranspose*B)‖+
        ‖((1/T-1/c^2 : ℝ) : ℂ) • (B.conjTranspose*B)‖ := norm_add_le _ _
    _ = (1/T)*‖A.conjTranspose*A-B.conjTranspose*B‖+|1/T-1/c^2| *c^2 := by
      rw [norm_smul,norm_smul,Complex.norm_real,Real.norm_eq_abs,abs_of_pos (one_div_pos.mpr hT),
        Complex.norm_real,Real.norm_eq_abs,Matrix.l2_opNorm_conjTranspose_mul_self]
      dsimp [c]
      ring
    _ ≤ (1/T)*D+(2*D)/(T*c^2)*c^2 := by
      rw [hrecip]
      exact add_le_add (mul_le_mul_of_nonneg_left hdiff (by positivity))
        (mul_le_mul_of_nonneg_right
          (div_le_div_of_nonneg_right htr (mul_pos hT (sq_pos_of_pos hc)).le) (sq_nonneg c))
    _ = 3*D/T := by
      field_simp [hT.ne',hc0]
      ring
    _ ≤ 12*delta/c := by
      simpa only [D,mul_assoc] using normalization_ratio_bound c delta T hc hd hcap hTlower

end GramStability

section RankOneTrace

open Qatlib.Concepts.BlockEncoding.Encoding
open scoped BigOperators Matrix.Norms.L2Operator ComplexOrder

/-- The finite construction in `NativeSourceGramNormalization` satisfies `sourceGram_trace_eq_norm_sq` under the displayed hypotheses. -/
theorem sourceGram_trace_eq_norm_sq (C : Matrix Bool Bool ℂ) (hdet : C.det=0) :
    (C.conjTranspose*C).trace.re=‖C‖^2 := by
  let H := C.conjTranspose*C
  have hH : H.PosSemidef := Matrix.posSemidef_conjTranspose_mul_self C
  have hdetH : H.det=0 := by
    dsimp [H]
    rw [Matrix.det_mul,Matrix.det_conjTranspose,hdet]
    simp
  let U := hH.isHermitian.eigenvectorUnitary
  let D := Matrix.diagonal (fun i : Bool => (hH.isHermitian.eigenvalues i : ℂ))
  have hprod : hH.isHermitian.eigenvalues true*hH.isHermitian.eigenvalues false=0 := by
    have he := hH.isHermitian.det_eq_prod_eigenvalues
    rw [hdetH] at he
    simpa using congrArg Complex.re he.symm
  have htr : H.trace.re=∑ i : Bool,hH.isHermitian.eigenvalues i := by
    simpa using congrArg Complex.re hH.isHermitian.trace_eq_sum_eigenvalues
  have hU : ‖(U : Matrix Bool Bool ℂ)‖ ≤ 1 := unitary_norm_le_one U.property
  have hD : ‖D‖ ≤ ‖H‖ := by
    have he : D=star (U : Matrix Bool Bool ℂ)*H*(U : Matrix Bool Bool ℂ) := by
      simpa [U,D,Unitary.conjStarAlgAut_apply, Function.comp_def] using hH.isHermitian.conjStarAlgAut_star_eigenvectorUnitary.symm
    calc
      _ = ‖star (U : Matrix Bool Bool ℂ)*H*(U : Matrix Bool Bool ℂ)‖ := congrArg norm he
      _ ≤ (‖star (U : Matrix Bool Bool ℂ)‖*‖H‖)*‖(U : Matrix Bool Bool ℂ)‖ :=
        (norm_mul_le _ _).trans (mul_le_mul_of_nonneg_right (norm_mul_le _ _) (norm_nonneg _))
      _ ≤ (1*‖H‖)*1 := by
        rw [norm_star]
        exact mul_le_mul (mul_le_mul_of_nonneg_right hU (norm_nonneg _)) hU (norm_nonneg _) (by positivity)
      _ = ‖H‖ := by ring
  have heig (i : Bool) : hH.isHermitian.eigenvalues i ≤ ‖D‖ := by
    dsimp [D]
    rw [Matrix.l2_opNorm_diagonal]
    have h := norm_le_pi_norm (fun j : Bool => (hH.isHermitian.eigenvalues j : ℂ)) i
    simpa only [Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (hH.eigenvalues_nonneg i)] using h
  have hback : H.trace.re ≤ ‖H‖ := by
    rcases mul_eq_zero.mp hprod with hzero|hzero
    · rw [htr]
      simpa [hzero] using (heig false).trans hD
    · rw [htr]
      simpa [hzero] using (heig true).trans hD
  have hn : ‖H‖=H.trace.re := le_antisymm (positive_norm_le_trace H hH) hback
  calc
    _ = ‖H‖ := hn.symm
    _ = ‖C‖*‖C‖ := Matrix.l2_opNorm_conjTranspose_mul_self C
    _ = ‖C‖^2 := by ring

end RankOneTrace

section StoredNormalize

open Qatlib.Concepts.MatrixAccess.MatrixBackend.RationalQsp.Data
open Qatlib.Concepts.MatrixAccess.MatrixBackend.RationalQsp.Data.SourceInput
open scoped Matrix.Norms.L2Operator

/-- Construction for source Gram Normalize in the native source gram normalization model. -/
def sourceGramNormalize (A : Matrix Bool Bool (ℚ×ℚ)) (eta : ℚ) : Matrix Bool Bool (ℚ×ℚ) :=
  sourceRoundCompletionMatrix (sourceGramNormalizeUnrounded A) eta

/-- The finite construction in `NativeSourceGramNormalization` satisfies `sourceGramNormalize_rounding` under the displayed hypotheses. -/
theorem sourceGramNormalize_rounding (A : Matrix Bool Bool (ℚ×ℚ)) (eta : ℚ) (heta : 0<eta) :
    ‖sourceDecodeCompletionMatrix (sourceGramNormalize A eta)-
      sourceDecodeCompletionMatrix (sourceGramNormalizeUnrounded A)‖ ≤ (eta : ℝ) := by
  exact sourceRoundCompletionMatrix_error (sourceGramNormalizeUnrounded A) eta heta

/-- The finite construction in `NativeSourceGramNormalization` satisfies `sourceGramNormalize_norm` under the displayed hypotheses. -/
theorem sourceGramNormalize_norm (A : Matrix Bool Bool (ℚ×ℚ)) (eta : ℚ) (heta : 0<eta)
    (hn : ∃ i j,A i j≠(0,0)) : ‖sourceDecodeCompletionMatrix (sourceGramNormalize A eta)‖ ≤ 1+(eta : ℝ) := by
  have hr := sourceGramNormalize_rounding A eta heta
  have hu := sourceGramNormalizeUnrounded_norm A hn
  have ht := norm_le_norm_sub_add (sourceDecodeCompletionMatrix (sourceGramNormalize A eta))
    (sourceDecodeCompletionMatrix (sourceGramNormalizeUnrounded A))
  linarith

/-- The finite construction in `NativeSourceGramNormalization` satisfies `source_initial_normalize` under the displayed hypotheses. -/
theorem source_initial_normalize {m : ℕ} (cs : List ℚ) (N : ℕ) (E : ℚ)
    (hE : 0<E) (hd : 0<sourceDegree cs N E) (f : Fin m → RootIntegerFactorData)
    (j : Fin (sourceDegree cs N E+1)) (hj : j.val=0 ∨ j.val=sourceDegree cs N E) :
    (sourceGaussianGramTrace (sourceRoundedMatrix cs N E f j)).2=0 ∧
      0<(sourceGaussianGramTrace (sourceRoundedMatrix cs N E f j)).1 ∧
      ‖sourceDecodeCompletionMatrix (sourceGramNormalize (sourceRoundedMatrix cs N E f j)
        (sourceInputEta cs N E))‖ ≤ 1+(sourceInputEta cs N E : ℝ) := by
  have hg := source_initial_extreme_gram_guard cs N E hE hd f j hj
  refine ⟨hg.1,hg.2,?_⟩
  apply sourceGramNormalize_norm _ _ (by unfold sourceInputEta; positivity)
  exact source_initial_extreme_nonzero cs N E hE hd f j hj

end StoredNormalize

section NormalizeStability

open Qatlib.Concepts.MatrixAccess.MatrixBackend.RationalQsp.Data
open Qatlib.Concepts.MatrixAccess.MatrixBackend.RationalQsp.Data.SourceInput
open scoped Matrix.Norms.L2Operator

/-- The finite construction in `NativeSourceGramNormalization` satisfies `sourceGramNormalizeUnrounded_eq_complex` under the displayed hypotheses. -/
private theorem sourceGramNormalizeUnrounded_eq_complex (A : Matrix Bool Bool (ℚ×ℚ)) :
    sourceDecodeCompletionMatrix (sourceGramNormalizeUnrounded A)=sourceComplexGramNormalize (sourceDecodeCompletionMatrix A) := by
  rw [sourceGramNormalizeUnrounded_decode]
  unfold sourceComplexGramNormalize
  rw [← sourceGaussianGram_decode,← sourceGaussianGramTrace_re]
  rw [← Complex.ofReal_ratCast,Rat.cast_div,Rat.cast_one]

/-- The finite construction in `NativeSourceGramNormalization` satisfies `sourceGramNormalize_stability` under the displayed hypotheses. -/
theorem sourceGramNormalize_stability (A : Matrix Bool Bool (ℚ×ℚ)) (B : Matrix Bool Bool ℂ)
    (delta : ℝ) (eta : ℚ) (heta : 0<eta) (hc : 0<‖B‖)
    (he : ‖sourceDecodeCompletionMatrix A-B‖ ≤ delta) (hcap : delta ≤ ‖B‖/4)
    (hrank : (B.conjTranspose*B).trace.re=‖B‖^2) :
    (sourceGaussianGramTrace A).2=0 ∧ 0<(sourceGaussianGramTrace A).1 ∧
      ‖sourceDecodeCompletionMatrix (sourceGramNormalize A eta)‖ ≤ 1+(eta : ℝ) ∧
      ‖sourceDecodeCompletionMatrix (sourceGramNormalize A eta)-sourceComplexGramNormalize B‖ ≤
        12*delta/‖B‖+(eta : ℝ) := by
  have h := complexGramNormalize_stability (sourceDecodeCompletionMatrix A) B delta hc he hcap hrank
  have ht : ((sourceGaussianGramTrace A).1 : ℝ)=(
      (sourceDecodeCompletionMatrix A).conjTranspose*sourceDecodeCompletionMatrix A).trace.re := by
    rw [← sourceGaussianGram_decode]
    exact sourceGaussianGramTrace_re A
  have hpos : 0<(sourceGaussianGramTrace A).1 := by
    have hp : (0 : ℝ)<((sourceGaussianGramTrace A).1 : ℝ) := ht.symm ▸ h.1
    exact_mod_cast hp
  have hn : ∃ i j,A i j≠(0,0) := by
    by_contra hn
    push Not at hn
    have hz : (sourceGaussianGramTrace A).1=0 := by
      rw [(sourceGaussianGramTrace_identity A).1]
      simp [hn,sourceGaussianNormSq]
    linarith
  refine ⟨(sourceGaussianGramTrace_identity A).2,hpos,sourceGramNormalize_norm A eta heta hn,?_⟩
  have hr := sourceGramNormalize_rounding A eta heta
  rw [sourceGramNormalizeUnrounded_eq_complex] at hr
  have ht := norm_sub_le_norm_sub_add_norm_sub (sourceDecodeCompletionMatrix (sourceGramNormalize A eta))
    (sourceComplexGramNormalize (sourceDecodeCompletionMatrix A)) (sourceComplexGramNormalize B)
  linarith [h.2]

end NormalizeStability

section DeflationContinuation
open scoped Matrix.Norms.L2Operator ComplexOrder

/-- The finite construction in `NativeSourceGramNormalization` satisfies `sourceComplexGram_norm_le_trace` under the displayed hypotheses. -/
theorem sourceComplexGram_norm_le_trace (C : Matrix Bool Bool ℂ) :
    ‖C.conjTranspose*C‖≤(C.conjTranspose*C).trace.re :=
  positive_norm_le_trace _ (Matrix.posSemidef_conjTranspose_mul_self C)

end DeflationContinuation

end Qatlib.Concepts.MatrixAccess.MatrixBackend.RationalQsp.Data.SourceInput
