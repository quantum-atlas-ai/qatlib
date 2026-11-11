/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.MatrixAccess.MatrixBackend.RationalQsp.NativeSourceGramNormalization
import Qatlib.Concepts.MatrixAccess.MatrixBackend.PolynomialArrays.Public
import Qatlib.Concepts.MatrixAccess.MatrixBackend.PolynomialArrays.Verifier
import Qatlib.Concepts.MatrixAccess.MatrixBackend.NativeWords.RationalCircle
import Qatlib.Concepts.MatrixAccess.MatrixBackend.NativeWords.HouseholderRotationTable
import Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords.NativeHouseholder
import Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords.NativePhasePrecision

set_option backward.isDefEq.respectTransparency false

/-! Same original-input Gaussian Gram normalization and first deflation: DeflationStep.
This does not certify subsequent ideal preservation, the whole loop, interpreter or fees. -/
set_option autoImplicit false
noncomputable section
namespace Qatlib.Concepts.MatrixAccess.MatrixBackend.RationalQsp.Data.SourceInput
open Qatlib.Concepts.MatrixAccess.MatrixBackend.PolynomialArrays Qatlib.Concepts.MatrixAccess.MatrixBackend.PolynomialArrays.SourceInput Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords.Prep Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords.Data Qatlib.Concepts.MatrixAccess.MatrixBackend.NativeWords


section DeflationStep

open Qatlib.Concepts.MatrixAccess.MatrixBackend.RationalQsp.Data
open Qatlib.Concepts.MatrixAccess.MatrixBackend.RationalQsp.Data.SourceInput
open scoped Matrix.Norms.L2Operator

/-- Construction for source Deflation Cell in the native source deflation step model. -/
def sourceDeflationCell (CL CR P Q : Matrix Bool Bool (ℚ×ℚ)) (eta : ℚ) : Matrix Bool Bool (ℚ×ℚ) :=
  sourceRoundCompletionMatrix (sourceGaussianMatrixMul CL Q+sourceGaussianMatrixMul CR P) eta

/-- The finite construction in `NativeSourceDeflationStep` satisfies `qmm_decode` under the displayed hypotheses. -/
theorem qmm_decode (A B : Matrix Bool Bool (ℚ×ℚ)) :
    sourceDecodeCompletionMatrix (sourceGaussianMatrixMul A B)=sourceDecodeCompletionMatrix A*sourceDecodeCompletionMatrix B := by
  ext i j
  cases i <;> cases j <;> apply Complex.ext <;>
    simp [sourceDecodeCompletionMatrix,sourceGaussianMatrixMul,gaussianRatMul,rootRationalCoordinate,Matrix.mul_apply] <;> ring

/-- The finite construction in `NativeSourceDeflationStep` satisfies `decode_add` under the displayed hypotheses. -/
private theorem decode_add (A B : Matrix Bool Bool (ℚ×ℚ)) :
    sourceDecodeCompletionMatrix (A+B)=sourceDecodeCompletionMatrix A+sourceDecodeCompletionMatrix B := by
  ext i j
  apply Complex.ext <;> simp [sourceDecodeCompletionMatrix,rootRationalCoordinate]

/-- The estimate `multiply_error` retains the actual parameter, input-error and normalization budgets. -/
private theorem multiply_error (A A0 B B0 : Matrix Bool Bool ℂ) (delta beta v : ℝ)
    (hA : ‖A-A0‖ ≤ delta) (hB : ‖B-B0‖ ≤ beta) (hA0 : ‖A0‖ ≤ 1) (hBn : ‖B‖ ≤ v) :
    ‖A*B-A0*B0‖ ≤ delta*v+beta := by
  have hd : 0 ≤ delta := (norm_nonneg _).trans hA
  have hid : A*B-A0*B0=(A-A0)*B+A0*(B-B0) := by
    rw [sub_mul,mul_sub]
    abel
  rw [hid]
  calc
    _ ≤ ‖(A-A0)*B‖+‖A0*(B-B0)‖ := norm_add_le _ _
    _ ≤ ‖A-A0‖*‖B‖+‖A0‖*‖B-B0‖ := add_le_add (norm_mul_le _ _) (norm_mul_le _ _)
    _ ≤ delta*v+1*beta := add_le_add
      (mul_le_mul hA hBn (norm_nonneg _) hd) (mul_le_mul hA0 hB (norm_nonneg _) (by norm_num))
    _ = _ := by ring

/-- The estimate `sourceDeflationCell_error` retains the actual parameter, input-error and normalization budgets. -/
theorem sourceDeflationCell_error (CL CR P Q : Matrix Bool Bool (ℚ×ℚ))
    (L0 R0 P0 Q0 : Matrix Bool Bool ℂ) (eta : ℚ) (heta : 0<eta) (delta beta : ℝ)
    (hL : ‖sourceDecodeCompletionMatrix CL-L0‖ ≤ delta)
    (hR : ‖sourceDecodeCompletionMatrix CR-R0‖ ≤ delta)
    (hP : ‖sourceDecodeCompletionMatrix P-P0‖ ≤ beta)
    (hQ : ‖sourceDecodeCompletionMatrix Q-Q0‖ ≤ beta)
    (hL0 : ‖L0‖ ≤ 1) (hR0 : ‖R0‖ ≤ 1)
    (hPn : ‖sourceDecodeCompletionMatrix P‖ ≤ 1+(eta : ℝ))
    (hQn : ‖sourceDecodeCompletionMatrix Q‖ ≤ 1+(eta : ℝ)) :
    ‖sourceDecodeCompletionMatrix (sourceDeflationCell CL CR P Q eta)-(L0*Q0+R0*P0)‖ ≤
      2*delta*(1+(eta : ℝ))+2*beta+(eta : ℝ) := by
  have h0 := multiply_error _ L0 _ Q0 delta beta _ hL hQ hL0 hQn
  have h1 := multiply_error _ R0 _ P0 delta beta _ hR hP hR0 hPn
  have hr := sourceRoundCompletionMatrix_error (sourceGaussianMatrixMul CL Q+sourceGaussianMatrixMul CR P) eta heta
  change ‖sourceDecodeCompletionMatrix (sourceDeflationCell CL CR P Q eta)-
    sourceDecodeCompletionMatrix (sourceGaussianMatrixMul CL Q+sourceGaussianMatrixMul CR P)‖ ≤ (eta : ℝ) at hr
  rw [decode_add,qmm_decode,qmm_decode] at hr
  have hs : ‖sourceDecodeCompletionMatrix CL*sourceDecodeCompletionMatrix Q+
      sourceDecodeCompletionMatrix CR*sourceDecodeCompletionMatrix P-(L0*Q0+R0*P0)‖ ≤
      2*(delta*(1+(eta : ℝ))+beta) := by
    rw [show sourceDecodeCompletionMatrix CL*sourceDecodeCompletionMatrix Q+
      sourceDecodeCompletionMatrix CR*sourceDecodeCompletionMatrix P-(L0*Q0+R0*P0)=
      (sourceDecodeCompletionMatrix CL*sourceDecodeCompletionMatrix Q-L0*Q0)+
      (sourceDecodeCompletionMatrix CR*sourceDecodeCompletionMatrix P-R0*P0) by abel]
    exact (norm_add_le _ _).trans (by linarith)
  have ht := norm_sub_le_norm_sub_add_norm_sub
    (sourceDecodeCompletionMatrix (sourceDeflationCell CL CR P Q eta))
    (sourceDecodeCompletionMatrix CL*sourceDecodeCompletionMatrix Q+
      sourceDecodeCompletionMatrix CR*sourceDecodeCompletionMatrix P) (L0*Q0+R0*P0)
  linarith

/-- Construction for source Deflation Step in the native source deflation step model. -/
def sourceDeflationStep {m : ℕ} (F : Fin (m+2) → Matrix Bool Bool (ℚ×ℚ)) (eta : ℚ) :
    Fin (m+1) → Matrix Bool Bool (ℚ×ℚ) :=
  fun j => sourceDeflationCell (F j.castSucc) (F j.succ)
    (sourceGramNormalize (F (Fin.last (m+1))) eta) (sourceGramNormalize (F 0) eta) eta

/-- Construction for source Ideal Deflation Step in the native source deflation step model. -/
def sourceIdealDeflationStep {m : ℕ} (F : Fin (m+2) → Matrix Bool Bool ℂ) :
    Fin (m+1) → Matrix Bool Bool ℂ :=
  fun j => F j.castSucc*sourceComplexGramNormalize (F 0)+F j.succ*sourceComplexGramNormalize (F (Fin.last (m+1)))


/-- The finite construction in `NativeSourceDeflationStep` satisfies `source_step_frequency` under the displayed hypotheses. -/
theorem source_step_frequency {m : ℕ} (j : Fin (m+1)) :
    (@sourceCompletionFrequency m j)-1=@sourceCompletionFrequency (m+1) j.castSucc ∧
      (@sourceCompletionFrequency m j)+1=@sourceCompletionFrequency (m+1) j.succ := by
  constructor <;> simp [sourceCompletionFrequency] <;> ring

/-- The estimate `step_numeric_bound` retains the actual parameter, input-error and normalization budgets. -/
private theorem step_numeric_bound (delta h eta : ℝ) (hh : 0<h) (hh1 : h ≤ 1)
    (hd : 0 ≤ delta) (he : eta ≤ delta) (hcap : delta ≤ h/4) :
    2*delta*(1+eta)+2*(12*delta/h+eta)+eta ≤ 30*delta/h := by
  have he4 : eta ≤ 1/4 := by linarith
  have ht : 2*delta*eta ≤ delta/2 := by nlinarith
  have hdiv : 6*delta ≤ 6*delta/h :=
    (le_div_iff₀ hh).mpr (mul_le_of_le_one_right (by positivity) hh1)
  calc
    _ ≤ 6*delta+24*delta/h := by
      rw [show 2*delta*(1+eta)+2*(12*delta/h+eta)+eta=
        2*delta+2*delta*eta+24*delta/h+3*eta by ring]
      linarith
    _ ≤ 6*delta/h+24*delta/h := add_le_add hdiv (le_refl _)
    _ = _ := by ring

/-- The estimate `sourceDeflationStep_error` retains the actual parameter, input-error and normalization budgets. -/
theorem sourceDeflationStep_error {m : ℕ}
    (F : Fin (m+2) → Matrix Bool Bool (ℚ×ℚ)) (G : Fin (m+2) → Matrix Bool Bool ℂ)
    (eta : ℚ) (heta : 0<eta) (delta h : ℝ) (hh : 0<h) (hh1 : h ≤ 1)
    (hcap : delta ≤ h/4) (heta_delta : (eta : ℝ) ≤ delta)
    (he : ∀ j,‖sourceDecodeCompletionMatrix (F j)-G j‖ ≤ delta)
    (hGn : ∀ j,‖G j‖ ≤ 1)
    (hleft : h ≤ ‖G 0‖) (hright : h ≤ ‖G (Fin.last (m+1))‖)
    (hleftRank : ((G 0).conjTranspose*G 0).trace.re=‖G 0‖^2)
    (hrightRank : ((G (Fin.last (m+1))).conjTranspose*G (Fin.last (m+1))).trace.re=
      ‖G (Fin.last (m+1))‖^2) :
    ((sourceGaussianGramTrace (F 0)).2=0 ∧ 0<(sourceGaussianGramTrace (F 0)).1) ∧
      ((sourceGaussianGramTrace (F (Fin.last (m+1)))).2=0 ∧ 0<(sourceGaussianGramTrace (F (Fin.last (m+1)))).1) ∧
      ∀ j,‖sourceDecodeCompletionMatrix (sourceDeflationStep F eta j)-sourceIdealDeflationStep G j‖ ≤
        30*delta/h := by
  have hd : 0 ≤ delta := (norm_nonneg _).trans (he 0)
  have hL := sourceGramNormalize_stability (F 0) (G 0) delta eta heta (hh.trans_le hleft)
    (he 0) (by linarith) hleftRank
  have hR := sourceGramNormalize_stability (F (Fin.last (m+1))) (G (Fin.last (m+1))) delta eta heta
    (hh.trans_le hright) (he _) (by linarith) hrightRank
  refine ⟨⟨hL.1,hL.2.1⟩,⟨hR.1,hR.2.1⟩,?_⟩
  intro j
  have hLe : ‖sourceDecodeCompletionMatrix (sourceGramNormalize (F 0) eta)-sourceComplexGramNormalize (G 0)‖ ≤
      12*delta/h+(eta : ℝ) := hL.2.2.2.trans
    (add_le_add (div_le_div_of_nonneg_left (show 0 ≤ 12*delta by positivity) hh hleft) (le_refl _))
  have hRe : ‖sourceDecodeCompletionMatrix (sourceGramNormalize (F (Fin.last (m+1))) eta)-
      sourceComplexGramNormalize (G (Fin.last (m+1)))‖ ≤ 12*delta/h+(eta : ℝ) := hR.2.2.2.trans
    (add_le_add (div_le_div_of_nonneg_left (show 0 ≤ 12*delta by positivity) hh hright) (le_refl _))
  have hs := sourceDeflationCell_error (F j.castSucc) (F j.succ)
    (sourceGramNormalize (F (Fin.last (m+1))) eta) (sourceGramNormalize (F 0) eta)
    (G j.castSucc) (G j.succ) (sourceComplexGramNormalize (G (Fin.last (m+1)))) (sourceComplexGramNormalize (G 0))
    eta heta delta (12*delta/h+(eta : ℝ)) (he _) (he _) hRe hLe (hGn _) (hGn _) hR.2.2.1 hL.2.2.1
  exact hs.trans (step_numeric_bound delta h (eta : ℝ) hh hh1 hd heta_delta hcap)

end DeflationStep

end Qatlib.Concepts.MatrixAccess.MatrixBackend.RationalQsp.Data.SourceInput
