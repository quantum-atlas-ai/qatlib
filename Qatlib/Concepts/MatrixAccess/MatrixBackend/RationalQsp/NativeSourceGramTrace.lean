/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.MatrixAccess.MatrixBackend.RationalQsp.NativeSourceCompletionMatrix
import Qatlib.Concepts.MatrixAccess.MatrixBackend.PolynomialArrays.Public
import Qatlib.Concepts.MatrixAccess.MatrixBackend.PolynomialArrays.Verifier
import Qatlib.Concepts.MatrixAccess.MatrixBackend.NativeWords.RationalCircle
import Qatlib.Concepts.MatrixAccess.MatrixBackend.NativeWords.HouseholderRotationTable
import Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords.NativeHouseholder
import Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords.NativePhasePrecision

set_option backward.isDefEq.respectTransparency false

/-! Same original-input Gaussian Gram normalization and first deflation: GramTrace.
This does not certify subsequent ideal preservation, the whole loop, interpreter or fees. -/
set_option autoImplicit false
noncomputable section
namespace Qatlib.Concepts.MatrixAccess.MatrixBackend.RationalQsp.Data.SourceInput
open Qatlib.Concepts.MatrixAccess.MatrixBackend.PolynomialArrays Qatlib.Concepts.MatrixAccess.MatrixBackend.PolynomialArrays.SourceInput Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords.Prep Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords.Data Qatlib.Concepts.MatrixAccess.MatrixBackend.NativeWords


section GramTrace

open Qatlib.Concepts.MatrixAccess.MatrixBackend.RationalQsp.Data
open Qatlib.Concepts.MatrixAccess.MatrixBackend.RationalQsp.Data.SourceInput
open scoped BigOperators

/-- Construction for source Gaussian Adjoint in the native source gram trace model. -/
def sourceGaussianAdjoint (A : Matrix Bool Bool (ℚ×ℚ)) : Matrix Bool Bool (ℚ×ℚ) :=
  fun i j => ((A j i).1,-(A j i).2)
/-- Construction for source Gaussian Matrix Mul in the native source gram trace model. -/
def sourceGaussianMatrixMul (A B : Matrix Bool Bool (ℚ×ℚ)) : Matrix Bool Bool (ℚ×ℚ) :=
  fun i j => gaussianRatMul (A i false) (B false j)+gaussianRatMul (A i true) (B true j)
/-- Construction for source Gaussian Norm Sq in the native source gram trace model. -/
def sourceGaussianNormSq (v : ℚ×ℚ) : ℚ := v.1^2+v.2^2
/-- Construction for source Gaussian Gram in the native source gram trace model. -/
def sourceGaussianGram (A : Matrix Bool Bool (ℚ×ℚ)) : Matrix Bool Bool (ℚ×ℚ) := sourceGaussianMatrixMul (sourceGaussianAdjoint A) A
/-- Construction for source Gaussian Gram Trace in the native source gram trace model. -/
def sourceGaussianGramTrace (A : Matrix Bool Bool (ℚ×ℚ)) : ℚ×ℚ := sourceGaussianGram A false false+sourceGaussianGram A true true

/-- The finite construction in `NativeSourceGramTrace` satisfies `sourceGaussianGramTrace_identity` under the displayed hypotheses. -/
theorem sourceGaussianGramTrace_identity (A : Matrix Bool Bool (ℚ×ℚ)) :
    (sourceGaussianGramTrace A).1=(∑ i : Bool,∑ j : Bool,sourceGaussianNormSq (A i j)) ∧
      (sourceGaussianGramTrace A).2=0 := by
  constructor <;> simp [sourceGaussianGramTrace,sourceGaussianGram,sourceGaussianMatrixMul,sourceGaussianAdjoint,gaussianRatMul,sourceGaussianNormSq] <;> ring

/-- The finite construction in `NativeSourceGramTrace` satisfies `qnorm2_nonneg` under the displayed hypotheses. -/
private theorem qnorm2_nonneg (v : ℚ×ℚ) : 0 ≤ sourceGaussianNormSq v := by
  unfold sourceGaussianNormSq
  positivity

/-- The finite construction in `NativeSourceGramTrace` satisfies `qnorm2_pos` under the displayed hypotheses. -/
private theorem qnorm2_pos (v : ℚ×ℚ) (hv : v≠(0,0)) : 0<sourceGaussianNormSq v := by
  have hn : v.1≠0 ∨ v.2≠0 := by
    by_contra h
    push Not at h
    exact hv (Prod.ext h.1 h.2)
  unfold sourceGaussianNormSq
  rcases hn with h|h
  · exact add_pos_of_pos_of_nonneg (sq_pos_of_ne_zero h) (sq_nonneg _)
  · exact add_pos_of_nonneg_of_pos (sq_nonneg _) (sq_pos_of_ne_zero h)

/-- The finite construction in `NativeSourceGramTrace` satisfies `sourceGaussianGramTrace_guard` under the displayed hypotheses. -/
theorem sourceGaussianGramTrace_guard (A : Matrix Bool Bool (ℚ×ℚ))
    (hn : ∃ i j,A i j≠(0,0)) :
    (sourceGaussianGramTrace A).2=0 ∧ 0<(sourceGaussianGramTrace A).1 := by
  obtain ⟨i,j,hij⟩ := hn
  have he := sourceGaussianGramTrace_identity A
  refine ⟨he.2,?_⟩
  rw [he.1]
  have hrow : sourceGaussianNormSq (A i j) ≤ ∑ k : Bool,sourceGaussianNormSq (A i k) :=
    Finset.single_le_sum (fun k _ => qnorm2_nonneg (A i k)) (Finset.mem_univ j)
  have htotal : (∑ k : Bool,sourceGaussianNormSq (A i k)) ≤ ∑ l : Bool,∑ k : Bool,sourceGaussianNormSq (A l k) :=
    Finset.single_le_sum (fun l _ => Finset.sum_nonneg (fun k _ => qnorm2_nonneg (A l k))) (Finset.mem_univ i)
  exact (qnorm2_pos (A i j) hij).trans_le (hrow.trans htotal)

end GramTrace

end Qatlib.Concepts.MatrixAccess.MatrixBackend.RationalQsp.Data.SourceInput
