/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.MatrixAccess.MatrixBackend.RationalQsp.NativeSourceProducerGuards
import Qatlib.Concepts.MatrixAccess.MatrixBackend.PolynomialArrays.Public
import Qatlib.Concepts.MatrixAccess.MatrixBackend.PolynomialArrays.Verifier
import Qatlib.Concepts.MatrixAccess.MatrixBackend.NativeWords.RationalCircle
import Qatlib.Concepts.MatrixAccess.MatrixBackend.NativeWords.HouseholderRotationTable
import Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords.NativeHouseholder
import Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords.NativePhasePrecision

set_option backward.isDefEq.respectTransparency false

/-! Same original-input spectral completion: SpectralInput.
This does not certify the full proposer, iterative deflation, interpreter or fees. -/
set_option autoImplicit false
noncomputable section
namespace Qatlib.Concepts.MatrixAccess.MatrixBackend.RationalQsp.Data.SourceInput
open Qatlib.Concepts.MatrixAccess.MatrixBackend.PolynomialArrays Qatlib.Concepts.MatrixAccess.MatrixBackend.PolynomialArrays.SourceInput Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords.Prep Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords.Data Qatlib.Concepts.MatrixAccess.MatrixBackend.NativeWords


section CompletionInput

open Qatlib.Concepts.MatrixAccess.MatrixBackend.RationalQsp.Data
open Qatlib.Concepts.MatrixAccess.MatrixBackend.RationalQsp.Data.SourceInput
open scoped BigOperators

/-- Construction for source Actual A1 in the native source spectral input model. -/
def sourceActualA1 (cs : List ℚ) (N : ℕ) (E : ℚ) : ℚ :=
  sourceAAt cs N E 0+2*∑ j : Fin (sourceDegree cs N E),sourceAAt cs N E (j.val+1)

/-- Construction for source Actual H1 in the native source spectral input model. -/
def sourceActualH1 (cs : List ℚ) (N : ℕ) (E : ℚ) : ℚ := 1-(sourceActualA1 cs N E)^2

/-- The finite construction in `NativeSourceSpectralInput` satisfies `sourceActualA1_sum` under the displayed hypotheses. -/
private theorem sourceActualA1_sum (cs : List ℚ) (N : ℕ) (E : ℚ) :
    (∑ j : Fin (N+1),sourceOutputCoefficient cs N E j)=sourceActualA1 cs N E := by
  let d := sourceDegree cs N E
  let f : ℕ → ℚ := fun j => (if j=0 then 1 else 2)*sourceAAt cs N E j
  have hf : (∑ j : Fin (N+1),sourceOutputCoefficient cs N E j)=∑ j : Fin (N+1),f j.val := by
    apply Finset.sum_congr rfl
    intro j _
    dsimp only [f]
    rw [sourceOutputCoefficient,sourceWeight,sourceAAt_of_lt cs N E j.val j.isLt]
  have ht : (∑ j : Fin (N+1),f j.val)=∑ j : Fin (d+1),f j.val := by
    rw [← Finset.sum_range,← Finset.sum_range]
    symm
    apply Finset.sum_subset (Finset.range_mono (Nat.succ_le_succ (sourceDegree_le cs N E)))
    intro j _ hj
    have hdj : d<j := by
      have h : d+1 ≤ j := by simpa only [Finset.mem_range,not_lt] using hj
      omega
    simp only [f,sourceAAt_tail cs N E j hdj,mul_zero]
  rw [hf,ht,Fin.sum_univ_succ]
  change f 0+(∑ j : Fin d,f (j.val+1))=sourceActualA1 cs N E
  simp [f,sourceActualA1,Finset.mul_sum]
  rfl

/-- The finite construction in `NativeSourceSpectralInput` satisfies `sourceActualA1_eval` under the displayed hypotheses. -/
theorem sourceActualA1_eval (cs : List ℚ) (N : ℕ) (E : ℚ) :
    (nativeChebyshevPolynomialFrom 0 (sourceOutputList cs N E)).eval 1=
      (sourceActualA1 cs N E : ℝ) := by
  have h := sourceOutput_cos cs N E 0
  simp only [Real.cos_zero,mul_zero,mul_one] at h
  rw [h]
  have he := congrArg (fun q : ℚ => (q : ℝ)) (sourceActualA1_sum cs N E)
  push_cast at he
  exact he

/-- The finite construction in `NativeSourceSpectralInput` satisfies `sourceActualH1_pos` under the displayed hypotheses. -/
theorem sourceActualH1_pos (cs : List ℚ) (N : ℕ) (E : ℚ) (hE : 0<E)
    (htail : ∀ k,N+1 ≤ k → cs.getD k 0=0)
    (hnorm : ∀ x∈Set.Icc (-1 : ℝ) 1,|(nativeChebyshevPolynomialFrom 0 cs).eval x| ≤ 1) :
    0<sourceActualH1 cs N E := by
  have h := sourceOutput_uniform_gap cs N E hE htail hnorm 1 (by constructor <;> norm_num)
  rw [sourceActualA1_eval] at h
  have hm := sourceMu_pos cs N E hE
  have ha : |(sourceActualA1 cs N E : ℝ)|<1 := by change 0<3*(sourceInputU cs N E : ℝ)/32 at hm; linarith
  have hs : (sourceActualA1 cs N E : ℝ)^2<1 := (sq_lt_one_iff_abs_lt_one _).mpr ha
  unfold sourceActualH1
  exact_mod_cast sub_pos.mpr hs

/-- The finite construction in `NativeSourceSpectralInput` satisfies `sourceActualH1_le_one` under the displayed hypotheses. -/
theorem sourceActualH1_le_one (cs : List ℚ) (N : ℕ) (E : ℚ) :
    sourceActualH1 cs N E ≤ 1 := by
  unfold sourceActualH1
  nlinarith [sq_nonneg (sourceActualA1 cs N E)]

/-- The finite construction in `NativeSourceSpectralInput` satisfies `sourceF_eval_one` under the displayed hypotheses. -/
theorem sourceF_eval_one (cs : List ℚ) (N : ℕ) (E : ℚ)
    (hparity : ∀ j : Fin (N+1),j.val%2≠N%2 → cs.getD j.val 0=0)
    (hd : 0<sourceDegree cs N E) :
    (sourceF cs N E).eval 1=(sourceActualH1 cs N E : ℂ) := by
  have h := sourceF_exp cs N E hparity hd 0
  simp only [Complex.ofReal_zero,zero_mul,mul_zero,Complex.exp_zero,one_pow,one_mul,
    Real.cos_zero,sourceActualA1_eval] at h
  rw [h]
  norm_cast

example : sourceActualH1 [0,1] 1 (1/8)=511/65536 := by decide +kernel

end CompletionInput

end Qatlib.Concepts.MatrixAccess.MatrixBackend.RationalQsp.Data.SourceInput
