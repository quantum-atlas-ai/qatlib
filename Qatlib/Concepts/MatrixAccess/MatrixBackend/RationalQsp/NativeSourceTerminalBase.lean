/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.MatrixAccess.MatrixBackend.RationalQsp.NativeSourceDiscoveredPhases
import Qatlib.Concepts.MatrixAccess.MatrixBackend.PolynomialArrays.Public
import Qatlib.Concepts.MatrixAccess.MatrixBackend.PolynomialArrays.Verifier
import Qatlib.Concepts.MatrixAccess.MatrixBackend.NativeWords.RationalCircle
import Qatlib.Concepts.MatrixAccess.MatrixBackend.NativeWords.HouseholderRotationTable
import Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords.NativeHouseholder
import Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords.NativePhasePrecision

set_option backward.isDefEq.respectTransparency false

/-! Original-input, accepted-certificate nonconstant source packet: TerminalBase.
Value and physical-word guarantees here do not certify a root proposer, Python interpreter or total costs. -/
set_option autoImplicit false
noncomputable section
namespace Qatlib.Concepts.MatrixAccess.MatrixBackend.RationalQsp.Data.SourceInput
open Qatlib.Concepts.MatrixAccess.MatrixBackend.PolynomialArrays Qatlib.Concepts.MatrixAccess.MatrixBackend.PolynomialArrays.SourceInput Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords.Prep Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords.Data Qatlib.Concepts.MatrixAccess.MatrixBackend.NativeWords


section TerminalBase

open Qatlib.Concepts.MatrixAccess.MatrixBackend.RationalQsp.Data
open Qatlib.Concepts.MatrixAccess.MatrixBackend.RationalQsp.Data.SourceInput
open scoped BigOperators Matrix.Norms.L2Operator
local instance : Fact (0<2*Real.pi) := ⟨Real.two_pi_pos⟩

/-- The finite construction in `NativeSourceTerminalBase` satisfies `sourceIdealDeflation_at_zero` under the displayed hypotheses. -/
theorem sourceIdealDeflation_at_zero {m : ℕ} (G : Fin (m+2) → Matrix Bool Bool ℂ)
    (h : ℝ) (hh : 0<h) (hinv : SourceIdealDeflationInvariant G h) :
    sourceCompletionCircleValue (sourceIdealDeflationStep G) (0 : AddCircle (2*Real.pi))=sourceCompletionCircleValue G 0 := by
  have hl : G 0≠0 := norm_pos_iff.mp (hh.trans_le hinv.2.1)
  have hr : G (Fin.last (m+1))≠0 := norm_pos_iff.mp (hh.trans_le hinv.2.2)
  obtain ⟨_,_,hplus,_,_,hLP,hRQ,_,_⟩ := sourceIdealDeflation_endpoints G hinv.1 hl hr
  rw [sourceIdealDeflation_circle G hLP hRQ,fourier_eval_zero,fourier_eval_zero,one_smul,one_smul]
  have hs : sourceComplexGramNormalize (G 0)+
      sourceComplexGramNormalize (G (Fin.last (m+1)))=1 := by
    simpa only [add_comm] using hplus
  rw [hs,mul_one]

/-- The finite construction in `NativeSourceTerminalBase` satisfies `sourceIdealDeflationLoop_at_zero` under the displayed hypotheses. -/
theorem sourceIdealDeflationLoop_at_zero {d : ℕ} (G : Fin (d+1) → Matrix Bool Bool ℂ)
    (h : ℝ) (hh : 0<h) (hinv : SourceIdealDeflationInvariant G h) :
    sourceIdealDeflationLoop G=sourceCompletionCircleValue G (0 : AddCircle (2*Real.pi)) := by
  induction d with
  | zero => simp [sourceIdealDeflationLoop,sourceCompletionCircleValue]
  | succ m ih =>
    calc
      _ = sourceIdealDeflationLoop (sourceIdealDeflationStep G) := rfl
      _ = sourceCompletionCircleValue (sourceIdealDeflationStep G) 0 := ih _ (sourceIdealDeflation_invariant G h hh hinv)
      _ = sourceCompletionCircleValue G 0 := sourceIdealDeflation_at_zero G h hh hinv

/-- The finite construction in `NativeSourceTerminalBase` satisfies `source_initial_zero_offdiag` under the displayed hypotheses. -/
theorem source_initial_zero_offdiag (cs : List ℚ) (N : ℕ) (E : ℚ) :
    sourceCompletionCircleValue (sourceIdealMatrixArray cs N E) (0 : AddCircle (2*Real.pi)) false true=0 ∧
      sourceCompletionCircleValue (sourceIdealMatrixArray cs N E) (0 : AddCircle (2*Real.pi)) true false=0 := by
  have hrev : (∑ j : Fin (sourceDegree cs N E+1),star (sourceIdealEArray cs N E j.rev))=
      ∑ j : Fin (sourceDegree cs N E+1),sourceIdealEArray cs N E j := by
    simp only [sourceIdealEArray_real]
    exact Fintype.sum_equiv Fin.revPerm _ _ (fun _ => rfl)
  constructor <;>
    simp only [sourceCompletionCircleValue,fourier_eval_zero,one_smul,Matrix.sum_apply]
  all_goals
    change (∑ j : Fin (sourceDegree cs N E+1),
      (sourceIdealEArray cs N E j-star (sourceIdealEArray cs N E j.rev))/2)=0
    rw [← Finset.sum_div,Finset.sum_sub_distrib,hrev,sub_self,zero_div]

/-- The finite construction in `NativeSourceTerminalBase` satisfies `source_ideal_terminal_base` under the displayed hypotheses. -/
theorem source_ideal_terminal_base (cs : List ℚ) (N : ℕ) (E : ℚ) (hE : 0<E)
    (htail : ∀ k,N+1 ≤ k → cs.getD k 0=0)
    (hparity : ∀ j : Fin (N+1),j.val%2≠N%2 → cs.getD j.val 0=0)
    (hd : 0<sourceDegree cs N E)
    (hnorm : ∀ x∈Set.Icc (-1 : ℝ) 1,|(nativeChebyshevPolynomialFrom 0 cs).eval x| ≤ 1) :
    let B := sourceIdealDeflationLoop (sourceIdealMatrixArray cs N E)
    B false true=0 ∧ B true false=0 ∧ ‖B false false‖=1 := by
  let G := sourceIdealMatrixArray cs N E
  let h := sourceGrid N (sourceInputU cs N E)
  have hh : (0 : ℝ)<(h : ℝ) := by exact_mod_cast sourceGrid_pos N (sourceInputU cs N E)
  have hinv : SourceIdealDeflationInvariant G (h : ℝ) :=
    ⟨sourceIdealArray_circle_unitary cs N E hE htail hparity hd hnorm,
      source_ideal_extreme_lower cs N E hd 0 (Or.inl rfl),
      source_ideal_extreme_lower cs N E hd _ (Or.inr rfl)⟩
  have hloop := sourceIdealDeflationLoop_at_zero G (h : ℝ) hh hinv
  have hoff := source_initial_zero_offdiag cs N E
  have hunit : sourceIdealDeflationLoop G∈Matrix.unitaryGroup Bool ℂ := by
    rw [hloop]
    exact hinv.1 0
  have h01 : sourceIdealDeflationLoop G false true=0 := by rw [hloop]; exact hoff.1
  have h10 : sourceIdealDeflationLoop G true false=0 := by rw [hloop]; exact hoff.2
  refine ⟨h01,h10,?_⟩
  have hp := congrFun (congrFun hunit.1 false) false
  simp only [Matrix.mul_apply,Fintype.sum_bool,Matrix.star_eq_conjTranspose,
    Matrix.conjTranspose_apply,h10,star_zero,mul_zero,zero_add,Matrix.one_apply_eq] at hp
  have hn := congrArg norm hp
  simp only [norm_mul,norm_star,norm_one] at hn
  nlinarith [norm_nonneg (sourceIdealDeflationLoop G false false)]

/-- The finite construction in `NativeSourceTerminalBase` satisfies `source_actual_terminal_base` under the displayed hypotheses. -/
theorem source_actual_terminal_base (cs : List ℚ) (N : ℕ) (E : ℚ) (hE : 0<E)
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
 :
    let C := sourceDeflationLoop (sourceRoundedMatrix cs N E f) (sourceInputEta cs N E)
    let B := sourceIdealDeflationLoop (sourceIdealMatrixArray cs N E)
    let h := sourceGrid N (sourceInputU cs N E)
    ‖B false false‖=1 ∧
      ‖sourceDecodeCompletionMatrix C false false-B false false‖≤(h : ℝ)/16 ∧
      sourceDecodeCompletionMatrix C false false≠0 := by
  let C := sourceDeflationLoop (sourceRoundedMatrix cs N E f) (sourceInputEta cs N E)
  let B := sourceIdealDeflationLoop (sourceIdealMatrixArray cs N E)
  let h := sourceGrid N (sourceInputU cs N E)
  have hs := source_deflation_loop cs N E hE htail hparity hd hnorm
    m content f hcontent hguard haccepted
  have hb := source_ideal_terminal_base cs N E hE htail hparity hd hnorm
  have he := (sourceCompletionMatrix_entry_norm (sourceDecodeCompletionMatrix C-B) false false).trans hs.2.2
  change ‖sourceDecodeCompletionMatrix C false false-B false false‖≤(h : ℝ)/16 at he
  have hunit : ‖B false false‖=1 := hb.2.2
  refine ⟨hunit,he,?_⟩
  intro hz
  rw [hz,zero_sub,norm_neg,hunit] at he
  have hh1 : (h : ℝ)≤1 := by
    dsimp [h,sourceGrid]
    push_cast
    exact (div_le_one (by positivity)).mpr (one_le_pow₀ (by norm_num))
  linarith

end TerminalBase

end Qatlib.Concepts.MatrixAccess.MatrixBackend.RationalQsp.Data.SourceInput
