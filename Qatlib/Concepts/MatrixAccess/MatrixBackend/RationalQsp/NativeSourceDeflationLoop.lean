/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.MatrixAccess.MatrixBackend.RationalQsp.NativeSourceIdealPreservation
import Qatlib.Concepts.MatrixAccess.MatrixBackend.PolynomialArrays.Public
import Qatlib.Concepts.MatrixAccess.MatrixBackend.PolynomialArrays.Verifier
import Qatlib.Concepts.MatrixAccess.MatrixBackend.NativeWords.RationalCircle
import Qatlib.Concepts.MatrixAccess.MatrixBackend.NativeWords.HouseholderRotationTable
import Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords.NativeHouseholder
import Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords.NativePhasePrecision

set_option backward.isDefEq.respectTransparency false

/-! Same-input complete coefficient deflation and incoming normalization guards.
This does not certify discovered phases, terminal base, full interpreter or costs. -/
set_option autoImplicit false
noncomputable section
namespace Qatlib.Concepts.MatrixAccess.MatrixBackend.RationalQsp.Data.SourceInput
open Qatlib.Concepts.MatrixAccess.MatrixBackend.PolynomialArrays Qatlib.Concepts.MatrixAccess.MatrixBackend.PolynomialArrays.SourceInput Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords.Prep Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords.Data Qatlib.Concepts.MatrixAccess.MatrixBackend.NativeWords


open Qatlib.Concepts.MatrixAccess.MatrixBackend.RationalQsp.Data

section DeflationLoop

open Qatlib.Concepts.MatrixAccess.MatrixBackend.RationalQsp.Data.SourceInput
open scoped Matrix.Norms.L2Operator

/-- Construction for source Deflation Loop in the native source deflation loop model. -/
def sourceDeflationLoop : {d : ℕ} → (Fin (d+1) → Matrix Bool Bool (ℚ×ℚ)) → ℚ → Matrix Bool Bool (ℚ×ℚ)
  | 0,F,_ => F 0
  | m+1,F,eta => sourceDeflationLoop (sourceDeflationStep (m:=m) F eta) eta

/-- Construction for source Ideal Deflation Loop in the native source deflation loop model. -/
def sourceIdealDeflationLoop : {d : ℕ} → (Fin (d+1) → Matrix Bool Bool ℂ) → Matrix Bool Bool ℂ
  | 0,F => F 0
  | m+1,F => sourceIdealDeflationLoop (sourceIdealDeflationStep (m:=m) F)

/-- Construction for Source Deflation Loop Guards in the native source deflation loop model. -/
def SourceDeflationLoopGuards : {d : ℕ} → (Fin (d+1) → Matrix Bool Bool (ℚ×ℚ)) → ℚ → Prop
  | 0,_,_ => True
  | m+1,F,eta =>
    ((sourceGaussianGramTrace (F 0)).2=0 ∧ 0<(sourceGaussianGramTrace (F 0)).1) ∧
    ((sourceGaussianGramTrace (F (Fin.last (m+1)))).2=0 ∧ 0<(sourceGaussianGramTrace (F (Fin.last (m+1)))).1) ∧
    SourceDeflationLoopGuards (sourceDeflationStep (m:=m) F eta) eta

/-- The estimate `sourceDeflationLoop_error` retains the actual parameter, input-error and normalization budgets. -/
theorem sourceDeflationLoop_error {d : ℕ}
    (F : Fin (d+1) → Matrix Bool Bool (ℚ×ℚ)) (G : Fin (d+1) → Matrix Bool Bool ℂ)
    (eta : ℚ) (heta : 0<eta) (delta h : ℝ) (hh : 0<h) (hh1 : h≤1)
    (heta_delta : (eta : ℝ)≤delta) (hinv : SourceIdealDeflationInvariant G h)
    (he : ∀ j,‖sourceDecodeCompletionMatrix (F j)-G j‖≤delta)
    (hcap : delta*(30/h)^d≤h/4) :
    SourceDeflationLoopGuards F eta ∧
      ‖sourceDecodeCompletionMatrix (sourceDeflationLoop F eta)-sourceIdealDeflationLoop G‖≤delta*(30/h)^d := by
  induction d generalizing delta with
  | zero => exact ⟨trivial,by simpa only [sourceDeflationLoop,sourceIdealDeflationLoop,pow_zero,mul_one] using he 0⟩
  | succ m ih =>
    have hd : 0≤delta := (norm_nonneg _).trans (he 0)
    have ha : 1≤30/h := (le_div_iff₀ hh).mpr (by linarith)
    have hpow : 1≤(30/h)^(m+1) := one_le_pow₀ ha
    have hcap0 : delta≤h/4 := calc
      delta=delta*1 := (mul_one _).symm
      _≤delta*(30/h)^(m+1) := mul_le_mul_of_nonneg_left hpow hd
      _≤h/4 := hcap
    have hl : G 0≠0 := norm_pos_iff.mp (hh.trans_le hinv.2.1)
    have hr : G (Fin.last (m+1))≠0 := norm_pos_iff.mp (hh.trans_le hinv.2.2)
    have hdet := sourceCompletionCircle_extreme_determinants_zero (by omega : 0 < m + 1) G hinv.1 hl hr
    have hs := sourceDeflationStep_error F G eta heta delta h hh hh1 hcap0 heta_delta he
      (sourceCompletionCircle_coefficient_norm G hinv.1) hinv.2.1 hinv.2.2
      (sourceGram_trace_eq_norm_sq _ hdet.1) (sourceGram_trace_eq_norm_sq _ hdet.2)
    have hnext : ∀ j,‖sourceDecodeCompletionMatrix (sourceDeflationStep F eta j)-sourceIdealDeflationStep G j‖≤
        delta*(30/h) := by
      intro j
      convert hs.2.2 j using 1; ring
    have hetanext : (eta : ℝ)≤delta*(30/h) :=
      heta_delta.trans (by simpa using mul_le_mul_of_nonneg_left ha hd)
    have hcapnext : (delta*(30/h))*(30/h)^m≤h/4 := by
      convert hcap using 1; rw [pow_succ]; ring
    have hi := ih (sourceDeflationStep F eta) (sourceIdealDeflationStep G) (delta*(30/h)) hetanext
      (sourceIdealDeflation_invariant G h hh hinv) hnext hcapnext
    refine ⟨⟨hs.1,hs.2.1,hi.1⟩,?_⟩
    change ‖sourceDecodeCompletionMatrix (sourceDeflationLoop (sourceDeflationStep F eta) eta)-
      sourceIdealDeflationLoop (sourceIdealDeflationStep G)‖≤delta*(30/h)^(m+1)
    convert hi.2 using 1; rw [pow_succ]; ring

end DeflationLoop

end Qatlib.Concepts.MatrixAccess.MatrixBackend.RationalQsp.Data.SourceInput
