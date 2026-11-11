/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.MatrixAccess.MatrixBackend.RationalQsp.NativeSourceIdealExtremes
import Qatlib.Concepts.MatrixAccess.MatrixBackend.RationalQsp.NativeSourceDeflationStep
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

section IdealPreservation

/-- The finite construction in `NativeSourceIdealPreservation` satisfies `sourceCompletionFrequency_rev` under the displayed hypotheses. -/
private theorem sourceCompletionFrequency_rev {d : ℕ} (j : Fin (d+1)) :
    sourceCompletionFrequency j.rev= -sourceCompletionFrequency j := by
  simp only [sourceCompletionFrequency,Fin.val_rev]
  omega

open Qatlib.Concepts.BlockEncoding.Encoding
open Matrix
open scoped BigOperators Matrix.Norms.L2Operator ComplexOrder
local instance : Fact (0<2*Real.pi) := ⟨Real.two_pi_pos⟩

/-- Construction for source Completion Reverse Adjoint in the native source ideal preservation model. -/
def sourceCompletionReverseAdjoint {d : ℕ} (F : Fin (d+1) → Matrix Bool Bool ℂ) : Fin (d+1) → Matrix Bool Bool ℂ :=
  fun j => (F j.rev).conjTranspose

/-- The finite construction in `NativeSourceIdealPreservation` satisfies `sourceCompletionReverseAdjoint_value` under the displayed hypotheses. -/
theorem sourceCompletionReverseAdjoint_value {d : ℕ} (F : Fin (d+1) → Matrix Bool Bool ℂ)
    (t : AddCircle (2*Real.pi)) : sourceCompletionCircleValue (sourceCompletionReverseAdjoint F) t=(sourceCompletionCircleValue F t).conjTranspose := by
  unfold sourceCompletionCircleValue sourceCompletionReverseAdjoint
  rw [Matrix.conjTranspose_sum]
  simp only [Matrix.conjTranspose_smul]
  exact Fintype.sum_equiv Fin.revPerm _ _ (fun j => by simp [sourceCompletionFrequency_rev])

/-- The finite construction in `NativeSourceIdealPreservation` satisfies `sourceCompletionCircle_extreme_left_orthogonality` under the displayed hypotheses. -/
theorem sourceCompletionCircle_extreme_left_orthogonality {d : ℕ} (hd : 0<d) (F : Fin (d+1) → Matrix Bool Bool ℂ)
    (hunit : ∀ t : AddCircle (2*Real.pi),sourceCompletionCircleValue F t∈Matrix.unitaryGroup Bool ℂ) :
    F (Fin.last d)*(F 0).conjTranspose=0 := by
  have hrev (t : AddCircle (2*Real.pi)) : sourceCompletionCircleValue (sourceCompletionReverseAdjoint F) t∈Matrix.unitaryGroup Bool ℂ := by
    rw [sourceCompletionReverseAdjoint_value,Matrix.mem_unitaryGroup_iff,Matrix.star_eq_conjTranspose]
    simpa only [Matrix.conjTranspose_conjTranspose,Matrix.star_eq_conjTranspose] using (hunit t).1
  have h := sourceCompletionCircle_extreme_orthogonality hd (sourceCompletionReverseAdjoint F) hrev
  simpa [sourceCompletionReverseAdjoint] using h

/-- The finite construction in `NativeSourceIdealPreservation` satisfies `sourceComplexGram_trace_real` under the displayed hypotheses. -/
theorem sourceComplexGram_trace_real (C : Matrix Bool Bool ℂ) :
    (C.conjTranspose*C).trace=(((C.conjTranspose*C).trace.re : ℝ) : ℂ) := by
  apply Complex.ext
  · rfl
  · change (C.conjTranspose*C).trace.im=0
    simp [Matrix.trace,Matrix.mul_apply,Matrix.conjTranspose_apply,Complex.mul_im]
    ring

/-- The finite construction in `NativeSourceIdealPreservation` satisfies `sourceComplexGram_trace_pos` under the displayed hypotheses. -/
theorem sourceComplexGram_trace_pos (C : Matrix Bool Bool ℂ) (hc : C≠0) :
    0<(C.conjTranspose*C).trace.re := by
  have h := sourceComplexGram_norm_le_trace C
  rw [Matrix.l2_opNorm_conjTranspose_mul_self] at h
  have hp := norm_pos_iff.mpr hc
  nlinarith

/-- The finite construction in `NativeSourceIdealPreservation` satisfies `sourceComplexGramNormalize_trace` under the displayed hypotheses. -/
theorem sourceComplexGramNormalize_trace (C : Matrix Bool Bool ℂ) (hc : C≠0) :
    (sourceComplexGramNormalize C).trace=1 := by
  have ht := sourceComplexGram_trace_pos C hc
  unfold sourceComplexGramNormalize
  rw [Matrix.trace_smul,sourceComplexGram_trace_real,smul_eq_mul,← Complex.ofReal_mul,Complex.ofReal_re,
    one_div_mul_cancel ht.ne',Complex.ofReal_one]

/-- The finite construction in `NativeSourceIdealPreservation` satisfies `sourceComplexGramNormalize_hermitian` under the displayed hypotheses. -/
theorem sourceComplexGramNormalize_hermitian (C : Matrix Bool Bool ℂ) :
    (sourceComplexGramNormalize C).conjTranspose=sourceComplexGramNormalize C := by
  unfold sourceComplexGramNormalize
  rw [Matrix.conjTranspose_smul]
  simp only [Complex.star_def,Complex.conj_ofReal,Matrix.conjTranspose_mul,Matrix.conjTranspose_conjTranspose]

/-- The finite construction in `NativeSourceIdealPreservation` satisfies `two_matrix_bilinear` under the displayed hypotheses. -/
private theorem two_matrix_bilinear (P Q : Matrix Bool Bool ℂ) :
    P*Q+Q*P=P.trace • Q+Q.trace • P+((P*Q).trace-P.trace*Q.trace) • (1 : Matrix Bool Bool ℂ) := by
  ext i j
  cases i <;> cases j <;>
    simp [Matrix.mul_apply,Matrix.trace] <;> ring

/-- The finite construction in `NativeSourceIdealPreservation` satisfies `sourceComplexGramNormalize_complement` under the displayed hypotheses. -/
theorem sourceComplexGramNormalize_complement (C D : Matrix Bool Bool ℂ)
    (hc : C≠0) (hd : D≠0) (hcross : C*D.conjTranspose=0) :
    sourceComplexGramNormalize C*sourceComplexGramNormalize D=0 ∧ sourceComplexGramNormalize D*sourceComplexGramNormalize C=0 ∧
      sourceComplexGramNormalize C+sourceComplexGramNormalize D=1 := by
  have hPQ : sourceComplexGramNormalize C*sourceComplexGramNormalize D=0 := by
    unfold sourceComplexGramNormalize
    rw [smul_mul_assoc,mul_smul_comm,smul_smul]
    have he : (C.conjTranspose*C)*(D.conjTranspose*D)=C.conjTranspose*(C*D.conjTranspose)*D := by
      simp only [mul_assoc]
    rw [he,hcross]
    simp
  have hQP : sourceComplexGramNormalize D*sourceComplexGramNormalize C=0 := by
    have h := congrArg Matrix.conjTranspose hPQ
    simpa only [Matrix.conjTranspose_mul,sourceComplexGramNormalize_hermitian,Matrix.conjTranspose_zero] using h
  have hbil := two_matrix_bilinear (sourceComplexGramNormalize C) (sourceComplexGramNormalize D)
  have hz : sourceComplexGramNormalize D+sourceComplexGramNormalize C-(1 : Matrix Bool Bool ℂ)=0 := by
    simpa [hPQ,hQP,sourceComplexGramNormalize_trace C hc,sourceComplexGramNormalize_trace D hd, sub_eq_add_neg] using hbil.symm
  exact ⟨hPQ,hQP,by simpa only [add_comm] using sub_eq_zero.mp hz⟩

end IdealPreservation

section IdealStep

open scoped BigOperators Matrix.Norms.L2Operator
local instance : Fact (0<2*Real.pi) := ⟨Real.two_pi_pos⟩

/-- The finite construction in `NativeSourceIdealPreservation` satisfies `sourceMulComplexGramNormalize_zero` under the displayed hypotheses. -/
theorem sourceMulComplexGramNormalize_zero (C D : Matrix Bool Bool ℂ) (hcross : C*D.conjTranspose=0) :
    C*sourceComplexGramNormalize D=0 := by
  unfold sourceComplexGramNormalize
  rw [mul_smul_comm,← mul_assoc,hcross]
  simp

/-- The finite construction in `NativeSourceIdealPreservation` satisfies `sourceIdealDeflation_endpoints` under the displayed hypotheses. -/
theorem sourceIdealDeflation_endpoints {m : ℕ} (F : Fin (m+2) → Matrix Bool Bool ℂ)
    (hunit : ∀ t : AddCircle (2*Real.pi),sourceCompletionCircleValue F t∈Matrix.unitaryGroup Bool ℂ)
    (hl : F 0≠0) (hr : F (Fin.last (m+1))≠0) :
    let P := sourceComplexGramNormalize (F (Fin.last (m+1)))
    let Q := sourceComplexGramNormalize (F 0)
    P*Q=0 ∧ Q*P=0 ∧ P+Q=1 ∧ P*P=P ∧ Q*Q=Q ∧
      F 0*P=0 ∧ F (Fin.last (m+1))*Q=0 ∧
      F 0*Q=F 0 ∧ F (Fin.last (m+1))*P=F (Fin.last (m+1)) := by
  dsimp only
  let P := sourceComplexGramNormalize (F (Fin.last (m+1)))
  let Q := sourceComplexGramNormalize (F 0)
  have hcross := sourceCompletionCircle_extreme_left_orthogonality (by omega : 0 < m + 1) F hunit
  have hcross' : F 0*(F (Fin.last (m+1))).conjTranspose=0 := by
    simpa using congrArg Matrix.conjTranspose hcross
  obtain ⟨hPQ,hQP,hplus⟩ := sourceComplexGramNormalize_complement _ _ hr hl hcross
  have hPP : P*P=P := by
    have h := congrArg (fun M => P*M) hplus
    simpa only [P,Q,mul_add,hPQ,add_zero,mul_one] using h
  have hQQ : Q*Q=Q := by
    have h := congrArg (fun M => Q*M) hplus
    simpa only [P,Q,mul_add,hQP,zero_add,mul_one] using h
  have hLP := sourceMulComplexGramNormalize_zero _ _ hcross'
  have hRQ := sourceMulComplexGramNormalize_zero _ _ hcross
  have hLQ : F 0*Q=F 0 := by
    have h := congrArg (fun M => F 0*M) hplus
    simpa only [mul_add,hLP,zero_add,mul_one] using h
  have hRP : F (Fin.last (m+1))*P=F (Fin.last (m+1)) := by
    have h := congrArg (fun M => F (Fin.last (m+1))*M) hplus
    simpa only [mul_add,hRQ,add_zero,mul_one] using h
  exact ⟨hPQ,hQP,hplus,hPP,hQQ,hLP,hRQ,hLQ,hRP⟩

/-- The actual finite word or frame satisfies `sourceIdealDeflation_elementary_unitary` with all displayed legality, input and workspace hypotheses. -/
theorem sourceIdealDeflation_elementary_unitary (P Q : Matrix Bool Bool ℂ)
    (hP : P.conjTranspose=P) (hQ : Q.conjTranspose=Q)
    (hPQ : P*Q=0) (hQP : Q*P=0) (hplus : P+Q=1)
    (hPP : P*P=P) (hQQ : Q*Q=Q) (t : AddCircle (2*Real.pi)) :
    fourier 1 t • Q+fourier (-1) t • P∈Matrix.unitaryGroup Bool ℂ := by
  have hmul (k : ℤ) : star (fourier k t)*fourier k t=1 := by
    rw [Complex.star_def,← fourier_neg,← fourier_add,neg_add_cancel,fourier_zero]
  rw [Matrix.mem_unitaryGroup_iff,Matrix.star_eq_conjTranspose]
  simp only [Matrix.conjTranspose_add,Matrix.conjTranspose_smul,hP,hQ,
    add_mul,mul_add,smul_mul_assoc,mul_smul_comm,smul_smul,hPQ,hQP,hPP,hQQ,
    smul_zero,add_zero,zero_add,hmul,one_smul]
  simpa only [add_comm] using hplus

/-- The finite construction in `NativeSourceIdealPreservation` satisfies `sourceIdealDeflation_circle` under the displayed hypotheses. -/
theorem sourceIdealDeflation_circle {m : ℕ} (F : Fin (m+2) → Matrix Bool Bool ℂ)
    (hL : F 0*sourceComplexGramNormalize (F (Fin.last (m+1)))=0)
    (hR : F (Fin.last (m+1))*sourceComplexGramNormalize (F 0)=0)
    (t : AddCircle (2*Real.pi)) :
    sourceCompletionCircleValue (sourceIdealDeflationStep F) t=sourceCompletionCircleValue F t*
      (fourier 1 t • sourceComplexGramNormalize (F 0)+fourier (-1) t • sourceComplexGramNormalize (F (Fin.last (m+1)))) := by
  have hcast (j : Fin (m+1)) : sourceCompletionFrequency j.castSucc+1=sourceCompletionFrequency j := by
    simp only [sourceCompletionFrequency,Fin.val_castSucc]
    push_cast
    ring
  have hsucc (j : Fin (m+1)) : sourceCompletionFrequency j.succ+(-1)=sourceCompletionFrequency j := by
    simp only [sourceCompletionFrequency,Fin.val_succ]
    push_cast
    ring
  have hQ : sourceCompletionCircleValue F t*(fourier 1 t • sourceComplexGramNormalize (F 0))=
      ∑ j : Fin (m+1),fourier (sourceCompletionFrequency j) t • (F j.castSucc*sourceComplexGramNormalize (F 0)) := by
    simp only [sourceCompletionCircleValue,Finset.sum_mul,smul_mul_assoc,mul_smul_comm]
    rw [Fin.sum_univ_castSucc]
    simp only [hR,smul_zero,add_zero]
    rw [Finset.smul_sum]
    apply Finset.sum_congr rfl
    intro j _
    rw [smul_smul,← fourier_add,add_comm (1 : ℤ),hcast]
  have hP : sourceCompletionCircleValue F t*(fourier (-1) t • sourceComplexGramNormalize (F (Fin.last (m+1))))=
      ∑ j : Fin (m+1),fourier (sourceCompletionFrequency j) t • (F j.succ*sourceComplexGramNormalize (F (Fin.last (m+1)))) := by
    simp only [sourceCompletionCircleValue,Finset.sum_mul,smul_mul_assoc,mul_smul_comm]
    rw [Fin.sum_univ_succ]
    simp only [hL,smul_zero,zero_add]
    rw [Finset.smul_sum]
    apply Finset.sum_congr rfl
    intro j _
    rw [smul_smul,← fourier_add,add_comm (-1 : ℤ),hsucc]
  rw [mul_add,hQ,hP]
  simp only [sourceCompletionCircleValue,sourceIdealDeflationStep,smul_add,Finset.sum_add_distrib]

/-- The actual finite word or frame satisfies `sourceIdealDeflation_unitary` with all displayed legality, input and workspace hypotheses. -/
theorem sourceIdealDeflation_unitary {m : ℕ} (F : Fin (m+2) → Matrix Bool Bool ℂ)
    (hunit : ∀ t : AddCircle (2*Real.pi),sourceCompletionCircleValue F t∈Matrix.unitaryGroup Bool ℂ)
    (hl : F 0≠0) (hr : F (Fin.last (m+1))≠0) :
    ∀ t : AddCircle (2*Real.pi),sourceCompletionCircleValue (sourceIdealDeflationStep F) t∈Matrix.unitaryGroup Bool ℂ := by
  obtain ⟨hPQ,hQP,hplus,hPP,hQQ,hLP,hRQ,_,_⟩ := sourceIdealDeflation_endpoints F hunit hl hr
  intro t
  rw [sourceIdealDeflation_circle F hLP hRQ]
  exact (Matrix.unitaryGroup Bool ℂ).mul_mem (hunit t)
    (sourceIdealDeflation_elementary_unitary _ _ (sourceComplexGramNormalize_hermitian _) (sourceComplexGramNormalize_hermitian _)
      hPQ hQP hplus hPP hQQ t)

end IdealStep

section IdealInvariant

open scoped Matrix.Norms.L2Operator ComplexOrder

/-- The finite construction in `NativeSourceIdealPreservation` satisfies `sourceComplexGramNormalize_norm` under the displayed hypotheses. -/
theorem sourceComplexGramNormalize_norm (C : Matrix Bool Bool ℂ) (hc : C≠0) :
    ‖sourceComplexGramNormalize C‖ ≤ 1 := by
  have ht := sourceComplexGram_trace_pos C hc
  have hb := sourceComplexGram_norm_le_trace C
  unfold sourceComplexGramNormalize
  rw [norm_smul,Complex.norm_real,Real.norm_eq_abs,abs_of_pos (one_div_pos.mpr ht)]
  exact (mul_le_mul_of_nonneg_left hb (by positivity)).trans_eq (one_div_mul_cancel ht.ne')

/-- The finite construction in `NativeSourceIdealPreservation` satisfies `sourceIdealDeflation_endpoint_norm` under the displayed hypotheses. -/
theorem sourceIdealDeflation_endpoint_norm {m : ℕ} (F : Fin (m+2) → Matrix Bool Bool ℂ)
    (hunit : ∀ t : AddCircle (2*Real.pi),sourceCompletionCircleValue F t∈Matrix.unitaryGroup Bool ℂ)
    (hl : F 0≠0) (hr : F (Fin.last (m+1))≠0) :
    ‖F 0‖ ≤ ‖sourceIdealDeflationStep F 0‖ ∧
      ‖F (Fin.last (m+1))‖ ≤ ‖sourceIdealDeflationStep F (Fin.last m)‖ := by
  let P := sourceComplexGramNormalize (F (Fin.last (m+1)))
  let Q := sourceComplexGramNormalize (F 0)
  obtain ⟨hPQ,hQP,_,hPP,hQQ,_,_,hLQ,hRP⟩ := sourceIdealDeflation_endpoints F hunit hl hr
  have hbot : sourceIdealDeflationStep F 0*Q=F 0 := by
    simp only [Q,sourceIdealDeflationStep,add_mul,mul_assoc,hPQ,hQQ,mul_zero,add_zero]
    simpa only [Fin.castSucc_zero] using hLQ
  have htop : sourceIdealDeflationStep F (Fin.last m)*P=F (Fin.last (m+1)) := by
    simp only [P,sourceIdealDeflationStep,add_mul,mul_assoc,hQP,hPP,mul_zero,zero_add]
    simpa only [Fin.succ_last] using hRP
  constructor
  · rw [← hbot]
    exact (norm_mul_le _ _).trans ((mul_le_mul_of_nonneg_left
      (sourceComplexGramNormalize_norm _ hl) (norm_nonneg _)).trans_eq (mul_one _))
  · rw [← htop]
    exact (norm_mul_le _ _).trans ((mul_le_mul_of_nonneg_left
      (sourceComplexGramNormalize_norm _ hr) (norm_nonneg _)).trans_eq (mul_one _))

/-- Construction for Source Ideal Deflation Invariant in the native source ideal preservation model. -/
def SourceIdealDeflationInvariant {d : ℕ} (F : Fin (d+1) → Matrix Bool Bool ℂ) (h : ℝ) : Prop :=
  (∀ t : AddCircle (2*Real.pi),sourceCompletionCircleValue F t∈Matrix.unitaryGroup Bool ℂ) ∧
    h ≤ ‖F 0‖ ∧ h ≤ ‖F (Fin.last d)‖

/-- The finite construction in `NativeSourceIdealPreservation` satisfies `sourceIdealDeflation_invariant` under the displayed hypotheses. -/
theorem sourceIdealDeflation_invariant {m : ℕ} (F : Fin (m+2) → Matrix Bool Bool ℂ)
    (h : ℝ) (hh : 0<h) (hinv : SourceIdealDeflationInvariant F h) :
    SourceIdealDeflationInvariant (sourceIdealDeflationStep F) h := by
  have hl : F 0≠0 := norm_pos_iff.mp (hh.trans_le hinv.2.1)
  have hr : F (Fin.last (m+1))≠0 := norm_pos_iff.mp (hh.trans_le hinv.2.2)
  have hs := sourceIdealDeflation_endpoint_norm F hinv.1 hl hr
  exact ⟨sourceIdealDeflation_unitary F hinv.1 hl hr,hinv.2.1.trans hs.1,hinv.2.2.trans hs.2⟩

end IdealInvariant

end Qatlib.Concepts.MatrixAccess.MatrixBackend.RationalQsp.Data.SourceInput
