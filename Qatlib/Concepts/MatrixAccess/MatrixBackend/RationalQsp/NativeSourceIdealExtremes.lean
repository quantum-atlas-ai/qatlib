/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.MatrixAccess.MatrixBackend.RationalQsp.NativeSourceCompletionMatrix
import Qatlib.Concepts.MatrixAccess.MatrixBackend.RationalQsp.NativeSourceGramNormalization
import Qatlib.Concepts.MatrixAccess.MatrixBackend.RationalQsp.NativeSourceInitialPivot
import Qatlib.Concepts.MatrixAccess.MatrixBackend.PolynomialArrays.Public
import Qatlib.Concepts.MatrixAccess.MatrixBackend.PolynomialArrays.Verifier
import Qatlib.Concepts.MatrixAccess.MatrixBackend.NativeWords.RationalCircle
import Qatlib.Concepts.MatrixAccess.MatrixBackend.NativeWords.HouseholderRotationTable
import Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords.NativeHouseholder
import Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords.NativePhasePrecision

set_option backward.isDefEq.respectTransparency false

/-! Same original-input Gaussian Gram normalization and first deflation: IdealExtremes.
This does not certify subsequent ideal preservation, the whole loop, interpreter or fees. -/
set_option autoImplicit false
noncomputable section
namespace Qatlib.Concepts.MatrixAccess.MatrixBackend.RationalQsp.Data.SourceInput
open Qatlib.Concepts.MatrixAccess.MatrixBackend.PolynomialArrays Qatlib.Concepts.MatrixAccess.MatrixBackend.PolynomialArrays.SourceInput Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords.Prep Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords.Data Qatlib.Concepts.MatrixAccess.MatrixBackend.NativeWords


section UnitaryExtremes

open MeasureTheory Matrix
open scoped BigOperators Matrix.Norms.L2Operator
local instance : Fact (0<2*Real.pi) := ⟨Real.two_pi_pos⟩

/-- The finite construction in `NativeSourceIdealExtremes` satisfies `term_integrable` under the displayed hypotheses. -/
private theorem term_integrable (k : ℤ) (A : Matrix Bool Bool ℂ) :
    Integrable (fun t : AddCircle (2*Real.pi) => fourier k t • A) AddCircle.haarAddCircle :=
  ((map_continuous (fourier k)).smul continuous_const).integrable_of_hasCompactSupport
    (HasCompactSupport.of_compactSpace _)

/-- The finite construction in `NativeSourceIdealExtremes` satisfies `term_coefficient` under the displayed hypotheses. -/
private theorem term_coefficient (k n : ℤ) (A : Matrix Bool Bool ℂ) :
    fourierCoeff (fun t : AddCircle (2*Real.pi) => fourier k t • A) n=if n=k then A else 0 := by
  have he : fourierCoeff (fun t : AddCircle (2*Real.pi) => fourier k t • A) n=
      (fourierCoeff (T := 2*Real.pi) (fourier k) n) • A := by
    unfold fourierCoeff
    simp only [← smul_assoc,smul_eq_mul]
    rw [integral_smul_const]
  rw [he,fourierCoeff_fourier]
  by_cases h : n=k
  · subst n; simp
  · simp [h]

/-- The finite construction in `NativeSourceIdealExtremes` satisfies `star_fourier_mul` under the displayed hypotheses. -/
private theorem star_fourier_mul (i j : ℤ) (t : AddCircle (2*Real.pi)) :
    star (fourier i t)*fourier j t=fourier (j-i) t := by
  rw [sub_eq_add_neg,fourier_add,fourier_neg]
  rw [Complex.star_def,mul_comm]

/-- The finite construction in `NativeSourceIdealExtremes` satisfies `gram_fourier_coefficient` under the displayed hypotheses. -/
private theorem gram_fourier_coefficient {d : ℕ} (F : Fin (d+1) → Matrix Bool Bool ℂ) (n : ℤ) :
    fourierCoeff (fun t : AddCircle (2*Real.pi) => (sourceCompletionCircleValue F t).conjTranspose*sourceCompletionCircleValue F t) n=
      ∑ i : Fin (d+1),∑ j : Fin (d+1),
        if n=sourceCompletionFrequency j-sourceCompletionFrequency i then (F i).conjTranspose*F j else 0 := by
  have hp : (fun t : AddCircle (2*Real.pi) => (sourceCompletionCircleValue F t).conjTranspose*sourceCompletionCircleValue F t)=
      ∑ i : Fin (d+1),∑ j : Fin (d+1),
        (fun t : AddCircle (2*Real.pi) => fourier (sourceCompletionFrequency j-sourceCompletionFrequency i) t • ((F i).conjTranspose*F j)) := by
    funext t
    simp only [sourceCompletionCircleValue,Matrix.conjTranspose_sum,Matrix.conjTranspose_smul,
      Finset.sum_mul,Finset.mul_sum,Finset.sum_apply]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    rw [smul_mul_assoc,mul_smul_comm,smul_smul,star_fourier_mul]
  rw [hp,fourierCoeff.sum _ _ (fun i _ =>
    integrable_finsetSum' _ (fun j _ => term_integrable _ _))]
  simp only [Finset.sum_apply]
  apply Finset.sum_congr rfl
  intro i _
  rw [fourierCoeff.sum _ _ (fun j _ => term_integrable _ _)]
  simp only [Finset.sum_apply,term_coefficient]

/-- The finite construction in `NativeSourceIdealExtremes` satisfies `extreme_orthogonality` under the displayed hypotheses. -/
private theorem extreme_orthogonality {d : ℕ} (hd : 0<d) (F : Fin (d+1) → Matrix Bool Bool ℂ)
    (hunit : ∀ t : AddCircle (2*Real.pi),sourceCompletionCircleValue F t∈Matrix.unitaryGroup Bool ℂ) :
    (F 0).conjTranspose*F (Fin.last d)=0 := by
  have hp : (fun t : AddCircle (2*Real.pi) => (sourceCompletionCircleValue F t).conjTranspose*sourceCompletionCircleValue F t)=
      (fun _ : AddCircle (2*Real.pi) => (1 : Matrix Bool Bool ℂ)) := by
    funext t
    simpa only [Matrix.star_eq_conjTranspose] using (hunit t).1
  have hn : (2*(d : ℤ))≠0 := by omega
  have hz := term_coefficient 0 (2*(d : ℤ)) (1 : Matrix Bool Bool ℂ)
  simp only [fourier_zero,one_smul,ite_eq_right hn] at hz
  have hc := gram_fourier_coefficient F (2*(d : ℤ))
  rw [hp,hz] at hc
  have hfreq (i j : Fin (d+1)) : 2*(d : ℤ)=sourceCompletionFrequency j-sourceCompletionFrequency i ↔ i=0 ∧ j=Fin.last d := by
    have hi := i.isLt
    have hj := j.isLt
    simp only [sourceCompletionFrequency,Fin.ext_iff,Fin.val_zero,Fin.val_last]
    omega
  simpa [hfreq,ite_and] using hc.symm


/-- The finite construction in `NativeSourceIdealExtremes` satisfies `determinant_zero_of_zero_product` under the displayed hypotheses. -/
private theorem determinant_zero_of_zero_product (A B : Matrix Bool Bool ℂ)
    (ha : A≠0) (hab : A*B=0) : B.det=0 := by
  by_contra hdet
  have hu : IsUnit B := (Matrix.isUnit_iff_isUnit_det B).mpr (isUnit_iff_ne_zero.mpr hdet)
  obtain ⟨u,hu⟩ := hu
  have hz := congrArg (fun M : Matrix Bool Bool ℂ => M*(↑(u⁻¹) : Matrix Bool Bool ℂ)) hab
  apply ha
  simpa [← hu,mul_assoc] using hz

/-- The finite construction in `NativeSourceIdealExtremes` satisfies `transpose_nonzero` under the displayed hypotheses. -/
private theorem transpose_nonzero {A : Matrix Bool Bool ℂ} (ha : A≠0) : A.conjTranspose≠0 := by
  intro hz
  apply ha
  simpa using congrArg Matrix.conjTranspose hz

/-- The finite construction in `NativeSourceIdealExtremes` satisfies `extreme_determinants_zero` under the displayed hypotheses. -/
private theorem extreme_determinants_zero {d : ℕ} (hd : 0<d) (F : Fin (d+1) → Matrix Bool Bool ℂ)
    (hunit : ∀ t : AddCircle (2*Real.pi),sourceCompletionCircleValue F t∈Matrix.unitaryGroup Bool ℂ)
    (hl : F 0≠0) (hr : F (Fin.last d)≠0) : (F 0).det=0 ∧ (F (Fin.last d)).det=0 := by
  have hcross := extreme_orthogonality hd F hunit
  have hcross' : (F (Fin.last d)).conjTranspose*F 0=0 := by
    simpa using congrArg Matrix.conjTranspose hcross
  exact ⟨determinant_zero_of_zero_product _ _ (transpose_nonzero hr) hcross',
    determinant_zero_of_zero_product _ _ (transpose_nonzero hl) hcross⟩

/-- The finite construction in `NativeSourceIdealExtremes` satisfies `coefficient_norm_le_one` under the displayed hypotheses. -/
private theorem coefficient_norm_le_one {d : ℕ} (F : Fin (d+1) → Matrix Bool Bool ℂ)
    (hunit : ∀ t : AddCircle (2*Real.pi),sourceCompletionCircleValue F t∈Matrix.unitaryGroup Bool ℂ)
    (j : Fin (d+1)) : ‖F j‖ ≤ 1 := by
  rw [← sourceCompletionCircleValue_coefficient F j,fourierCoeff]
  have h : ∀ᵐ t : AddCircle (2*Real.pi) ∂AddCircle.haarAddCircle,
      ‖fourier (-sourceCompletionFrequency j) t • sourceCompletionCircleValue F t‖ ≤ 1 := by
    apply ae_of_all
    intro t
    rw [norm_smul,fourier_apply,Circle.norm_coe,one_mul]
    exact Qatlib.Concepts.BlockEncoding.Encoding.unitary_norm_le_one (hunit t)
  simpa using norm_integral_le_of_norm_le_const h

end UnitaryExtremes

section IdealExtremes

open Qatlib.Concepts.MatrixAccess.MatrixBackend.RationalQsp.Data
open Qatlib.Concepts.MatrixAccess.MatrixBackend.RationalQsp.Data.SourceInput
open scoped Matrix.Norms.L2Operator
local instance : Fact (0<2*Real.pi) := ⟨Real.two_pi_pos⟩

/-- The finite construction in `NativeSourceIdealExtremes` satisfies `ideal_diagonal_im_difference` under the displayed hypotheses. -/
private theorem ideal_diagonal_im_difference (cs : List ℚ) (N : ℕ) (E : ℚ)
    (j : Fin (sourceDegree cs N E+1)) :
    (sourceIdealMatrixArray cs N E j false false).im-(sourceIdealMatrixArray cs N E j true true).im=
      2*(sourceRealArray cs N E j : ℝ) := by
  let a := sourceRealArray cs N E j
  let v := sourceIdealEArray cs N E j
  let w := star (sourceIdealEArray cs N E j.rev)
  change (Complex.I*(a : ℂ)-(v+w)/2).im-(-Complex.I*(a : ℂ)-(v+w)/2).im=2*(a : ℝ)
  simp
  ring

/-- The finite construction in `NativeSourceIdealExtremes` satisfies `real_extreme_eq` under the displayed hypotheses. -/
private theorem real_extreme_eq (cs : List ℚ) (N : ℕ) (E : ℚ)
    (j : Fin (sourceDegree cs N E+1)) (hj : j.val=0 ∨ j.val=sourceDegree cs N E) :
    sourceRealArray cs N E j=sourceRealArray cs N E (Fin.last (sourceDegree cs N E)) := by
  unfold sourceRealArray sourceP sourceLiftedArray
  congr 1
  apply Fin.ext
  change Nat.dist (2*j.val) (sourceDegree cs N E)=
    Nat.dist (2*sourceDegree cs N E) (sourceDegree cs N E)
  rcases hj with hj|hj
  · rw [hj]
    simp only [Nat.dist]
    omega
  · rw [hj]

/-- The finite construction in `NativeSourceIdealExtremes` satisfies `source_ideal_extreme_lower` under the displayed hypotheses. -/
theorem source_ideal_extreme_lower (cs : List ℚ) (N : ℕ) (E : ℚ)
    (hd : 0<sourceDegree cs N E) (j : Fin (sourceDegree cs N E+1))
    (hj : j.val=0 ∨ j.val=sourceDegree cs N E) :
    (sourceGrid N (sourceInputU cs N E) : ℝ) ≤ ‖sourceIdealMatrixArray cs N E j‖ := by
  have ha : (sourceGrid N (sourceInputU cs N E) : ℝ) ≤ |(sourceRealArray cs N E j : ℝ)| := by
    have h := source_real_last_grid_lower cs N E hd
    rw [← real_extreme_eq cs N E j hj] at h
    exact_mod_cast h
  have h0 := (Complex.abs_im_le_norm (sourceIdealMatrixArray cs N E j false false)).trans
    (sourceCompletionMatrix_entry_norm _ false false)
  have h1 := (Complex.abs_im_le_norm (sourceIdealMatrixArray cs N E j true true)).trans
    (sourceCompletionMatrix_entry_norm _ true true)
  have ht : |(sourceIdealMatrixArray cs N E j false false).im-(sourceIdealMatrixArray cs N E j true true).im| ≤
      |(sourceIdealMatrixArray cs N E j false false).im|+|(sourceIdealMatrixArray cs N E j true true).im| := by
    simpa only [sub_zero,zero_sub,abs_neg] using
      abs_sub_le (sourceIdealMatrixArray cs N E j false false).im 0 (sourceIdealMatrixArray cs N E j true true).im
  rw [ideal_diagonal_im_difference,abs_mul] at ht
  norm_num at ht
  linarith

/-- The actual finite word or frame satisfies `source_ideal_circle_unitary` with all displayed legality, input and workspace hypotheses. -/
private theorem source_ideal_circle_unitary (cs : List ℚ) (N : ℕ) (E : ℚ) (hE : 0<E)
    (htail : ∀ k,N+1 ≤ k → cs.getD k 0=0)
    (hparity : ∀ j : Fin (N+1),j.val%2≠N%2 → cs.getD j.val 0=0)
    (hd : 0<sourceDegree cs N E)
    (hnorm : ∀ x∈Set.Icc (-1 : ℝ) 1,|(nativeChebyshevPolynomialFrom 0 cs).eval x| ≤ 1)
    (t : AddCircle (2*Real.pi)) :
    sourceCompletionCircleValue (sourceIdealMatrixArray cs N E) t∈Matrix.unitaryGroup Bool ℂ := by
  obtain ⟨theta,rfl⟩ := QuotientAddGroup.mk_surjective t
  have he : sourceCompletionCircleValue (sourceIdealMatrixArray cs N E) (theta : AddCircle (2*Real.pi))=
      sourceCompletionLaurentMatrix (sourceIdealMatrixArray cs N E) theta := sourceCompletionCircleValue_real _ theta
  rw [he]
  exact sourceIdealArray_unitary cs N E hE htail hparity hd hnorm theta

/-- The finite construction in `NativeSourceIdealExtremes` satisfies `source_ideal_extreme_rank_one` under the displayed hypotheses. -/
theorem source_ideal_extreme_rank_one (cs : List ℚ) (N : ℕ) (E : ℚ) (hE : 0<E)
    (htail : ∀ k,N+1 ≤ k → cs.getD k 0=0)
    (hparity : ∀ j : Fin (N+1),j.val%2≠N%2 → cs.getD j.val 0=0)
    (hd : 0<sourceDegree cs N E)
    (hnorm : ∀ x∈Set.Icc (-1 : ℝ) 1,|(nativeChebyshevPolynomialFrom 0 cs).eval x| ≤ 1)
    (j : Fin (sourceDegree cs N E+1)) (hj : j.val=0 ∨ j.val=sourceDegree cs N E) :
    (sourceGrid N (sourceInputU cs N E) : ℝ) ≤ ‖sourceIdealMatrixArray cs N E j‖ ∧
      ((sourceIdealMatrixArray cs N E j).conjTranspose*sourceIdealMatrixArray cs N E j).trace.re=
        ‖sourceIdealMatrixArray cs N E j‖^2 := by
  have hh : (0 : ℝ)<(sourceGrid N (sourceInputU cs N E) : ℝ) := by exact_mod_cast sourceGrid_pos N (sourceInputU cs N E)
  have hl : sourceIdealMatrixArray cs N E 0≠0 :=
    norm_pos_iff.mp (hh.trans_le (source_ideal_extreme_lower cs N E hd 0 (Or.inl rfl)))
  have hr : sourceIdealMatrixArray cs N E (Fin.last (sourceDegree cs N E))≠0 :=
    norm_pos_iff.mp (hh.trans_le (source_ideal_extreme_lower cs N E hd _ (Or.inr rfl)))
  have hdet := extreme_determinants_zero hd (sourceIdealMatrixArray cs N E)
    (source_ideal_circle_unitary cs N E hE htail hparity hd hnorm) hl hr
  have hjdet : (sourceIdealMatrixArray cs N E j).det=0 := by
    rcases hj with hj|hj
    · have he : j=0 := Fin.ext hj
      simpa only [he] using hdet.1
    · have he : j=Fin.last (sourceDegree cs N E) := Fin.ext hj
      simpa only [he] using hdet.2
  exact ⟨source_ideal_extreme_lower cs N E hd j hj,sourceGram_trace_eq_norm_sq _ hjdet⟩

/-- The finite construction in `NativeSourceIdealExtremes` satisfies `source_ideal_coefficient_norm` under the displayed hypotheses. -/
theorem source_ideal_coefficient_norm (cs : List ℚ) (N : ℕ) (E : ℚ) (hE : 0<E)
    (htail : ∀ k,N+1 ≤ k → cs.getD k 0=0)
    (hparity : ∀ j : Fin (N+1),j.val%2≠N%2 → cs.getD j.val 0=0)
    (hd : 0<sourceDegree cs N E)
    (hnorm : ∀ x∈Set.Icc (-1 : ℝ) 1,|(nativeChebyshevPolynomialFrom 0 cs).eval x| ≤ 1)
    (j : Fin (sourceDegree cs N E+1)) : ‖sourceIdealMatrixArray cs N E j‖ ≤ 1 :=
  coefficient_norm_le_one _ (source_ideal_circle_unitary cs N E hE htail hparity hd hnorm) j

end IdealExtremes

section DeflationContinuation
open scoped Matrix.Norms.L2Operator

/-- The finite construction in `NativeSourceIdealExtremes` satisfies `sourceCompletionCircle_extreme_orthogonality` under the displayed hypotheses. -/
theorem sourceCompletionCircle_extreme_orthogonality {d : ℕ} (hd : 0<d)
    (F : Fin (d+1) → Matrix Bool Bool ℂ)
    (hunit : ∀ t : AddCircle (2*Real.pi),sourceCompletionCircleValue F t∈Matrix.unitaryGroup Bool ℂ) :
    (F 0).conjTranspose*F (Fin.last d)=0 := extreme_orthogonality hd F hunit

/-- The finite construction in `NativeSourceIdealExtremes` satisfies `sourceCompletionCircle_extreme_determinants_zero` under the displayed hypotheses. -/
theorem sourceCompletionCircle_extreme_determinants_zero {d : ℕ} (hd : 0<d)
    (F : Fin (d+1) → Matrix Bool Bool ℂ)
    (hunit : ∀ t : AddCircle (2*Real.pi),sourceCompletionCircleValue F t∈Matrix.unitaryGroup Bool ℂ)
    (hl : F 0≠0) (hr : F (Fin.last d)≠0) : (F 0).det=0 ∧ (F (Fin.last d)).det=0 :=
  extreme_determinants_zero hd F hunit hl hr

/-- The finite construction in `NativeSourceIdealExtremes` satisfies `sourceCompletionCircle_coefficient_norm` under the displayed hypotheses. -/
theorem sourceCompletionCircle_coefficient_norm {d : ℕ} (F : Fin (d+1) → Matrix Bool Bool ℂ)
    (hunit : ∀ t : AddCircle (2*Real.pi),sourceCompletionCircleValue F t∈Matrix.unitaryGroup Bool ℂ)
    (j : Fin (d+1)) : ‖F j‖≤1 := coefficient_norm_le_one F hunit j

/-- The actual finite word or frame satisfies `sourceIdealArray_circle_unitary` with all displayed legality, input and workspace hypotheses. -/
theorem sourceIdealArray_circle_unitary (cs : List ℚ) (N : ℕ) (E : ℚ) (hE : 0<E)
    (htail : ∀ k,N+1 ≤ k → cs.getD k 0=0)
    (hparity : ∀ j : Fin (N+1),j.val%2≠N%2 → cs.getD j.val 0=0)
    (hd : 0<sourceDegree cs N E)
    (hnorm : ∀ x∈Set.Icc (-1 : ℝ) 1,|(nativeChebyshevPolynomialFrom 0 cs).eval x| ≤ 1)
    (t : AddCircle (2*Real.pi)) :
    sourceCompletionCircleValue (sourceIdealMatrixArray cs N E) t∈Matrix.unitaryGroup Bool ℂ :=
  source_ideal_circle_unitary cs N E hE htail hparity hd hnorm t

end DeflationContinuation

end Qatlib.Concepts.MatrixAccess.MatrixBackend.RationalQsp.Data.SourceInput
