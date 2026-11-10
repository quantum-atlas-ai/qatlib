/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Foundations.PureStateMath.MixedState
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Ring
open Qatlib.Foundations.PureStateMath
open Qatlib

set_option autoImplicit false
namespace Qatlib.Concepts.ShadowModels.ShadowChannel
open Matrix
open scoped Classical BigOperators ComplexOrder

noncomputable def designProbePure : Operator 2 := Matrix.diagonal ![1, 0]

theorem designProbePure_isPure : IsPureDensityOperator designProbePure := by
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · apply Matrix.PosSemidef.diagonal
    intro i
    fin_cases i <;> norm_num
  · norm_num [designProbePure, Matrix.trace, Fin.sum_univ_two]
  · ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [designProbePure, Matrix.mul_apply, Matrix.diagonal, Fin.sum_univ_two]

theorem imaginary_identity_overlap_zero (U : Operator 2) :
    (Matrix.trace ((Complex.I • (1 : Operator 2)) * Uᴴ * designProbePure * U)).re = 0 := by
  have hq := designProbePure_isPure.1.1.conjTranspose_mul_mul_same U
  have hi : (Matrix.trace (Uᴴ * designProbePure * U)).im = 0 :=
    (RCLike.nonneg_iff.mp hq.trace_nonneg).2
  simp only [Matrix.smul_mul, Matrix.trace_smul, smul_eq_mul,
    Complex.mul_re, Complex.I_re, Complex.I_im, zero_mul, one_mul, hi, sub_zero]

theorem qubit_real_second_moment_impossible {J : Type} [Fintype J]
    (prob : J → ℝ) (Uf : J → Operator 2) :
    ¬ (∀ Pp : Operator 2, IsPureDensityOperator Pp → ∀ A B : Operator 2,
      (∑ j, prob j * (Matrix.trace (A * (Uf j)ᴴ * Pp * Uf j)).re *
        (Matrix.trace (B * (Uf j)ᴴ * Pp * Uf j)).re) =
      ((Matrix.trace A).re * (Matrix.trace B).re + (Matrix.trace (A * B)).re) / 6) := by
  intro h
  have he := h designProbePure designProbePure_isPure
    (Complex.I • (1 : Operator 2)) (Complex.I • (1 : Operator 2))
  simp only [imaginary_identity_overlap_zero, mul_zero, Finset.sum_const_zero] at he
  norm_num [Matrix.trace, Matrix.mul_apply, Matrix.smul_apply, Matrix.one_apply,
    Fin.sum_univ_two] at he

end Qatlib.Concepts.ShadowModels.ShadowChannel

namespace Qatlib.Concepts.ShadowModels.ShadowChannel
open Matrix
open scoped Classical BigOperators

theorem not_qubit_conjugation_two_design_contract :
    ¬ (∃ f : Fin 24 → Operator 2,
      (∀ i, f i ∈ Matrix.unitaryGroup (Fin 2) ℂ) ∧
      (∀ Pp : Operator 2, IsPureDensityOperator Pp → ∀ A : Operator 2,
        (∑ i, (Matrix.trace (A * (f i)ᴴ * Pp * f i)).re) / 24 =
          (Matrix.trace A).re / 2) ∧
      (∀ Pp : Operator 2, IsPureDensityOperator Pp → ∀ A B : Operator 2,
        (∑ i, (Matrix.trace (A * (f i)ᴴ * Pp * f i)).re *
            (Matrix.trace (B * (f i)ᴴ * Pp * f i)).re) / 24 =
          ((Matrix.trace A).re * (Matrix.trace B).re +
            (Matrix.trace (A * B)).re) / 6)) := by
  rintro ⟨f, _, _, h⟩
  have he := h designProbePure designProbePure_isPure
    (Complex.I • (1 : Operator 2)) (Complex.I • (1 : Operator 2))
  simp only [imaginary_identity_overlap_zero, mul_zero, Finset.sum_const_zero] at he
  norm_num [Matrix.trace, Matrix.mul_apply, Matrix.smul_apply, Matrix.one_apply,
    Fin.sum_univ_two] at he

end Qatlib.Concepts.ShadowModels.ShadowChannel

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000
namespace Qatlib.Concepts.ShadowModels.ShadowChannel
open Matrix
open scoped Classical BigOperators ComplexOrder

noncomputable def qubitConjugationRaw : Fin 24 → Operator 2 := ![
!![1, 0; 0, 1],
!![0, 1; 1, 0],
!![0, -Complex.I; Complex.I, 0],
!![1, 0; 0, -1],
!![1, 0; 0, Complex.I],
!![0, Complex.I; 1, 0],
!![0, 1; Complex.I, 0],
!![1, 0; 0, -Complex.I],
!![1, 1; 1, -1],
!![1, -1; 1, 1],
!![-Complex.I, Complex.I; Complex.I, Complex.I],
!![1, 1; -1, 1],
!![1, 1; Complex.I, -Complex.I],
!![Complex.I, -Complex.I; 1, 1],
!![1, -1; Complex.I, Complex.I],
!![1, 1; -Complex.I, Complex.I],
!![1, Complex.I; 1, -Complex.I],
!![1, -Complex.I; 1, Complex.I],
!![-Complex.I, -1; Complex.I, -1],
!![1, Complex.I; -1, Complex.I],
!![1, Complex.I; Complex.I, 1],
!![Complex.I, 1; 1, Complex.I],
!![1, -Complex.I; Complex.I, -1],
!![1, Complex.I; -Complex.I, -1]]

noncomputable def qubitConjugationScale (i : Fin 24) : ℝ :=
  if i.val < 8 then 1 else 1 / Real.sqrt 2
noncomputable def qubitConjugationWeight (i : Fin 24) : ℂ :=
  if i.val < 8 then 1 else 1 / 2

noncomputable def qubitConjugationFamily (i : Fin 24) : Operator 2 :=
  (qubitConjugationScale i : ℂ) • qubitConjugationRaw i

private lemma qubitConjugationScale_sq (i : Fin 24) : (qubitConjugationScale i : ℂ)^2 = qubitConjugationWeight i := by
  have hs : (Real.sqrt 2)^2 = 2 := Real.sq_sqrt (by norm_num)
  have hz : Real.sqrt 2 ≠ 0 := by positivity
  unfold qubitConjugationScale qubitConjugationWeight
  split_ifs
  · norm_num
  · have hr : (1 / Real.sqrt 2)^2 = (1/2 : ℝ) := by
      rw [div_pow, hs]
      norm_num
    simpa only [Complex.ofReal_pow, Complex.ofReal_div, Complex.ofReal_one,
        Complex.ofReal_ofNat] using congrArg Complex.ofReal hr

private lemma design_star_real (r : ℝ) : star (r : ℂ) = (r : ℂ) := Complex.conj_ofReal r

private lemma qubit_conjugation_overlap (i : Fin 24) (P A : Operator 2) :
    Matrix.trace (A * (qubitConjugationFamily i)ᴴ * P * qubitConjugationFamily i) =
    qubitConjugationWeight i * Matrix.trace (A * (qubitConjugationRaw i)ᴴ * P * qubitConjugationRaw i) := by
  simp only [qubitConjugationFamily, Matrix.conjTranspose_smul, design_star_real, Matrix.mul_smul, Matrix.smul_mul,
    Matrix.trace_smul, smul_eq_mul]
  rw [show (qubitConjugationScale i : ℂ) * ((qubitConjugationScale i : ℂ) *
      Matrix.trace (A * (qubitConjugationRaw i)ᴴ * P * qubitConjugationRaw i)) =
      (qubitConjugationScale i : ℂ)^2 * Matrix.trace (A * (qubitConjugationRaw i)ᴴ * P * qubitConjugationRaw i) by ring,
    qubitConjugationScale_sq]

lemma qubit_conjugation_unitary (i : Fin 24) : qubitConjugationFamily i ∈ Matrix.unitaryGroup (Fin 2) ℂ := by
  rw [Matrix.mem_unitaryGroup_iff, Matrix.star_eq_conjTranspose]
  simp only [qubitConjugationFamily, Matrix.conjTranspose_smul, design_star_real, Matrix.mul_smul, Matrix.smul_mul,
    smul_smul, ← pow_two, qubitConjugationScale_sq]
  fin_cases i <;> ext a b <;> fin_cases a <;> fin_cases b <;>
    norm_num [qubitConjugationRaw, qubitConjugationWeight, Matrix.mul_apply, Fin.sum_univ_two,
      Matrix.conjTranspose_apply, Matrix.smul_apply, Matrix.one_apply, Matrix.vecMul, dotProduct]

private lemma qubit_conjugation_first_complex (P A : Operator 2) :
    (∑ i, Matrix.trace (A * (qubitConjugationFamily i)ᴴ * P * qubitConjugationFamily i)) =
      12 * Matrix.trace A * Matrix.trace P := by
  simp_rw [qubit_conjugation_overlap]
  simp [Fin.sum_univ_succ, qubitConjugationRaw, qubitConjugationWeight, Matrix.trace_fin_two,
    Matrix.mul_apply, Matrix.conjTranspose_apply]
  ring_nf
  simp [Complex.I_sq]
  ring

private lemma qubit_conjugation_second_complex_raw (P A B : Operator 2) :
    (∑ i, Matrix.trace (A * (qubitConjugationFamily i)ᴴ * P * qubitConjugationFamily i) *
      Matrix.trace (B * (qubitConjugationFamily i)ᴴ * P * qubitConjugationFamily i)) =
    8 * Matrix.trace A * Matrix.trace B * (Matrix.trace P)^2 -
      4 * Matrix.trace (A * B) * (Matrix.trace P)^2 +
      8 * Matrix.trace (A * B) * Matrix.trace (P * P) -
      4 * Matrix.trace A * Matrix.trace B * Matrix.trace (P * P) := by
  simp_rw [qubit_conjugation_overlap]
  simp [Fin.sum_univ_succ, qubitConjugationRaw, qubitConjugationWeight, Matrix.trace_fin_two,
    Matrix.mul_apply, Matrix.conjTranspose_apply]
  ring_nf
  simp [Complex.I_sq]
  ring

private lemma design_hermitian_trace_im (A : Operator 2) (hA : A.IsHermitian) :
    (Matrix.trace A).im = 0 := by
  have hh : star (Matrix.trace A) = Matrix.trace A := by
    rw [← Matrix.trace_conjTranspose, hA.eq]
  have hi := congrArg Complex.im hh
  change -(Matrix.trace A).im = (Matrix.trace A).im at hi
  linarith

private lemma design_hermitian_pair_im (A B : Operator 2)
    (hA : A.IsHermitian) (hB : B.IsHermitian) :
    (Matrix.trace (A * B)).im = 0 := by
  have hh : star (Matrix.trace (A * B)) = Matrix.trace (A * B) := by
    rw [← Matrix.trace_conjTranspose, Matrix.conjTranspose_mul, hA.eq, hB.eq,
      Matrix.trace_mul_comm]
  have hi := congrArg Complex.im hh
  change -(Matrix.trace (A * B)).im = (Matrix.trace (A * B)).im at hi
  linarith

theorem qubit_conjugation_two_design_exists :
    ∃ f : Fin 24 → Operator 2,
      (∀ i, f i ∈ Matrix.unitaryGroup (Fin 2) ℂ) ∧
      (∀ Pp : Operator 2, IsPureDensityOperator Pp → ∀ A : Operator 2,
        (∑ i, (Matrix.trace (A * (f i)ᴴ * Pp * f i)).re) / 24 =
          (Matrix.trace A).re / 2) ∧
      (∀ Pp : Operator 2, IsPureDensityOperator Pp → ∀ A B : Operator 2,
        A.IsHermitian → B.IsHermitian →
        (∑ i, (Matrix.trace (A * (f i)ᴴ * Pp * f i)).re *
            (Matrix.trace (B * (f i)ᴴ * Pp * f i)).re) / 24 =
          ((Matrix.trace A).re * (Matrix.trace B).re +
            (Matrix.trace (A * B)).re) / 6) := by
  refine ⟨qubitConjugationFamily, qubit_conjugation_unitary, ?_, ?_⟩
  · intro P hP A
    have h := qubit_conjugation_first_complex P A
    rw [hP.1.2, mul_one] at h
    have hr := congrArg Complex.re h
    simp only [Complex.re_sum, Complex.mul_re] at hr
    norm_num at hr
    linarith
  · intro P hP A B hA hB
    have h := qubit_conjugation_second_complex_raw P A B
    rw [hP.2, hP.1.2] at h
    have him : ∀ i, (Matrix.trace (A * (qubitConjugationFamily i)ᴴ * P * qubitConjugationFamily i)).im = 0 := by
      intro i
      have hq := (hP.1.1.conjTranspose_mul_mul_same (qubitConjugationFamily i)).isHermitian
      simpa only [Matrix.mul_assoc] using design_hermitian_pair_im A _ hA hq
    have hr := congrArg Complex.re h
    simp only [Complex.re_sum, Complex.mul_re, Complex.sub_re, him,
      design_hermitian_trace_im A hA] at hr
    norm_num at hr
    rw [design_hermitian_trace_im A hA] at hr
    norm_num at hr
    linarith
end Qatlib.Concepts.ShadowModels.ShadowChannel
