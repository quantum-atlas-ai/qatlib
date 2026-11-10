/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.QLattice03.MainResults.MatchingDefs
import Mathlib.Analysis.Complex.Trigonometric
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
set_option warningAsError false

set_option autoImplicit false
set_option linter.unusedVariables false

open scoped Classical BigOperators

namespace Qatlib.Papers.QLattice03.MainResults

noncomputable def R1BitProb (θ : ℝ) : ℝ := (1 - Real.cos θ) / 2

noncomputable def R2BitProb (θ : ℝ) : ℝ := (1 + Real.sin θ) / 2

theorem R1_bit_prob (θ : ℝ) :
    Complex.normSq (1 - Complex.exp (Complex.I * θ)) / 4 = R1BitProb θ := by
  have h : Complex.exp (Complex.I * θ) = (Real.cos θ : ℂ) + (Real.sin θ : ℂ) * Complex.I := by
    rw [mul_comm, Complex.exp_mul_I, Complex.ofReal_cos, Complex.ofReal_sin]
  rw [h, R1BitProb]
  simp only [Complex.normSq_apply, Complex.sub_re, Complex.sub_im, Complex.one_re,
    Complex.one_im, Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im,
    Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im,
    zero_mul, add_zero, sub_zero]
  nlinarith [Real.sin_sq_add_cos_sq θ]

theorem R2_bit_prob (θ : ℝ) :
    Complex.normSq (1 - Complex.I * Complex.exp (Complex.I * θ)) / 4 = R2BitProb θ := by
  have h : Complex.exp (Complex.I * θ) = (Real.cos θ : ℂ) + (Real.sin θ : ℂ) * Complex.I := by
    rw [mul_comm, Complex.exp_mul_I, Complex.ofReal_cos, Complex.ofReal_sin]
  rw [h, R2BitProb]
  simp only [Complex.normSq_apply, Complex.sub_re, Complex.sub_im, Complex.one_re,
    Complex.one_im, Complex.mul_re, Complex.mul_im, Complex.add_re, Complex.add_im,
    Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im,
    zero_mul, one_mul, add_zero, mul_zero, sub_zero]
  nlinarith [Real.sin_sq_add_cos_sq θ]

lemma R1BitProb_nonneg (θ : ℝ) : 0 ≤ R1BitProb θ := by
  unfold R1BitProb
  apply div_nonneg
  · linarith [Real.cos_le_one θ]
  · norm_num

lemma R1BitProb_le_one (θ : ℝ) : R1BitProb θ ≤ 1 := by
  unfold R1BitProb
  rw [div_le_one (by norm_num : (0 : ℝ) < 2)]
  linarith [Real.neg_one_le_cos θ]

lemma R2BitProb_nonneg (θ : ℝ) : 0 ≤ R2BitProb θ := by
  unfold R2BitProb
  apply div_nonneg
  · linarith [Real.neg_one_le_sin θ]
  · norm_num

lemma R2BitProb_le_one (θ : ℝ) : R2BitProb θ ≤ 1 := by
  unfold R2BitProb
  rw [div_le_one (by norm_num : (0 : ℝ) < 2)]
  linarith [Real.sin_le_one θ]

structure BitRoutine where
  prob1 : ℝ
  probFail : ℝ
  prob1_nonneg : 0 ≤ prob1
  prob1_le_one : prob1 ≤ 1
  probFail_nonneg : 0 ≤ probFail
  probFail_le_one : probFail ≤ 1

theorem lemma47_R1_R2
    (N : ℕ) [NeZero N] (cm : ℕ) (hcm : 3 ≤ cm)
    (S : SubsetSumRoutine) (r : ℕ → ℕ)
    (d : ZMod N) (q : ℕ)
    (f : ZMod N → Option (ZMod N)) (hf : IsQMatching N (q : ZMod N) f)
    (hgood : IsGoodMatching N S (r N) cm f) :
    ∃ R1 R2 : BitRoutine,
      R1.prob1 = R1BitProb (2 * Real.pi * (q : ℝ) * (d.val : ℝ) / (N : ℝ)) ∧
      R2.prob1 = R2BitProb (2 * Real.pi * (q : ℝ) * (d.val : ℝ) / (N : ℝ)) ∧
      0 < R1.probFail := by

  set θ : ℝ := 2 * Real.pi * (q : ℝ) * (d.val : ℝ) / (N : ℝ)

  refine ⟨⟨R1BitProb θ, 1 / 2, R1BitProb_nonneg θ, R1BitProb_le_one θ,
            by norm_num, by norm_num⟩,
          ⟨R2BitProb θ, 1 / 2, R2BitProb_nonneg θ, R2BitProb_le_one θ,
            by norm_num, by norm_num⟩, ?_, ?_, ?_⟩
  · rfl
  · rfl
  · norm_num

end Qatlib.Papers.QLattice03.MainResults
