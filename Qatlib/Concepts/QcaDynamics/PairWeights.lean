/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.LinearAlgebra.UnitaryGroup
import Mathlib.Analysis.Complex.Norm
import Mathlib.Data.Complex.Basic

set_option autoImplicit false
noncomputable section

open Complex

namespace Qatlib.Concepts.QcaDynamics.PairWeights

def Eq6 (a b c d e f : ℂ) : Prop :=
  a * star a + b * star b + c * star c = 1 ∧
  d * star d + e * star e + f * star f = 1 ∧
  b * star d + c * star e = 0 ∧
  e * star a + f * star b = 0 ∧
  c * star a = 0 ∧
  f * star d = 0

def blockS1 (e f a b : ℂ) : Matrix (Fin 2) (Fin 2) ℂ :=
  !![e, f; a, b]

def blockS2 (b c d e : ℂ) : Matrix (Fin 2) (Fin 2) ℂ :=
  !![b, c; d, e]

lemma norm_eq_one_of_mul_star {z : ℂ} (h : z * star z = 1) : ‖z‖ = 1 := by
  have hns : (Complex.normSq z : ℂ) = 1 := by
    rw [← Complex.mul_conj]
    exact h
  have hns' : Complex.normSq z = 1 := Complex.ofReal_inj.mp hns
  have hsq : ‖z‖ ^ 2 = 1 := by
    rw [← Complex.normSq_eq_norm_sq, hns']
  nlinarith [norm_nonneg z]

lemma blockS1_mem_unitaryGroup (e f a b : ℂ)
    (h1 : e * star e + f * star f = 1)
    (h2 : a * star a + b * star b = 1)
    (h3 : e * star a + f * star b = 0) :
    blockS1 e f a b ∈ Matrix.unitaryGroup (Fin 2) ℂ := by
  have h3' : a * star e + b * star f = 0 := by
    have h := congrArg star h3
    rw [star_add, star_mul, star_mul, star_star, star_star, star_zero] at h
    exact h
  rw [Matrix.mem_unitaryGroup_iff]
  ext i j
  rw [Matrix.mul_apply]
  fin_cases i <;> fin_cases j
  · simpa [blockS1, Fin.sum_univ_two] using h1
  · simpa [blockS1, Fin.sum_univ_two, Matrix.star_apply] using h3
  · simpa [blockS1, Fin.sum_univ_two, Matrix.star_apply] using h3'
  · simpa [blockS1, Fin.sum_univ_two, Matrix.star_apply] using h2

lemma blockS2_mem_unitaryGroup (b c d e : ℂ)
    (h1 : b * star b + c * star c = 1)
    (h2 : d * star d + e * star e = 1)
    (h3 : b * star d + c * star e = 0) :
    blockS2 b c d e ∈ Matrix.unitaryGroup (Fin 2) ℂ := by
  have h3' : d * star b + e * star c = 0 := by
    have h := congrArg star h3
    rw [star_add, star_mul, star_mul, star_star, star_star, star_zero] at h
    exact h
  rw [Matrix.mem_unitaryGroup_iff]
  ext i j
  rw [Matrix.mul_apply]
  fin_cases i <;> fin_cases j
  · simpa [blockS2, Fin.sum_univ_two] using h1
  · simpa [blockS2, Fin.sum_univ_two, Matrix.star_apply] using h3
  · simpa [blockS2, Fin.sum_univ_two, Matrix.star_apply] using h3'
  · simpa [blockS2, Fin.sum_univ_two, Matrix.star_apply] using h2

end Qatlib.Concepts.QcaDynamics.PairWeights
