/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.ContDiscWalk08.MainResults.WalkSpectrum.WalkDefs
set_option warningAsError false

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false

noncomputable section

open Matrix Qatlib.Foundations.PureStateMath

namespace Qatlib.Papers.ContDiscWalk08.SchemeAlgebra

variable {J : Type*} [Fintype J] [DecidableEq J]

def phase (φ : ℝ) : ℂ := Complex.exp (Complex.I * (φ : ℂ))

theorem phase_unit (φ : ℝ) : (starRingEnd ℂ) (phase φ) * phase φ = 1 := by
  unfold phase
  rw [← Complex.normSq_eq_conj_mul_self, Complex.normSq_eq_norm_sq]
  have hre : (Complex.I * (φ : ℂ)).re = 0 := by simp
  have h : ‖Complex.exp (Complex.I * (φ : ℂ))‖ = 1 := by
    rw [Complex.norm_exp, hre, Real.exp_zero]
  rw [h]
  norm_num

def schemeUnitary {m : ℕ} (E : Fin m → Matrix J J ℂ) (φ : Fin m → ℝ) : Matrix J J ℂ :=
  ∑ i, phase (φ i) • E i

theorem conjTranspose_schemeUnitary {m : ℕ} (E : Fin m → Matrix J J ℂ)
    (hHerm : ∀ i, (E i).IsHermitian) (φ : Fin m → ℝ) :
    (schemeUnitary E φ)ᴴ = ∑ i, (starRingEnd ℂ) (phase (φ i)) • E i := by
  unfold schemeUnitary
  rw [Matrix.conjTranspose_sum]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [Matrix.conjTranspose_smul, (hHerm i).eq]
  rfl

theorem sum_mul_orthogonal {m : ℕ} (E : Fin m → Matrix J J ℂ)
    (hIdem : ∀ i, E i * E i = E i)
    (hOrth : ∀ i j, i ≠ j → E i * E j = 0)
    (i : Fin m) (g : Fin m → ℂ) :
    (∑ j, g j • (E i * E j)) = g i • E i := by
  rw [Finset.sum_eq_single_of_mem i (Finset.mem_univ i)]
  · rw [hIdem i]
  · intro j _ hji
    simp [hOrth i j hji.symm]

theorem schemeUnitary_conjTranspose_mul {m : ℕ} (E : Fin m → Matrix J J ℂ)
    (hHerm : ∀ i, (E i).IsHermitian)
    (hIdem : ∀ i, E i * E i = E i)
    (hOrth : ∀ i j, i ≠ j → E i * E j = 0)
    (hComplete : ∑ i, E i = 1)
    (φ : Fin m → ℝ) :
    (schemeUnitary E φ)ᴴ * schemeUnitary E φ = 1 := by
  rw [conjTranspose_schemeUnitary E hHerm φ]
  unfold schemeUnitary
  rw [Finset.sum_mul_sum]
  simp only [Matrix.smul_mul, Matrix.mul_smul, smul_smul]
  have hstep : ∀ i : Fin m,
      (∑ j, (phase (φ j) * (starRingEnd ℂ) (phase (φ i))) • (E i * E j))
        = (phase (φ i) * (starRingEnd ℂ) (phase (φ i))) • E i :=
    fun i => sum_mul_orthogonal E hIdem hOrth i
      (fun j => phase (φ j) * (starRingEnd ℂ) (phase (φ i)))
  rw [Finset.sum_congr rfl (fun i _ => hstep i)]
  have hcomm : ∀ i, phase (φ i) * (starRingEnd ℂ) (phase (φ i)) = (1 : ℂ) := by
    intro i
    rw [mul_comm]
    exact phase_unit (φ i)
  simp only [hcomm, one_smul]
  exact hComplete

theorem schemeUnitary_mul_conjTranspose {m : ℕ} (E : Fin m → Matrix J J ℂ)
    (hHerm : ∀ i, (E i).IsHermitian)
    (hIdem : ∀ i, E i * E i = E i)
    (hOrth : ∀ i j, i ≠ j → E i * E j = 0)
    (hComplete : ∑ i, E i = 1)
    (φ : Fin m → ℝ) :
    schemeUnitary E φ * (schemeUnitary E φ)ᴴ = 1 := by
  rw [conjTranspose_schemeUnitary E hHerm φ]
  unfold schemeUnitary
  rw [Finset.sum_mul_sum]
  simp only [Matrix.smul_mul, Matrix.mul_smul, smul_smul]
  have hstep : ∀ i : Fin m,
      (∑ j, ((starRingEnd ℂ) (phase (φ j)) * phase (φ i)) • (E i * E j))
        = ((starRingEnd ℂ) (phase (φ i)) * phase (φ i)) • E i :=
    fun i => sum_mul_orthogonal E hIdem hOrth i
      (fun j => (starRingEnd ℂ) (phase (φ j)) * phase (φ i))
  rw [Finset.sum_congr rfl (fun i _ => hstep i)]
  simp only [phase_unit, one_smul]
  exact hComplete

theorem schemeUnitary_mem_unitaryGroup {m : ℕ} (E : Fin m → Matrix J J ℂ)
    (hHerm : ∀ i, (E i).IsHermitian)
    (hIdem : ∀ i, E i * E i = E i)
    (hOrth : ∀ i j, i ≠ j → E i * E j = 0)
    (hComplete : ∑ i, E i = 1)
    (φ : Fin m → ℝ) :
    schemeUnitary E φ ∈ Matrix.unitaryGroup J ℂ := by
  rw [Matrix.mem_unitaryGroup_iff', Matrix.star_eq_conjTranspose]
  exact schemeUnitary_conjTranspose_mul E hHerm hIdem hOrth hComplete φ

theorem complete_resolution {m : ℕ} (E : Fin m → Matrix J J ℂ)
    (hComplete : ∑ i, E i = 1) : ∑ i, E i = 1 := hComplete

end Qatlib.Papers.ContDiscWalk08.SchemeAlgebra
