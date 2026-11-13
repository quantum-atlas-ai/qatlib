/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.ContDiscWalk08.MainResults.WalkSpectrum.WalkDefs

/-!
# Phase unitaries from orthogonal idempotents

The function `schemeUnitary` forms a phase-weighted sum of matrices. When the matrices are
mutually orthogonal Hermitian idempotents summing to the identity, this sum is unitary, as in
the association-scheme construction of [Childs2010].

## Main statements

* `schemeUnitary_conjTranspose_mul`: the adjoint product is the identity.
* `schemeUnitary_mem_unitaryGroup`: the phase sum belongs to the unitary group.

## References

* [Childs, 2010][Childs2010]
-/

set_option autoImplicit false

noncomputable section

open Matrix Qatlib.Foundations.PureStateMath

namespace Qatlib.Papers.ContDiscWalk08.SchemeAlgebra

variable {J : Type*} [Fintype J] [DecidableEq J]

/-- Defines the complex phase `exp(i * φ)`. -/
def phase (φ : ℝ) : ℂ := Complex.exp (Complex.I * (φ : ℂ))

/-- The conjugate of `phase φ` multiplied by `phase φ` equals one. -/
theorem phase_unit (φ : ℝ) : (starRingEnd ℂ) (phase φ) * phase φ = 1 := by
  unfold phase
  rw [← Complex.normSq_eq_conj_mul_self, Complex.normSq_eq_norm_sq]
  have hre : (Complex.I * (φ : ℂ)).re = 0 := by simp
  have h : ‖Complex.exp (Complex.I * (φ : ℂ))‖ = 1 := by
    rw [Complex.norm_exp, hre, Real.exp_zero]
  rw [h]
  norm_num

/-- Defines the matrix sum of `E i` weighted by the complex phases `phase (φ i)`. -/
def schemeUnitary {m : ℕ} (E : Fin m → Matrix J J ℂ) (φ : Fin m → ℝ) : Matrix J J ℂ :=
  ∑ i, phase (φ i) • E i

omit [Fintype J] [DecidableEq J] in

/-- For Hermitian `E i`, the conjugate transpose of `schemeUnitary E φ` is the sum with
conjugated phase coefficients. -/
theorem conjTranspose_schemeUnitary {m : ℕ} (E : Fin m → Matrix J J ℂ)
    (hHerm : ∀ i, (E i).IsHermitian) (φ : Fin m → ℝ) :
    (schemeUnitary E φ)ᴴ = ∑ i, (starRingEnd ℂ) (phase (φ i)) • E i := by
  unfold schemeUnitary
  rw [Matrix.conjTranspose_sum]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [Matrix.conjTranspose_smul, (hHerm i).eq]
  rfl

omit [DecidableEq J] in

/-- Multiplying a fixed idempotent by a weighted sum of mutually orthogonal idempotents retains
only its own weighted term. -/
theorem sum_mul_orthogonal {m : ℕ} (E : Fin m → Matrix J J ℂ)
    (hIdem : ∀ i, E i * E i = E i)
    (hOrth : ∀ i j, i ≠ j → E i * E j = 0)
    (i : Fin m) (g : Fin m → ℂ) :
    (∑ j, g j • (E i * E j)) = g i • E i := by
  rw [Finset.sum_eq_single_of_mem i (Finset.mem_univ i)]
  · rw [hIdem i]
  · intro j _ hji
    simp [hOrth i j hji.symm]

/-- For a complete family of mutually orthogonal Hermitian idempotents, the conjugate transpose
of `schemeUnitary E φ` times itself equals the identity. See the association-scheme
construction in [Childs2010]. -/
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

/-- For a complete family of mutually orthogonal Hermitian idempotents, `schemeUnitary E φ`
times its conjugate transpose equals the identity. -/
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

/-- A phase-weighted complete family of mutually orthogonal Hermitian idempotents gives a
unitary matrix. See [Childs2010]. -/
theorem schemeUnitary_mem_unitaryGroup {m : ℕ} (E : Fin m → Matrix J J ℂ)
    (hHerm : ∀ i, (E i).IsHermitian)
    (hIdem : ∀ i, E i * E i = E i)
    (hOrth : ∀ i j, i ≠ j → E i * E j = 0)
    (hComplete : ∑ i, E i = 1)
    (φ : Fin m → ℝ) :
    schemeUnitary E φ ∈ Matrix.unitaryGroup J ℂ := by
  rw [Matrix.mem_unitaryGroup_iff', Matrix.star_eq_conjTranspose]
  exact schemeUnitary_conjTranspose_mul E hHerm hIdem hOrth hComplete φ

omit [Fintype J] in

/-- Restates the supplied completeness identity that the idempotents sum to the identity. -/
theorem complete_resolution {m : ℕ} (E : Fin m → Matrix J J ℂ)
    (hComplete : ∑ i, E i = 1) : ∑ i, E i = 1 := hComplete

end Qatlib.Papers.ContDiscWalk08.SchemeAlgebra
