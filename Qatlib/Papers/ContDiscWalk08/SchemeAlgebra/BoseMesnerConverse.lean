/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.ContDiscWalk08.SchemeAlgebra.BoseMesnerUnitary
set_option warningAsError false

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false

noncomputable section

open Matrix Qatlib.Foundations.PureStateMath

namespace Qatlib.Papers.ContDiscWalk08.SchemeAlgebra

variable {J : Type*} [Fintype J] [DecidableEq J]

theorem sum_mul_sum {m : ℕ} (E : Fin m → Matrix J J ℂ)
    (hIdem : ∀ i, E i * E i = E i)
    (hOrth : ∀ i j, i ≠ j → E i * E j = 0)
    (a b : Fin m → ℂ) :
    (∑ i, a i • E i) * (∑ j, b j • E j) = ∑ i, (a i * b i) • E i := by
  rw [Finset.sum_mul_sum]
  simp only [Matrix.smul_mul, Matrix.mul_smul, smul_smul]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [sum_mul_orthogonal E hIdem hOrth i (fun j => b j * a i), mul_comm (b i) (a i)]

theorem conjTranspose_sum_smul {m : ℕ} (E : Fin m → Matrix J J ℂ)
    (hHerm : ∀ i, (E i).IsHermitian) (c : Fin m → ℂ) :
    (∑ i, c i • E i)ᴴ = ∑ i, (starRingEnd ℂ) (c i) • E i := by
  rw [Matrix.conjTranspose_sum]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [Matrix.conjTranspose_smul, (hHerm i).eq, RCLike.star_def]

theorem conjTranspose_mul_self_eq {m : ℕ} (E : Fin m → Matrix J J ℂ)
    (hHerm : ∀ i, (E i).IsHermitian)
    (hIdem : ∀ i, E i * E i = E i)
    (hOrth : ∀ i j, i ≠ j → E i * E j = 0)
    (c : Fin m → ℂ) :
    (∑ i, c i • E i)ᴴ * (∑ i, c i • E i)
      = ∑ i, ((starRingEnd ℂ) (c i) * c i) • E i := by
  rw [conjTranspose_sum_smul E hHerm]
  exact sum_mul_sum E hIdem hOrth _ _

theorem sum_smul_eq_zero_coeff {m : ℕ} (E : Fin m → Matrix J J ℂ)
    (hIdem : ∀ i, E i * E i = E i)
    (hOrth : ∀ i j, i ≠ j → E i * E j = 0)
    (hNonzero : ∀ i, E i ≠ 0)
    (c : Fin m → ℂ) (h : ∑ i, c i • E i = 0) (i : Fin m) : c i = 0 := by
  have hmul : (∑ j, c j • E j) * E i = 0 := by rw [h, Matrix.zero_mul]
  have hsum : (∑ j, c j • E j) * E i = ∑ j, c j • (E j * E i) := by
    rw [Finset.sum_mul]
    exact Finset.sum_congr rfl (fun j _ => Matrix.smul_mul (c j) (E j) (E i))
  have hsingle : (∑ j, c j • (E j * E i)) = c i • E i := by
    rw [Finset.sum_eq_single_of_mem i (Finset.mem_univ i)]
    · rw [hIdem i]
    · intro j _ hji
      rw [hOrth j i hji, smul_zero]
  rw [hsum, hsingle] at hmul
  rcases smul_eq_zero.mp hmul with hc | hE
  · exact hc
  · exact absurd hE (hNonzero i)

theorem coefficients_eq {m : ℕ} (E : Fin m → Matrix J J ℂ)
    (hIdem : ∀ i, E i * E i = E i)
    (hOrth : ∀ i j, i ≠ j → E i * E j = 0)
    (hNonzero : ∀ i, E i ≠ 0)
    {a b : Fin m → ℂ} (h : ∑ i, a i • E i = ∑ i, b i • E i) :
    ∀ i, a i = b i := by
  intro i
  have h0 : ∑ j, (a j - b j) • E j = 0 := by
    rw [Finset.sum_congr rfl (fun j _ => sub_smul (a j) (b j) (E j))]
    rw [Finset.sum_sub_distrib, h, sub_self]
  have := sum_smul_eq_zero_coeff E hIdem hOrth hNonzero (fun j => a j - b j) h0 i
  exact sub_eq_zero.mp this

theorem star_mul_self_eq_one_of_norm_eq_one {z : ℂ} (hz : ‖z‖ = 1) :
    (starRingEnd ℂ) z * z = 1 := by
  rw [← Complex.normSq_eq_conj_mul_self]
  have hnsq : Complex.normSq z = 1 := by
    rw [Complex.normSq_eq_norm_sq, hz]
    norm_num
  exact_mod_cast hnsq

theorem norm_eq_one_of_star_mul_self_eq_one {z : ℂ}
    (hz : (starRingEnd ℂ) z * z = 1) : ‖z‖ = 1 := by
  have hnsq : Complex.normSq z = 1 := by
    have h1 : (Complex.normSq z : ℂ) = 1 := by
      rw [Complex.normSq_eq_conj_mul_self]
      exact hz
    exact_mod_cast h1
  rw [Complex.normSq_eq_norm_sq] at hnsq
  nlinarith [norm_nonneg z]

theorem norm_coefficient_eq_one_of_unitary {m : ℕ} (E : Fin m → Matrix J J ℂ)
    (hHerm : ∀ i, (E i).IsHermitian)
    (hIdem : ∀ i, E i * E i = E i)
    (hOrth : ∀ i j, i ≠ j → E i * E j = 0)
    (hComplete : ∑ i, E i = 1)
    (hNonzero : ∀ i, E i ≠ 0)
    (c : Fin m → ℂ)
    (hU : (∑ i, c i • E i) ∈ Matrix.unitaryGroup J ℂ) (i : Fin m) :
    ‖c i‖ = 1 := by
  have h1 : star (∑ i, c i • E i) * (∑ i, c i • E i) = 1 :=
    (Matrix.mem_unitaryGroup_iff').mp hU
  rw [Matrix.star_eq_conjTranspose, conjTranspose_mul_self_eq E hHerm hIdem hOrth] at h1
  have h2 : (∑ j, ((starRingEnd ℂ) (c j) * c j) • E j) = ∑ j, (1 : ℂ) • E j := by
    rw [h1]
    rw [← hComplete]
    exact Finset.sum_congr rfl (fun j _ => by rw [one_smul])
  have hcoef := coefficients_eq E hIdem hOrth hNonzero h2 i
  exact norm_eq_one_of_star_mul_self_eq_one hcoef

theorem unitary_iff_norm_coefficient_eq_one {m : ℕ} (E : Fin m → Matrix J J ℂ)
    (hHerm : ∀ i, (E i).IsHermitian)
    (hIdem : ∀ i, E i * E i = E i)
    (hOrth : ∀ i j, i ≠ j → E i * E j = 0)
    (hComplete : ∑ i, E i = 1)
    (hNonzero : ∀ i, E i ≠ 0)
    (c : Fin m → ℂ) :
    (∑ i, c i • E i) ∈ Matrix.unitaryGroup J ℂ ↔ ∀ i, ‖c i‖ = 1 := by
  constructor
  · exact norm_coefficient_eq_one_of_unitary E hHerm hIdem hOrth hComplete hNonzero c
  · intro hc
    rw [Matrix.mem_unitaryGroup_iff', Matrix.star_eq_conjTranspose,
      conjTranspose_mul_self_eq E hHerm hIdem hOrth]
    have hcoef : ∀ i, (starRingEnd ℂ) (c i) * c i = (1 : ℂ) :=
      fun i => star_mul_self_eq_one_of_norm_eq_one (hc i)
    rw [Finset.sum_congr rfl (fun i _ => by rw [hcoef i])]
    simpa using hComplete

theorem exists_phase_of_unitary {m : ℕ} (E : Fin m → Matrix J J ℂ)
    (hHerm : ∀ i, (E i).IsHermitian)
    (hIdem : ∀ i, E i * E i = E i)
    (hOrth : ∀ i j, i ≠ j → E i * E j = 0)
    (hComplete : ∑ i, E i = 1)
    (hNonzero : ∀ i, E i ≠ 0)
    (c : Fin m → ℂ)
    (hU : (∑ i, c i • E i) ∈ Matrix.unitaryGroup J ℂ) :
    ∃ φ : Fin m → ℝ, ∀ i, c i = phase (φ i) := by
  classical
  have hnorm : ∀ i, ‖c i‖ = 1 :=
    norm_coefficient_eq_one_of_unitary E hHerm hIdem hOrth hComplete hNonzero c hU
  choose φ hφ using fun i =>
    (Complex.norm_eq_one_iff (c i)).mp (hnorm i)
  refine ⟨φ, fun i => ?_⟩
  have h := hφ i

  rw [phase]
  rw [mul_comm ((φ i : ℂ)) Complex.I] at h
  exact h.symm

theorem norm_phase (φ : ℝ) : ‖phase φ‖ = 1 := by
  unfold phase
  rw [Complex.norm_exp]
  have hre : (Complex.I * (φ : ℂ)).re = 0 := by simp
  rw [hre, Real.exp_zero]

theorem norm_sum_phase_mul_le {m : ℕ} (a : Fin m → ℂ) (φ : Fin m → ℝ) :
    ‖∑ i, phase (φ i) * a i‖ ≤ ∑ i, ‖a i‖ := by
  refine (norm_sum_le _ _).trans (le_of_eq ?_)
  exact Finset.sum_congr rfl (fun i _ => by
    rw [norm_mul, norm_phase, one_mul])

end Qatlib.Papers.ContDiscWalk08.SchemeAlgebra
