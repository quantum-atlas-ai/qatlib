/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Data.Matrix.Basis
import Mathlib.Data.Matrix.Mul
import Mathlib.Data.Fin.SuccPred
import Mathlib.Data.Complex.Basic
import Mathlib.Tactic

set_option autoImplicit false

namespace Qatlib.Papers.DiracSearch04.MainResults

open Matrix

noncomputable def alpha (d : ℕ) (j : Fin d) : Matrix (Fin (d+1)) (Fin (d+1)) ℂ :=
  Matrix.single (0 : Fin (d+1)) (Fin.succ j) 1 +
    Matrix.single (Fin.succ j) (0 : Fin (d+1)) 1

noncomputable def beta (d : ℕ) : Matrix (Fin (d+1)) (Fin (d+1)) ℂ :=
  (2 : ℂ) • Matrix.single (0 : Fin (d+1)) (0 : Fin (d+1)) 1 - 1

noncomputable def eta (d : ℕ) : Fin (d+1) → ℂ :=
  Pi.single (0 : Fin (d+1)) (1 : ℂ)

noncomputable def unitVec (d : ℕ) (i : Fin (d+1)) : Fin (d+1) → ℂ :=
  Pi.single i (1 : ℂ)

theorem update_zero_eq_single {n : ℕ} (i : Fin n) (c : ℂ) :
    Function.update (0 : Fin n → ℂ) i c = Pi.single (M := fun _ => ℂ) i c := by
  funext a
  by_cases h : a = i
  · subst h; rw [Function.update_self, Pi.single_eq_same]
  · rw [Function.update_of_ne h c (0 : Fin n → ℂ)]
    exact (Pi.single_eq_of_ne (M := fun _ => ℂ) h c).symm

@[simp] theorem eta_zero (d : ℕ) : eta d (0 : Fin (d+1)) = 1 := by
  unfold eta; exact Pi.single_eq_same _ _

theorem eta_succ (d : ℕ) (j : Fin d) : eta d (Fin.succ j) = 0 := by
  unfold eta; exact Pi.single_eq_of_ne (Fin.succ_ne_zero j) 1

@[simp] theorem unitVec_self (d : ℕ) (i : Fin (d+1)) : unitVec d i i = 1 := by
  unfold unitVec; exact Pi.single_eq_same _ _

theorem unitVec_succ_zero (d : ℕ) (k : Fin d) :
    unitVec d (Fin.succ k) (0 : Fin (d+1)) = 0 := by
  unfold unitVec; exact Pi.single_eq_of_ne (Fin.succ_ne_zero k).symm 1

theorem unitVec_succ_succ (d : ℕ) (j k : Fin d) :
    unitVec d (Fin.succ k) (Fin.succ j) = if j = k then (1 : ℂ) else 0 := by
  unfold unitVec
  rw [Pi.single_apply]
  by_cases h : Fin.succ j = Fin.succ k
  · rw [if_pos h, if_pos (Fin.succ_inj.mp h)]
  · rw [if_neg h, if_neg (fun hjk => h (by rw [hjk]))]

theorem single_zero_zero_mulVec_eta (d : ℕ) :
    Matrix.single (0 : Fin (d+1)) (0 : Fin (d+1)) (1 : ℂ) *ᵥ eta d = eta d := by
  rw [Matrix.single_mulVec,
    show (1 : ℂ) * eta d (0 : Fin (d+1)) = 1 by rw [eta_zero, mul_one],
    update_zero_eq_single]
  rfl

theorem single_zero_succ_mulVec_eta (d : ℕ) (j : Fin d) :
    Matrix.single (0 : Fin (d+1)) (Fin.succ j) (1 : ℂ) *ᵥ eta d = 0 := by
  rw [Matrix.single_mulVec,
    show (1 : ℂ) * eta d (Fin.succ j) = 0 by rw [eta_succ, mul_zero],
    update_zero_eq_single]
  simp

theorem single_succ_zero_mulVec_eta (d : ℕ) (j : Fin d) :
    Matrix.single (Fin.succ j) (0 : Fin (d+1)) (1 : ℂ) *ᵥ eta d =
      unitVec d (Fin.succ j) := by
  rw [Matrix.single_mulVec,
    show (1 : ℂ) * eta d (0 : Fin (d+1)) = 1 by rw [eta_zero, mul_one],
    update_zero_eq_single]
  rfl

theorem single_zero_succ_mulVec_unit (d : ℕ) (j k : Fin d) :
    Matrix.single (0 : Fin (d+1)) (Fin.succ j) (1 : ℂ) *ᵥ unitVec d (Fin.succ k) =
      if j = k then eta d else 0 := by
  rw [Matrix.single_mulVec, unitVec_succ_succ]
  rw [show (1 : ℂ) * (if j = k then (1 : ℂ) else 0) = (if j = k then (1 : ℂ) else 0) by
    rw [one_mul]]
  rw [update_zero_eq_single]
  by_cases h : j = k
  · rw [if_pos h] at *
    rw [if_pos h]
    rfl
  · rw [if_neg h] at *
    rw [if_neg h]
    simp

theorem single_succ_zero_mulVec_unit (d : ℕ) (j k : Fin d) :
    Matrix.single (Fin.succ j) (0 : Fin (d+1)) (1 : ℂ) *ᵥ unitVec d (Fin.succ k) = 0 := by
  rw [Matrix.single_mulVec, unitVec_succ_zero,
    show (1 : ℂ) * 0 = 0 by rw [mul_zero], update_zero_eq_single]
  simp

theorem beta_mulVec_eta (d : ℕ) : beta d *ᵥ eta d = eta d := by
  unfold beta
  rw [sub_mulVec, smul_mulVec, one_mulVec, single_zero_zero_mulVec_eta, two_smul ℂ]
  abel

theorem alpha_mulVec_eta (d : ℕ) (j : Fin d) :
    alpha d j *ᵥ eta d = unitVec d (Fin.succ j) := by
  unfold alpha
  rw [add_mulVec, single_zero_succ_mulVec_eta, single_succ_zero_mulVec_eta, zero_add]

theorem beta_mulVec_unit_succ (d : ℕ) (j : Fin d) :
    beta d *ᵥ unitVec d (Fin.succ j) = - unitVec d (Fin.succ j) := by
  unfold beta
  rw [sub_mulVec, smul_mulVec, one_mulVec, Matrix.single_mulVec,
    unitVec_succ_zero,
    show (1 : ℂ) * 0 = 0 by rw [mul_zero], update_zero_eq_single]
  rw [Pi.single_zero, smul_zero, zero_sub]

theorem alpha_mulVec_unit_succ (d : ℕ) (j k : Fin d) :
    alpha d j *ᵥ unitVec d (Fin.succ k) = if j = k then eta d else 0 := by
  unfold alpha
  rw [add_mulVec, single_zero_succ_mulVec_unit, single_succ_zero_mulVec_unit, add_zero]

theorem anticomm_alpha_alpha (d : ℕ) (j k : Fin d) :
    (alpha d j * alpha d k + alpha d k * alpha d j) *ᵥ eta d =
      (2 * (if j = k then (1 : ℂ) else 0)) • eta d := by
  rw [add_mulVec, ← mulVec_mulVec, ← mulVec_mulVec, alpha_mulVec_eta,
    alpha_mulVec_unit_succ, alpha_mulVec_eta, alpha_mulVec_unit_succ]
  by_cases h : j = k
  · subst h
    simp only [if_true, mul_one]
    rw [two_smul ℂ]
  · rw [if_neg h, if_neg (Ne.symm h), if_neg h]
    simp

theorem anticomm_alpha_beta (d : ℕ) (j : Fin d) :
    (alpha d j * beta d + beta d * alpha d j) *ᵥ eta d = 0 := by
  rw [add_mulVec, ← mulVec_mulVec, ← mulVec_mulVec, beta_mulVec_eta,
    alpha_mulVec_eta, beta_mulVec_unit_succ]
  simp

theorem dirac_algebra_on_subspace (d : ℕ) :
    (∀ j k : Fin d,
        (alpha d j * alpha d k + alpha d k * alpha d j) *ᵥ eta d =
          (2 * (if j = k then (1 : ℂ) else 0)) • eta d) ∧
      (∀ j : Fin d, (alpha d j * beta d + beta d * alpha d j) *ᵥ eta d = 0) ∧
      beta d *ᵥ eta d = eta d :=
  ⟨anticomm_alpha_alpha d, anticomm_alpha_beta d, beta_mulVec_eta d⟩

noncomputable def freeHamiltonian (d : ℕ) (c : Fin d → ℂ) (g : ℂ) :
    Matrix (Fin (d+1)) (Fin (d+1)) ℂ :=
  (∑ j : Fin d, c j • alpha d j) + g • beta d

theorem alpha_sq_mulVec_eta (d : ℕ) (j : Fin d) :
    alpha d j *ᵥ (alpha d j *ᵥ eta d) = eta d := by
  rw [mulVec_mulVec]
  have h := anticomm_alpha_alpha d j j
  rw [if_pos rfl, mul_one, add_mulVec, two_smul] at h
  have h2 : (2 : ℂ) • ((alpha d j * alpha d j) *ᵥ eta d) = (2 : ℂ) • eta d := by
    rw [two_smul, two_smul]
    exact h
  exact (smul_right_injective (Fin (d+1) → ℂ) (by norm_num)) h2

theorem beta_sq_mulVec_eta (d : ℕ) :
    beta d *ᵥ (beta d *ᵥ eta d) = eta d := by
  rw [beta_mulVec_eta, beta_mulVec_eta]

theorem sum_alpha_mulVec_eta (d : ℕ) (c : Fin d → ℂ) :
    (∑ j : Fin d, c j • alpha d j) *ᵥ eta d =
      ∑ j : Fin d, c j • unitVec d (Fin.succ j) := by
  rw [Matrix.sum_mulVec]
  simp_rw [Matrix.smul_mulVec, alpha_mulVec_eta]

theorem sum_alpha_mulVec_unit (d : ℕ) (c : Fin d → ℂ) (k : Fin d) :
    (∑ j : Fin d, c j • alpha d j) *ᵥ unitVec d (Fin.succ k) = c k • eta d := by
  rw [Matrix.sum_mulVec, Finset.sum_eq_single k]
  · rw [Matrix.smul_mulVec, alpha_mulVec_unit_succ, if_pos rfl]
  · intro j _ hj
    rw [Matrix.smul_mulVec, alpha_mulVec_unit_succ, if_neg hj, smul_zero]
  · intro hk
    exact absurd (Finset.mem_univ k) hk

theorem sum_alpha_sq_mulVec_eta (d : ℕ) (c : Fin d → ℂ) :
    (∑ j : Fin d, c j • alpha d j) *ᵥ
      ((∑ j : Fin d, c j • alpha d j) *ᵥ eta d) =
      (∑ j : Fin d, (c j) ^ 2) • eta d := by
  rw [sum_alpha_mulVec_eta, Matrix.mulVec_sum]
  simp_rw [Matrix.mulVec_smul, sum_alpha_mulVec_unit, smul_smul]
  rw [← Finset.sum_smul]
  simp only [pow_two]

theorem beta_mulVec_sum_unit (d : ℕ) (c : Fin d → ℂ) :
    beta d *ᵥ (∑ j : Fin d, c j • unitVec d (Fin.succ j)) =
      - ∑ j : Fin d, c j • unitVec d (Fin.succ j) := by
  rw [Matrix.mulVec_sum]
  simp_rw [Matrix.mulVec_smul, beta_mulVec_unit_succ, smul_neg]
  rw [Finset.sum_neg_distrib]

theorem freeHamiltonian_mulVec_eta (d : ℕ) (c : Fin d → ℂ) (g : ℂ) :
    freeHamiltonian d c g *ᵥ eta d =
      (∑ j : Fin d, c j • unitVec d (Fin.succ j)) + g • eta d := by
  unfold freeHamiltonian
  rw [add_mulVec, Matrix.smul_mulVec, beta_mulVec_eta, sum_alpha_mulVec_eta]

theorem freeHamiltonian_sq_mulVec_eta (d : ℕ) (c : Fin d → ℂ) (g : ℂ) :
    freeHamiltonian d c g *ᵥ (freeHamiltonian d c g *ᵥ eta d) =
      ((∑ j : Fin d, (c j) ^ 2) + g ^ 2) • eta d := by
  rw [freeHamiltonian_mulVec_eta]
  unfold freeHamiltonian
  have hA : (∑ j : Fin d, c j • alpha d j) *ᵥ eta d =
      ∑ j : Fin d, c j • unitVec d (Fin.succ j) := sum_alpha_mulVec_eta d c
  have hSq : (∑ j : Fin d, c j • alpha d j) *ᵥ
      (∑ j : Fin d, c j • unitVec d (Fin.succ j)) =
      (∑ j : Fin d, (c j) ^ 2) • eta d := by
    rw [← hA]
    exact sum_alpha_sq_mulVec_eta d c
  have hB : beta d *ᵥ (∑ j : Fin d, c j • unitVec d (Fin.succ j)) =
      - ∑ j : Fin d, c j • unitVec d (Fin.succ j) := beta_mulVec_sum_unit d c
  rw [add_mulVec]
  simp only [Matrix.mulVec_add, Matrix.mulVec_smul, Matrix.smul_mulVec, beta_mulVec_eta]
  rw [hSq, hA, hB, smul_neg, smul_smul, ← pow_two, add_smul]
  abel

end Qatlib.Papers.DiracSearch04.MainResults
