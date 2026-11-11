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

/-!
# Dirac matrix relations on the distinguished search vector

Sparse `(d + 1)`-dimensional matrices `alpha` and `beta` act on the distinguished vector `eta`
and coordinate vectors `unitVec`. Their actions establish Dirac anticommutation relations on
`eta` and a scalar formula for the square of `freeHamiltonian` applied to that vector.

This development follows [ChildsGoldstone2004a].

## Main statements

* `dirac_algebra_on_subspace`: anticommutation and beta-eigenvector identities evaluated on
  `eta`.
* `freeHamiltonian_mulVec_eta`: the Hamiltonian action on the distinguished vector.
* `freeHamiltonian_sq_mulVec_eta`: the squared action is multiplication by the sum of
  coefficient squares and the squared mass term.

## References

* [Childs and Goldstone, 2004][ChildsGoldstone2004a]
-/

set_option autoImplicit false

namespace Qatlib.Papers.DiracSearch04.MainResults

open Matrix

/-- The sparse matrix with unit entries connecting coordinate zero to coordinate `Fin.succ j` in
both directions. -/
noncomputable def alpha (d : ℕ) (j : Fin d) : Matrix (Fin (d+1)) (Fin (d+1)) ℂ :=
  Matrix.single (0 : Fin (d+1)) (Fin.succ j) 1 +
    Matrix.single (Fin.succ j) (0 : Fin (d+1)) 1

/-- The matrix twice the projection onto coordinate zero minus the identity. -/
noncomputable def beta (d : ℕ) : Matrix (Fin (d+1)) (Fin (d+1)) ℂ :=
  (2 : ℂ) • Matrix.single (0 : Fin (d+1)) (0 : Fin (d+1)) 1 - 1

/-- The coordinate vector supported at index zero with value one. -/
noncomputable def eta (d : ℕ) : Fin (d+1) → ℂ :=
  Pi.single (0 : Fin (d+1)) (1 : ℂ)

/-- The coordinate vector supported at index `i` with value one. -/
noncomputable def unitVec (d : ℕ) (i : Fin (d+1)) : Fin (d+1) → ℂ :=
  Pi.single i (1 : ℂ)

/-- Updating the zero vector at `i` with value `c` gives the corresponding single-coordinate
vector. -/
theorem update_zero_eq_single {n : ℕ} (i : Fin n) (c : ℂ) :
    Function.update (0 : Fin n → ℂ) i c = Pi.single (M := fun _ => ℂ) i c := by
  funext a
  by_cases h : a = i
  · subst h; rw [Function.update_self, Pi.single_eq_same]
  · rw [Function.update_of_ne h c (0 : Fin n → ℂ)]
    exact (Pi.single_eq_of_ne (M := fun _ => ℂ) h c).symm

/-- The distinguished vector `eta d` has value one at coordinate zero. -/
@[simp] theorem eta_zero (d : ℕ) : eta d (0 : Fin (d+1)) = 1 := by
  unfold eta; exact Pi.single_eq_same _ _

/-- The distinguished vector `eta d` vanishes at every successor coordinate. -/
theorem eta_succ (d : ℕ) (j : Fin d) : eta d (Fin.succ j) = 0 := by
  unfold eta; exact Pi.single_eq_of_ne (Fin.succ_ne_zero j) 1

/-- The coordinate vector `unitVec d i` has value one at its supporting index. -/
@[simp] theorem unitVec_self (d : ℕ) (i : Fin (d+1)) : unitVec d i i = 1 := by
  unfold unitVec; exact Pi.single_eq_same _ _

/-- A successor coordinate vector vanishes at coordinate zero. -/
theorem unitVec_succ_zero (d : ℕ) (k : Fin d) :
    unitVec d (Fin.succ k) (0 : Fin (d+1)) = 0 := by
  unfold unitVec; exact Pi.single_eq_of_ne (Fin.succ_ne_zero k).symm 1

/-- At successor coordinate `j`, the vector supported at successor coordinate `k` is one if `j =
k` and zero otherwise. -/
theorem unitVec_succ_succ (d : ℕ) (j k : Fin d) :
    unitVec d (Fin.succ k) (Fin.succ j) = if j = k then (1 : ℂ) else 0 := by
  unfold unitVec
  rw [Pi.single_apply]
  by_cases h : Fin.succ j = Fin.succ k
  · rw [if_pos h, if_pos (Fin.succ_inj.mp h)]
  · rw [if_neg h, if_neg (fun hjk => h (by rw [hjk]))]

/-- The matrix unit at entry `(0, 0)` fixes the distinguished vector. -/
theorem single_zero_zero_mulVec_eta (d : ℕ) :
    Matrix.single (0 : Fin (d+1)) (0 : Fin (d+1)) (1 : ℂ) *ᵥ eta d = eta d := by
  rw [Matrix.single_mulVec,
    show (1 : ℂ) * eta d (0 : Fin (d+1)) = 1 by rw [eta_zero, mul_one],
    update_zero_eq_single]
  rfl

/-- The matrix unit at entry `(0, Fin.succ j)` annihilates the distinguished vector. -/
theorem single_zero_succ_mulVec_eta (d : ℕ) (j : Fin d) :
    Matrix.single (0 : Fin (d+1)) (Fin.succ j) (1 : ℂ) *ᵥ eta d = 0 := by
  rw [Matrix.single_mulVec,
    show (1 : ℂ) * eta d (Fin.succ j) = 0 by rw [eta_succ, mul_zero],
    update_zero_eq_single]
  simp

/-- The matrix unit at entry `(Fin.succ j, 0)` sends the distinguished vector to the
corresponding successor coordinate vector. -/
theorem single_succ_zero_mulVec_eta (d : ℕ) (j : Fin d) :
    Matrix.single (Fin.succ j) (0 : Fin (d+1)) (1 : ℂ) *ᵥ eta d =
      unitVec d (Fin.succ j) := by
  rw [Matrix.single_mulVec,
    show (1 : ℂ) * eta d (0 : Fin (d+1)) = 1 by rw [eta_zero, mul_one],
    update_zero_eq_single]
  rfl

/-- The matrix unit at entry `(0, Fin.succ j)` sends the successor vector for `k` to `eta d` if
`j = k` and to zero otherwise. -/
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

/-- The matrix unit at entry `(Fin.succ j, 0)` annihilates every successor coordinate vector. -/
theorem single_succ_zero_mulVec_unit (d : ℕ) (j k : Fin d) :
    Matrix.single (Fin.succ j) (0 : Fin (d+1)) (1 : ℂ) *ᵥ unitVec d (Fin.succ k) = 0 := by
  rw [Matrix.single_mulVec, unitVec_succ_zero,
    show (1 : ℂ) * 0 = 0 by rw [mul_zero], update_zero_eq_single]
  simp

/-- The distinguished vector is a beta eigenvector with eigenvalue one. -/
theorem beta_mulVec_eta (d : ℕ) : beta d *ᵥ eta d = eta d := by
  unfold beta
  rw [sub_mulVec, smul_mulVec, one_mulVec, single_zero_zero_mulVec_eta, two_smul ℂ]
  abel

/-- The matrix `alpha d j` sends the distinguished vector to the successor coordinate vector for
`j`. -/
theorem alpha_mulVec_eta (d : ℕ) (j : Fin d) :
    alpha d j *ᵥ eta d = unitVec d (Fin.succ j) := by
  unfold alpha
  rw [add_mulVec, single_zero_succ_mulVec_eta, single_succ_zero_mulVec_eta, zero_add]

/-- Each successor coordinate vector is a beta eigenvector with eigenvalue minus one. See
[ChildsGoldstone2004a]. -/
theorem beta_mulVec_unit_succ (d : ℕ) (j : Fin d) :
    beta d *ᵥ unitVec d (Fin.succ j) = - unitVec d (Fin.succ j) := by
  unfold beta
  rw [sub_mulVec, smul_mulVec, one_mulVec, Matrix.single_mulVec,
    unitVec_succ_zero,
    show (1 : ℂ) * 0 = 0 by rw [mul_zero], update_zero_eq_single]
  rw [Pi.single_zero, smul_zero, zero_sub]

/-- The matrix `alpha d j` sends the successor vector for `k` to `eta d` if `j = k` and to zero
otherwise. See [ChildsGoldstone2004a]. -/
theorem alpha_mulVec_unit_succ (d : ℕ) (j k : Fin d) :
    alpha d j *ᵥ unitVec d (Fin.succ k) = if j = k then eta d else 0 := by
  unfold alpha
  rw [add_mulVec, single_zero_succ_mulVec_unit, single_succ_zero_mulVec_unit, add_zero]

/-- On the distinguished vector, the anticommutator of two alpha matrices acts as twice the
Kronecker delta. -/
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

/-- The anticommutator of an alpha matrix and beta annihilates the distinguished vector. -/
theorem anticomm_alpha_beta (d : ℕ) (j : Fin d) :
    (alpha d j * beta d + beta d * alpha d j) *ᵥ eta d = 0 := by
  rw [add_mulVec, ← mulVec_mulVec, ← mulVec_mulVec, beta_mulVec_eta,
    alpha_mulVec_eta, beta_mulVec_unit_succ]
  simp

/-- The alpha anticommutation relations and the alpha-beta anticommutation relation hold on `eta
d`, which beta fixes. See [ChildsGoldstone2004a]. -/
theorem dirac_algebra_on_subspace (d : ℕ) :
    (∀ j k : Fin d,
        (alpha d j * alpha d k + alpha d k * alpha d j) *ᵥ eta d =
          (2 * (if j = k then (1 : ℂ) else 0)) • eta d) ∧
      (∀ j : Fin d, (alpha d j * beta d + beta d * alpha d j) *ᵥ eta d = 0) ∧
      beta d *ᵥ eta d = eta d :=
  ⟨anticomm_alpha_alpha d, anticomm_alpha_beta d, beta_mulVec_eta d⟩

/-- The matrix sum of the alpha terms with coefficients `c` and the beta term with coefficient
`g`. -/
noncomputable def freeHamiltonian (d : ℕ) (c : Fin d → ℂ) (g : ℂ) :
    Matrix (Fin (d+1)) (Fin (d+1)) ℂ :=
  (∑ j : Fin d, c j • alpha d j) + g • beta d

/-- Applying the same alpha matrix twice to the distinguished vector returns that vector. -/
theorem alpha_sq_mulVec_eta (d : ℕ) (j : Fin d) :
    alpha d j *ᵥ (alpha d j *ᵥ eta d) = eta d := by
  rw [mulVec_mulVec]
  have h := anticomm_alpha_alpha d j j
  rw [if_pos rfl, mul_one, add_mulVec, two_smul] at h
  have h2 : (2 : ℂ) • ((alpha d j * alpha d j) *ᵥ eta d) = (2 : ℂ) • eta d := by
    rw [two_smul, two_smul]
    exact h
  exact (smul_right_injective (Fin (d+1) → ℂ) (by norm_num)) h2

/-- Applying beta twice to the distinguished vector returns that vector. -/
theorem beta_sq_mulVec_eta (d : ℕ) :
    beta d *ᵥ (beta d *ᵥ eta d) = eta d := by
  rw [beta_mulVec_eta, beta_mulVec_eta]

/-- The weighted alpha sum sends the distinguished vector to the correspondingly weighted sum of
successor coordinate vectors. -/
theorem sum_alpha_mulVec_eta (d : ℕ) (c : Fin d → ℂ) :
    (∑ j : Fin d, c j • alpha d j) *ᵥ eta d =
      ∑ j : Fin d, c j • unitVec d (Fin.succ j) := by
  rw [Matrix.sum_mulVec]
  simp_rw [Matrix.smul_mulVec, alpha_mulVec_eta]

/-- The weighted alpha sum sends the successor coordinate vector for `k` to `c k • eta d`. -/
theorem sum_alpha_mulVec_unit (d : ℕ) (c : Fin d → ℂ) (k : Fin d) :
    (∑ j : Fin d, c j • alpha d j) *ᵥ unitVec d (Fin.succ k) = c k • eta d := by
  rw [Matrix.sum_mulVec, Finset.sum_eq_single k]
  · rw [Matrix.smul_mulVec, alpha_mulVec_unit_succ, if_pos rfl]
  · intro j _ hj
    rw [Matrix.smul_mulVec, alpha_mulVec_unit_succ, if_neg hj, smul_zero]
  · intro hk
    exact absurd (Finset.mem_univ k) hk

/-- Applying the weighted alpha sum twice to the distinguished vector gives the sum of the
squared coefficients times that vector. See [ChildsGoldstone2004a]. -/
theorem sum_alpha_sq_mulVec_eta (d : ℕ) (c : Fin d → ℂ) :
    (∑ j : Fin d, c j • alpha d j) *ᵥ
      ((∑ j : Fin d, c j • alpha d j) *ᵥ eta d) =
      (∑ j : Fin d, (c j) ^ 2) • eta d := by
  rw [sum_alpha_mulVec_eta, Matrix.mulVec_sum]
  simp_rw [Matrix.mulVec_smul, sum_alpha_mulVec_unit, smul_smul]
  rw [← Finset.sum_smul]
  simp only [pow_two]

/-- Beta negates every weighted sum of successor coordinate vectors. -/
theorem beta_mulVec_sum_unit (d : ℕ) (c : Fin d → ℂ) :
    beta d *ᵥ (∑ j : Fin d, c j • unitVec d (Fin.succ j)) =
      - ∑ j : Fin d, c j • unitVec d (Fin.succ j) := by
  rw [Matrix.mulVec_sum]
  simp_rw [Matrix.mulVec_smul, beta_mulVec_unit_succ, smul_neg]
  rw [Finset.sum_neg_distrib]

/-- The free Hamiltonian sends `eta d` to the weighted successor-vector sum plus `g • eta d`.
See [ChildsGoldstone2004a]. -/
theorem freeHamiltonian_mulVec_eta (d : ℕ) (c : Fin d → ℂ) (g : ℂ) :
    freeHamiltonian d c g *ᵥ eta d =
      (∑ j : Fin d, c j • unitVec d (Fin.succ j)) + g • eta d := by
  unfold freeHamiltonian
  rw [add_mulVec, Matrix.smul_mulVec, beta_mulVec_eta, sum_alpha_mulVec_eta]

/-- The square of the free Hamiltonian acts on `eta d` by the scalar `(∑ j, (c j) ^ 2) + g ^ 2`.
See [ChildsGoldstone2004a]. -/
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
