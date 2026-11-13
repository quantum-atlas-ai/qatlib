/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.CarlemanLin24.MainResults.Source.SourceModel

set_option backward.isDefEq.respectTransparency false

/-!
# Resolvent Norm Bound for Non-Resonant Eigenvalue Sums

This module formalizes Lemma 2.5 of [Wu, Wang, and Li, 2024][WuWangLi2024], proving invertibility
and the induced-norm resolvent bound `ν ((s • 1 - F1)⁻¹) ≤ ν W * ν Winv / Δ` for sums of
eigenvalues separated from the spectrum of `F1` by at least `Δ`.

## Main statements

* `lemma_2_5`: invertibility of `s • 1 - F1` and the resolvent bound under `AssumptionOne`.

## References

* [Wu, Wang, and Li, 2024][WuWangLi2024]
-/

set_option autoImplicit false

noncomputable section

open scoped BigOperators

namespace Qatlib.Papers.CarlemanLin24.MainResults.Lemma25

open Qatlib.Papers.CarlemanLin24.MainResults.Source

/-- **Lemma 2.5** (arXiv:2405.12714v2, p. 10, Eq. (34)–(35)).

Let `F₁ = W Λ W⁻¹` satisfy Assumption 1, and let `s = λ_{i_1}+⋯+λ_{i_r}` be a
sum of `r ≥ 2` eigenvalues (the sums occurring in Definition 2.4).  If `s` is
separated from every `λ_i` by `Δ` (the no-resonance instance of Eq. (10) at
`s`), then `s I − F₁` is invertible and, for any matrix norm `ν` that is
submultiplicative, normalised at `1`, nonnegative, and bounded on diagonal
matrices by the maximal modulus entry (all standard for induced norms),

`ν ((s I − F₁)⁻¹) ≤ ν W · ν W⁻¹ / Δ`.

Specializing `ν` to the induced 1-norm gives Eq. (35); the paper's
"any induced norm" is captured by the generic `ν` hypotheses. -/
theorem lemma_2_5
    {n : ℕ} (F1 : Matrix (Fin n) (Fin n) ℂ) (W Winv : Matrix (Fin n) (Fin n) ℂ)
    (lam : Fin n → ℂ) (Δ : ℝ) (hass : AssumptionOne F1 W Winv lam Δ)
    (ν : Matrix (Fin n) (Fin n) ℂ → ℝ)
    (hν_mul : ∀ A B : Matrix (Fin n) (Fin n) ℂ, ν (A * B) ≤ ν A * ν B)
    (hν_one : ν 1 = 1)
    (hν_nonneg : ∀ A : Matrix (Fin n) (Fin n) ℂ, 0 ≤ ν A)
    (hν_diag : ∀ d : Fin n → ℂ, ν (Matrix.diagonal d) ≤
      ↑((Finset.univ : Finset (Fin n)).sup fun i => ‖d i‖₊))
    (s : ℂ) (hs : ∃ (r : ℕ) (idx : Fin r → Fin n),
      2 ≤ r ∧ s = ∑ i, lam (idx i))
    (hsep : ∀ i : Fin n, Δ ≤ ‖s - lam i‖) :
    IsUnit (s • (1 : Matrix (Fin n) (Fin n) ℂ) - F1) ∧
      ν ((s • (1 : Matrix (Fin n) (Fin n) ℂ) - F1)⁻¹) ≤ ν W * ν Winv / Δ := by
  rcases hs with ⟨r, idx, hr, hs_eq⟩
  have hr_pos : 0 < r := lt_of_lt_of_le (by decide : 0 < 2) hr
  obtain ⟨r, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hr_pos)
  subst s
  let s : ℂ := ∑ i : Fin (r + 1), lam (idx i)
  have hΔ : 0 < Δ := hass.delta_pos
  have hne (i : Fin n) : s - lam i ≠ 0 :=
    norm_pos_iff.mp (lt_of_lt_of_le hΔ (hsep i))
  let M := s • (1 : Matrix (Fin n) (Fin n) ℂ) - F1
  let D := Matrix.diagonal (fun i => s - lam i)
  let Dinv := Matrix.diagonal (fun i => (s - lam i)⁻¹)
  have hDDinv : D * Dinv = 1 := by
    simp only [D, Dinv, Matrix.diagonal_mul_diagonal, mul_inv_cancel₀ (hne _),
      Matrix.diagonal_one]
  have hDinvD : Dinv * D = 1 := by
    simp only [D, Dinv, Matrix.diagonal_mul_diagonal, inv_mul_cancel₀ (hne _),
      Matrix.diagonal_one]
  have hD : D = s • (1 : Matrix (Fin n) (Fin n) ℂ) - Matrix.diagonal lam := by
    dsimp [D]
    rw [← Matrix.diagonal_one, ← Matrix.diagonal_smul, Matrix.diagonal_sub]
    simp only [Pi.smul_apply, smul_eq_mul, mul_one]
  have hM : M = W * D * Winv := by
    calc
      M = s • (1 : Matrix (Fin n) (Fin n) ℂ) - W * Matrix.diagonal lam * Winv := by
        rw [← hass.diagonalizes]
      _ = W * (s • (1 : Matrix (Fin n) (Fin n) ℂ) - Matrix.diagonal lam) * Winv := by
        simp only [mul_sub, sub_mul, Matrix.mul_smul, Matrix.smul_mul, mul_one,
          hass.left_inv]
      _ = W * D * Winv := by rw [hD]
  let R := W * Dinv * Winv
  have hMR : M * R = 1 := by
    calc
      M * R = W * D * (Winv * W) * Dinv * Winv := by
        dsimp [R]
        rw [hM]
        simp only [mul_assoc]
      _ = W * (D * Dinv) * Winv := by
        rw [hass.right_inv]
        simp only [mul_one, mul_assoc]
      _ = 1 := by rw [hDDinv, mul_one, hass.left_inv]
  have hRM : R * M = 1 := by
    calc
      R * M = W * Dinv * (Winv * W) * D * Winv := by
        dsimp [R]
        rw [hM]
        simp only [mul_assoc]
      _ = W * (Dinv * D) * Winv := by
        rw [hass.right_inv]
        simp only [mul_one, mul_assoc]
      _ = 1 := by rw [hDinvD, mul_one, hass.left_inv]
  have hunit : IsUnit M := ⟨⟨M, R, hMR, hRM⟩, rfl⟩
  have hinv : M⁻¹ = R := Matrix.inv_eq_right_inv hMR
  have hsup : (Finset.univ : Finset (Fin n)).sup (fun i => ‖(s - lam i)⁻¹‖₊) ≤
      (Real.toNNReal Δ)⁻¹ := by
    apply Finset.sup_le
    intro i _
    rw [nnnorm_inv]
    apply inv_anti₀ (Real.toNNReal_pos.mpr hΔ)
    apply NNReal.coe_le_coe.mp
    simpa only [Real.coe_toNNReal Δ hΔ.le, coe_nnnorm] using hsep i
  have hDinv_bound : ν Dinv ≤ 1 / Δ := by
    apply (hν_diag (fun i => (s - lam i)⁻¹)).trans
    have hcast := NNReal.coe_le_coe.mpr hsup
    simpa only [NNReal.coe_inv, Real.coe_toNNReal Δ hΔ.le, one_div] using hcast
  refine ⟨hunit, ?_⟩
  have hbound : ν (M⁻¹) ≤ ν W * ν Winv / Δ := by
    calc
      ν (M⁻¹) = ν (W * (Dinv * Winv)) := by rw [hinv]; simp only [R, mul_assoc]
      _ ≤ ν W * ν (Dinv * Winv) := hν_mul W (Dinv * Winv)
      _ ≤ ν W * (ν Dinv * ν Winv) :=
        mul_le_mul_of_nonneg_left (hν_mul Dinv Winv) (hν_nonneg W)
      _ ≤ ν W * ((1 / Δ) * ν Winv) :=
        mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_right hDinv_bound (hν_nonneg Winv)) (hν_nonneg W)
      _ = ν W * ν Winv / Δ := by ring
  simpa only [hν_one, one_mul] using
    (mul_le_mul_of_nonneg_left hbound (hν_nonneg 1))

end Qatlib.Papers.CarlemanLin24.MainResults.Lemma25
