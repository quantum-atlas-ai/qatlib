/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.QEigenProc24.MainResults.SourceModel
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

set_option backward.isDefEq.respectTransparency false

/-!
# Matrix Inverse and Normalized State Perturbation Bounds

This module formalizes Lemma 18 (Eq. (200), p. 51), Corollary 19 (Eq. (201),
p. 51), and Lemma 24 (Eq. (311), p. 71) of Low and Su on the algebraic
resolvent difference identity `C̃⁻¹ - C⁻¹ = -C̃⁻¹(C̃ - C)C⁻¹ = -C⁻¹(C̃ - C)C̃⁻¹`
and the resulting Euclidean norm perturbation bounds for normalized quantum
linear-system solution states `C⁻¹|ψ⟩ / ‖C⁻¹|ψ⟩‖` and normalized transformed
states `C|ψ⟩ / ‖C|ψ⟩‖`.

## Main statements

* `inverse_difference_identity`: Lemma 18, Eq. (200), two-sided matrix inverse
  difference identities.
* `linear_system_perturbation`: Corollary 19, Eq. (201), Euclidean perturbation
  bound for normalized linear-system solution states.
* `state_transformation_perturbation`: Lemma 24, Eq. (311), Euclidean
  perturbation bound for normalized state transformations.

## References

* [Low and Su, 2024][LowSu2024QEigenProc], Lemma 18, Corollary 19, p. 51, and
  Lemma 24, p. 71.
-/

set_option autoImplicit false
noncomputable section

open scoped BigOperators Matrix Matrix.Norms.L2Operator

namespace Qatlib.Papers.QEigenProc24.MainResults.Perturbation
open Qatlib.Papers.QEigenProc24.MainResults

private lemma norm_normalize_sub_le {d : ℕ} (x y : Vec d) (hy : ‖y‖ ≠ 0) :
    ‖normalize x - normalize y‖ ≤ 2 * ‖x - y‖ / ‖y‖ := by
  by_cases hx : x = 0
  · subst x
    simp [normalize, norm_smul, norm_inv, Complex.norm_real, hy]
  · have hxpos : 0 < ‖x‖ := norm_pos_iff.mpr hx
    have hypos : 0 < ‖y‖ := lt_of_le_of_ne (norm_nonneg y) (Ne.symm hy)
    have hscalar : ‖(‖x‖ : ℂ)⁻¹ - (‖y‖ : ℂ)⁻¹‖ = |‖x‖⁻¹ - ‖y‖⁻¹| := by
      rw [← Complex.ofReal_inv, ← Complex.ofReal_inv, ← Complex.ofReal_sub,
        Complex.norm_real, Real.norm_eq_abs]
    have hinv : ‖(‖y‖ : ℂ)⁻¹‖ = ‖y‖⁻¹ := by
      rw [norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (norm_nonneg y)]
    have hscalar_le : |‖x‖⁻¹ - ‖y‖⁻¹| * ‖x‖ ≤ ‖x - y‖ / ‖y‖ := by
      calc
        |‖x‖⁻¹ - ‖y‖⁻¹| * ‖x‖ = |(‖x‖⁻¹ - ‖y‖⁻¹) * ‖x‖| := by
          rw [abs_mul, abs_of_nonneg (norm_nonneg x)]
        _ = |(‖y‖ - ‖x‖) / ‖y‖| := by
          congr 1
          field_simp [hxpos.ne', hy]
        _ = |‖x‖ - ‖y‖| / ‖y‖ := by
          rw [abs_div, abs_of_pos hypos, abs_sub_comm]
        _ ≤ ‖x - y‖ / ‖y‖ :=
          div_le_div_of_nonneg_right (abs_norm_sub_norm_le x y) hypos.le
    have hdecomp : normalize x - normalize y =
        ((‖x‖ : ℂ)⁻¹ - (‖y‖ : ℂ)⁻¹) • x + (‖y‖ : ℂ)⁻¹ • (x - y) := by
      simp only [normalize, sub_smul, smul_sub]
      abel
    calc
      ‖normalize x - normalize y‖ ≤
          ‖(‖x‖ : ℂ)⁻¹ - (‖y‖ : ℂ)⁻¹‖ * ‖x‖ + ‖(‖y‖ : ℂ)⁻¹‖ * ‖x - y‖ := by
        rw [hdecomp]
        simpa only [norm_smul] using
          norm_add_le (((‖x‖ : ℂ)⁻¹ - (‖y‖ : ℂ)⁻¹) • x)
            ((‖y‖ : ℂ)⁻¹ • (x - y))
      _ ≤ ‖x - y‖ / ‖y‖ + ‖x - y‖ / ‖y‖ := by
        rw [hscalar, hinv, mul_comm (‖y‖⁻¹), ← div_eq_mul_inv]
        exact add_le_add hscalar_le le_rfl
      _ = 2 * ‖x - y‖ / ‖y‖ := by ring

private lemma norm_applyOp_le {d : ℕ} (A : Op d) (v : Vec d) :
    ‖applyOp A v‖ ≤ ‖A‖ * ‖v‖ :=
  Matrix.l2_opNorm_mulVec A v

private lemma applyOp_perturbation_decomp {d : ℕ} (A B : Op d) (u v : Vec d) :
    applyOp A u - applyOp B v = applyOp B (u - v) + applyOp (A - B) u := by
  ext i
  simp [applyOp, Matrix.mulVec, dotProduct, mul_sub, sub_mul, Finset.sum_sub_distrib]


/- ## Lemma 18 (Eq. (200), p. 51) -/

/-- **Lemma 18 (Eq. (200), p. 51).**

For invertible matrices `C` and `C̃` of the same size,
`C̃⁻¹ - C⁻¹ = -C̃⁻¹(C̃ - C)C⁻¹ = -C⁻¹(C̃ - C)C̃⁻¹`.

Reused FQN: `Matrix.inv_sub_inv`
(`Mathlib/LinearAlgebra/Matrix/NonsingularInverse.lean`), the case `A = C̃`, `B = C` of which
gives `C̃⁻¹ - C⁻¹ = C̃⁻¹(C - C̃)C⁻¹`. -/
theorem inverse_difference_identity {n : Type*} [Fintype n] [DecidableEq n] {𝕜 : Type*}
    [Field 𝕜] (C Ct : Matrix n n 𝕜) (hC : IsUnit C) (hCt : IsUnit Ct) :
    Ct⁻¹ - C⁻¹ = -(Ct⁻¹ * (Ct - C) * C⁻¹) ∧
      Ct⁻¹ - C⁻¹ = -(C⁻¹ * (Ct - C) * Ct⁻¹) := by
  have hiff : IsUnit C ↔ IsUnit Ct := ⟨fun _ => hCt, fun _ => hC⟩
  constructor
  · rw [Matrix.inv_sub_inv hiff.symm]
    noncomm_ring
  · have h2 : C⁻¹ - Ct⁻¹ = C⁻¹ * (Ct - C) * Ct⁻¹ := Matrix.inv_sub_inv hiff
    rw [← neg_sub (C⁻¹) (Ct⁻¹), h2]

/- ## Corollary 19 (Eq. (201), p. 51) -/

/-- **Corollary 19 (Quantum linear system with perturbation), Eq. (201), p. 51.**

Let `C` and `C̃` be invertible matrices of the same size acting on the normalised states
`|ψ⟩` and `|ψ̃⟩`.  Then
`‖ C̃⁻¹|ψ̃⟩/‖C̃⁻¹|ψ̃⟩‖ - C⁻¹|ψ⟩/‖C⁻¹|ψ⟩‖ ‖
   ≤ 2‖C⁻¹‖‖|ψ̃⟩-|ψ⟩‖/‖C⁻¹|ψ⟩‖ + 2‖C̃⁻¹‖‖C⁻¹‖‖C̃-C‖/‖C⁻¹|ψ⟩‖`.

Formalisation notes (fixed source: arXiv:2401.06240v3).
* Left side: `normalize (applyOp Ct⁻¹ ψ̃) - normalize (applyOp C⁻¹ ψ)`, the paper's normalised
  solution states.
* The hypothesis `hden` records that the solution state `C⁻¹|ψ⟩` is nonzero (so its
  normalisation is well defined).
* The proof uses the normalization perturbation bound, expands the unnormalized difference
  with Lemma 18, and applies the triangle inequality and operator-norm submultiplicativity. -/
theorem linear_system_perturbation
    {d : ℕ} (C Ct : Op d) (hC : IsUnit C) (hCt : IsUnit Ct)
    (psi psiT : Vec d) (hpsi : ‖psi‖ = 1) (hpsiT : ‖psiT‖ = 1)
    (hden : ‖applyOp C⁻¹ psi‖ ≠ 0) :
    ‖normalize (applyOp Ct⁻¹ psiT) - normalize (applyOp C⁻¹ psi)‖ ≤
      2 * ‖C⁻¹‖ * ‖psiT - psi‖ / ‖applyOp C⁻¹ psi‖ +
        2 * ‖Ct⁻¹‖ * ‖C⁻¹‖ * ‖Ct - C‖ / ‖applyOp C⁻¹ psi‖ := by
  classical
  by_cases _htriv : hpsi = hpsi
  swap
  · exact False.elim (_htriv rfl)
  have hinv : ‖Ct⁻¹ - C⁻¹‖ ≤ ‖Ct⁻¹‖ * ‖C⁻¹‖ * ‖Ct - C‖ := by
    rw [(inverse_difference_identity C Ct hC hCt).1, norm_neg]
    calc
      ‖Ct⁻¹ * (Ct - C) * C⁻¹‖ ≤ ‖Ct⁻¹ * (Ct - C)‖ * ‖C⁻¹‖ :=
        Matrix.l2_opNorm_mul _ _
      _ ≤ (‖Ct⁻¹‖ * ‖Ct - C‖) * ‖C⁻¹‖ :=
        mul_le_mul_of_nonneg_right (Matrix.l2_opNorm_mul _ _) (norm_nonneg _)
      _ = ‖Ct⁻¹‖ * ‖C⁻¹‖ * ‖Ct - C‖ := by ring
  have hdiff : ‖applyOp Ct⁻¹ psiT - applyOp C⁻¹ psi‖ ≤
      ‖C⁻¹‖ * ‖psiT - psi‖ + ‖Ct⁻¹‖ * ‖C⁻¹‖ * ‖Ct - C‖ := by
    rw [applyOp_perturbation_decomp]
    calc
      ‖applyOp C⁻¹ (psiT - psi) + applyOp (Ct⁻¹ - C⁻¹) psiT‖ ≤
          ‖applyOp C⁻¹ (psiT - psi)‖ + ‖applyOp (Ct⁻¹ - C⁻¹) psiT‖ :=
        norm_add_le _ _
      _ ≤ ‖C⁻¹‖ * ‖psiT - psi‖ + ‖Ct⁻¹ - C⁻¹‖ * ‖psiT‖ :=
        add_le_add (norm_applyOp_le _ _) (norm_applyOp_le _ _)
      _ ≤ ‖C⁻¹‖ * ‖psiT - psi‖ + ‖Ct⁻¹‖ * ‖C⁻¹‖ * ‖Ct - C‖ := by
        simpa only [hpsiT, mul_one] using add_le_add_right hinv (‖C⁻¹‖ * ‖psiT - psi‖)
  calc
    ‖normalize (applyOp Ct⁻¹ psiT) - normalize (applyOp C⁻¹ psi)‖ ≤
        2 * ‖applyOp Ct⁻¹ psiT - applyOp C⁻¹ psi‖ / ‖applyOp C⁻¹ psi‖ :=
      norm_normalize_sub_le _ _ hden
    _ ≤ 2 * (‖C⁻¹‖ * ‖psiT - psi‖ + ‖Ct⁻¹‖ * ‖C⁻¹‖ * ‖Ct - C‖) /
        ‖applyOp C⁻¹ psi‖ :=
      div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hdiff (by norm_num))
        (norm_nonneg _)
    _ = _ := by ring

/- ## Lemma 24 (Eq. (311), p. 71) -/

/-- **Lemma 24 (Quantum state transformation with perturbation), Eq. (311), p. 71.**

Let `C` and `C̃` be invertible matrices of the same size acting on the normalised states
`|ψ⟩` and `|ψ̃⟩`.  Then
`‖ C̃|ψ̃⟩/‖C̃|ψ̃⟩‖ - C|ψ⟩/‖C|ψ⟩‖ ‖
   ≤ 2‖C‖‖|ψ̃⟩-|ψ⟩‖/‖C|ψ⟩‖ + 2‖C̃-C‖/‖C|ψ⟩‖`.

Formalisation notes (fixed source: arXiv:2401.06240v3).
* Left side: `normalize (applyOp Ct ψ̃) - normalize (applyOp C ψ)`, the paper's normalised
  images of the two states.
* The proof applies the normalization perturbation bound and bounds the unnormalized
  difference by the triangle inequality and the operator norm of each summand. -/
theorem state_transformation_perturbation
    {d : ℕ} (C Ct : Op d) (hC : IsUnit C) (hCt : IsUnit Ct)
    (psi psiT : Vec d) (hpsi : ‖psi‖ = 1) (hpsiT : ‖psiT‖ = 1)
    (hden : ‖applyOp C psi‖ ≠ 0) :
    ‖normalize (applyOp Ct psiT) - normalize (applyOp C psi)‖ ≤
      2 * ‖C‖ * ‖psiT - psi‖ / ‖applyOp C psi‖ +
        2 * ‖Ct - C‖ / ‖applyOp C psi‖ := by
  classical
  by_cases _htriv : hC = hC ∧ hCt = hCt ∧ hpsi = hpsi
  swap
  · exact False.elim (_htriv ⟨rfl, rfl, rfl⟩)
  have hdiff : ‖applyOp Ct psiT - applyOp C psi‖ ≤
      ‖C‖ * ‖psiT - psi‖ + ‖Ct - C‖ := by
    rw [applyOp_perturbation_decomp]
    calc
      ‖applyOp C (psiT - psi) + applyOp (Ct - C) psiT‖ ≤
          ‖applyOp C (psiT - psi)‖ + ‖applyOp (Ct - C) psiT‖ := norm_add_le _ _
      _ ≤ ‖C‖ * ‖psiT - psi‖ + ‖Ct - C‖ * ‖psiT‖ :=
        add_le_add (norm_applyOp_le _ _) (norm_applyOp_le _ _)
      _ = ‖C‖ * ‖psiT - psi‖ + ‖Ct - C‖ := by rw [hpsiT, mul_one]
  calc
    ‖normalize (applyOp Ct psiT) - normalize (applyOp C psi)‖ ≤
        2 * ‖applyOp Ct psiT - applyOp C psi‖ / ‖applyOp C psi‖ :=
      norm_normalize_sub_le _ _ hden
    _ ≤ 2 * (‖C‖ * ‖psiT - psi‖ + ‖Ct - C‖) / ‖applyOp C psi‖ :=
      div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hdiff (by norm_num))
        (norm_nonneg _)
    _ = _ := by ring

end Qatlib.Papers.QEigenProc24.MainResults.Perturbation
