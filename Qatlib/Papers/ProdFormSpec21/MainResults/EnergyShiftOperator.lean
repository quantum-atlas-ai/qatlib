/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Analysis.Normed.Operator.Basic
import Mathlib.Tactic.NormNum

/-!
# Operator-norm energy shift for Lemma 3

This module gives operator estimates related to [YiCrosson2022],
Lemma 3, Eqs. (18)--(19), in a general complex inner-product space
with its true Euclidean norm and the true operator norm of continuous
linear maps.  If a perturbation `W` decomposes at a unit vector `ψ`
as `W ψ = δt • (W₁ ψ) + W₂ ψ` with vanishing first-order diagonal
`⟪ψ, W₁ ψ⟫_ℂ = 0` (the off-diagonal first-order cancellation), then
the diagonal expectation satisfies `‖⟪ψ, W ψ⟫_ℂ‖ ≤ ‖W₂‖`.  Applied to
`W = H̃ - H`, Cauchy--Schwarz and the operator norm give the
Rayleigh-quotient shift bound `|Re ⟪ψ, H̃ ψ⟫ - Re ⟪ψ, H ψ⟫| ≤ ‖H̃ - H‖`,
and hence the Eq. (19) scale `N² δt² max{1, 1/lam²}` whenever the
operator norm is bounded by that scale. For a common eigenvector the
Rayleigh quotients are the eigenvalues. The general spectral estimate in
Eq. (19) compares eigenvalues even when their eigenvectors differ.

The real-symmetric commutator cancellation that produces the
vanishing first-order diagonal for product formulas is
`Qatlib.Papers.ProdFormSpec21.MainResults.lemma3_first_perturbation_offdiagonal`;
deriving the operator-norm scale from the product formula itself is
not claimed here.
[Fixed source](https://arxiv.org/abs/2102.12655v1).
-/

@[expose] public section

set_option autoImplicit false

namespace Qatlib.Papers.ProdFormSpec21.MainResults

open scoped InnerProductSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

/-- **Lemma 3, Eq. (18) operator form.**  Let `W W₁ W₂ : E →L[ℂ] E`
and a unit vector `ψ`.  If `W ψ = (δt : ℂ) • (W₁ ψ) + W₂ ψ` and the
first-order diagonal vanishes, `⟪ψ, W₁ ψ⟫_ℂ = 0`, then the diagonal
expectation of the full perturbation is controlled by the second-order
remainder alone: `‖⟪ψ, W ψ⟫_ℂ‖ ≤ ‖W₂‖` in the operator norm. -/
theorem first_order_diagonal_bound (W W₁ W₂ : E →L[ℂ] E) (ψ : E)
    (hψ : ‖ψ‖ = 1) (δt : ℝ)
    (hdecomp : W ψ = (δt : ℂ) • (W₁ ψ) + W₂ ψ)
    (hdiag : ⟪ψ, W₁ ψ⟫_ℂ = 0) :
    ‖⟪ψ, W ψ⟫_ℂ‖ ≤ ‖W₂‖ := by
  have h1 : ⟪ψ, W ψ⟫_ℂ = ⟪ψ, W₂ ψ⟫_ℂ := by
    rw [hdecomp, inner_add_right, inner_smul_right, hdiag, mul_zero,
      zero_add]
  rw [h1]
  calc ‖⟪ψ, W₂ ψ⟫_ℂ‖ ≤ ‖ψ‖ * ‖W₂ ψ‖ := norm_inner_le_norm ψ (W₂ ψ)
    _ ≤ ‖ψ‖ * (‖W₂‖ * ‖ψ‖) := by
        apply mul_le_mul_of_nonneg_left _ (norm_nonneg ψ)
        exact ContinuousLinearMap.le_opNorm _ _
    _ = ‖W₂‖ := by simp [hψ]

/-- **Lemma 3, Rayleigh shift by the operator norm.**  For continuous
linear maps `H H̃ : E →L[ℂ] E` and a unit vector `ψ`, the real
Rayleigh-quotient shift satisfies
`|Re ⟪ψ, H̃ ψ⟫_ℂ - Re ⟪ψ, H ψ⟫_ℂ| ≤ ‖H̃ - H‖` in the operator norm,
by Cauchy--Schwarz in the Euclidean norm. -/
theorem rayleigh_shift_le_opNorm (H Ht : E →L[ℂ] E) (ψ : E)
    (hψ : ‖ψ‖ = 1) :
    |Complex.re ⟪ψ, Ht ψ⟫_ℂ - Complex.re ⟪ψ, H ψ⟫_ℂ| ≤ ‖Ht - H‖ := by
  have hdiff : ⟪ψ, Ht ψ⟫_ℂ - ⟪ψ, H ψ⟫_ℂ = ⟪ψ, (Ht - H) ψ⟫_ℂ := by
    rw [sub_apply, inner_sub_right]
  have hre : Complex.re ⟪ψ, Ht ψ⟫_ℂ - Complex.re ⟪ψ, H ψ⟫_ℂ
      = Complex.re (⟪ψ, Ht ψ⟫_ℂ - ⟪ψ, H ψ⟫_ℂ) := by
    rw [Complex.sub_re]
  rw [hre, hdiff]
  calc |Complex.re ⟪ψ, (Ht - H) ψ⟫_ℂ|
      ≤ ‖⟪ψ, (Ht - H) ψ⟫_ℂ‖ := Complex.abs_re_le_norm _
    _ ≤ ‖ψ‖ * ‖(Ht - H) ψ‖ := norm_inner_le_norm ψ ((Ht - H) ψ)
    _ ≤ ‖ψ‖ * (‖Ht - H‖ * ‖ψ‖) := by
        apply mul_le_mul_of_nonneg_left _ (norm_nonneg ψ)
        exact ContinuousLinearMap.le_opNorm _ _
    _ = ‖Ht - H‖ := by simp [hψ]

/-- **Lemma 3, Eq. (19) scale.**  If the operator norm of the effective
perturbation satisfies
`‖H̃ - H‖ ≤ N ^ 2 * δt ^ 2 * max 1 (1 / lam ^ 2)`, then every unit
vector has Rayleigh-quotient shift bounded by the same scale. -/
theorem rayleigh_shift_le_scale (H Ht : E →L[ℂ] E) (N δt lam : ℝ) (_hlam : 0 < lam)
    (hW : ‖Ht - H‖ ≤ N ^ 2 * δt ^ 2 * max 1 (1 / lam ^ 2)) :
    ∀ ψ : E, ‖ψ‖ = 1 → |Complex.re ⟪ψ, Ht ψ⟫_ℂ - Complex.re ⟪ψ, H ψ⟫_ℂ|
      ≤ N ^ 2 * δt ^ 2 * max 1 (1 / lam ^ 2) :=
  fun ψ hψ => (rayleigh_shift_le_opNorm H Ht ψ hψ).trans hW

/-- **Common-eigenvector comparison.** If a unit vector
`ψ` is an eigenvector of both `H` and `H̃` with real eigenvalues `Ek`
and `Ẽk`, then `|Ẽk - Ek| ≤ ‖H̃ - H‖` in the operator norm. -/
theorem eigenvalue_shift_le_opNorm (H Ht : E →L[ℂ] E) (ψ : E)
    (hψ : ‖ψ‖ = 1) (Ek Etk : ℝ)
    (hH : H ψ = (Ek : ℂ) • ψ) (hHt : Ht ψ = (Etk : ℂ) • ψ) :
    |Etk - Ek| ≤ ‖Ht - H‖ := by
  have hself : ⟪ψ, ψ⟫_ℂ = 1 := by
    rw [inner_self_eq_norm_sq_to_K, hψ]
    norm_num
  have h1 : ⟪ψ, H ψ⟫_ℂ = (Ek : ℂ) := by
    rw [hH, inner_smul_right, hself, mul_one]
  have h2 : ⟪ψ, Ht ψ⟫_ℂ = (Etk : ℂ) := by
    rw [hHt, inner_smul_right, hself, mul_one]
  have h := rayleigh_shift_le_opNorm H Ht ψ hψ
  rw [h1, h2] at h
  have hre1 : Complex.re ((Etk : ℂ)) = Etk := Complex.ofReal_re Etk
  have hre2 : Complex.re ((Ek : ℂ)) = Ek := Complex.ofReal_re Ek
  rw [hre1, hre2] at h
  exact h

end Qatlib.Papers.ProdFormSpec21.MainResults
