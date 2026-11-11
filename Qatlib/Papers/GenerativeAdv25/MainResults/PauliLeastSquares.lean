/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Tactic
import Mathlib.Analysis.InnerProductSpace.PiL2

set_option backward.isDefEq.respectTransparency false

/-! Strong convexity of the Pauli least-squares loss in
"Generative quantum advantage for classical and quantum problems"
(arXiv:2509.09033v1, 2025).

Theorem 10 of the paper: the least-squares loss used to learn the
Pauli coefficients of an unknown unitary,

`ℒ(α) = (1/N) Σ_ℓ ‖α − d_ℓ‖²`,

decomposes around the data barycentre `d̄ = (1/N) Σ_ℓ d_ℓ` as

`ℒ(α) = ‖α − d̄‖² + variance`,

so it is `2`-strongly convex (Hessian `2𝟙` in the paper's
normalisation: the quadratic term has unit leading coefficient).

Corollary 1 of the paper: the loss has a unique global minimum
`α* = d̄`, every local minimum is the global one, and every critical
point equals `α*`.

This file proves, over a finite-dimensional real inner-product space
(the paper's parameter space `ℝ^m`):

- `sum_sub_mean_eq_zero`: the residuals `d̄ − d_ℓ` sum to zero.
- `lsLoss_eq`: the variance decomposition (Theorem 10).
- `lsLoss_strict_convex_eq`: the exact strong-convexity identity
  `ℒ(t•α+(1−t)•β) = tℒ(α)+(1−t)ℒ(β) − t(1−t)‖α−β‖²`, whose
  curvature constant `1` on `‖α−β‖²` (before the paper's factor-2
  gradient convention) is the initial-form counterpart of Hessian
  `2𝟙`; `lsLoss_strong_convex` is its inequality form.
- `lsLoss_eq_min_iff`, `lsCritical_eq_mean`: Corollary 1 — the unique
  global minimiser is `d̄`, and every critical point (first-order
  orthogonality to all directions) is `d̄`.

No axiom beyond the three standard ones, no `sorry`. -/
set_option autoImplicit false

namespace Qatlib.Papers.GenerativeAdv25.MainResults.PauliLeastSquares

open Finset
open scoped RealInnerProductSpace
open scoped InnerProductSpace

variable {D : Type} [Fintype D] {N : ℕ} [NeZero N]

/-- The empirical ℓ² loss `ℒ(α) = (1/N) Σ_ℓ ‖α − d_ℓ‖²` on the
Pauli-coefficient parameter space, with the paper's `1/N`
normalisation. -/
noncomputable def lsLoss (d : Fin N → EuclideanSpace ℝ D) (α : EuclideanSpace ℝ D) : ℝ :=
  (1 / (N : ℝ)) * ∑ ℓ ∈ Finset.univ, ‖α - d ℓ‖ ^ 2

/-- The data barycentre `d̄ = (1/N) Σ_ℓ d_ℓ`. -/
noncomputable def lsMean (d : Fin N → EuclideanSpace ℝ D) : EuclideanSpace ℝ D :=
  (1 / (N : ℝ)) • ∑ ℓ ∈ Finset.univ, d ℓ

/-- The irreducible variance term `(1/N) Σ_ℓ ‖d̄ − d_ℓ‖²`. -/
noncomputable def lsVariance (d : Fin N → EuclideanSpace ℝ D) : ℝ :=
  (1 / (N : ℝ)) * ∑ ℓ ∈ Finset.univ, ‖lsMean d - d ℓ‖ ^ 2

/-- The sample size casts to a non-zero real. -/
lemma cast_ne_zero' : ((N : ℝ)) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne N)

omit [Fintype D] in
/-- The residuals `d̄ − d_ℓ` sum to zero: the barycentre absorbs the
first-order cross term of the variance decomposition. -/
lemma sum_sub_mean_eq_zero (d : Fin N → EuclideanSpace ℝ D) :
    ∑ ℓ ∈ Finset.univ, (lsMean d - d ℓ) = 0 := by
  rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    ← Nat.cast_smul_eq_nsmul (R := ℝ), lsMean, smul_smul, one_div, mul_inv_cancel₀ cast_ne_zero',
    one_smul, sub_self]

/-- Theorem 10, expansion step: the empirical squared-distance sum
splits into `N` times the squared distance to the barycentre plus the
residual sum. -/
theorem sum_dist_eq_smul_dist_mean (d : Fin N → EuclideanSpace ℝ D)
    (α : EuclideanSpace ℝ D) :
    ∑ ℓ ∈ Finset.univ, ‖α - d ℓ‖ ^ 2
      = (N : ℝ) * ‖α - lsMean d‖ ^ 2 + ∑ ℓ ∈ Finset.univ, ‖lsMean d - d ℓ‖ ^ 2 := by
  have e : ∀ ℓ : Fin N, ‖α - d ℓ‖ ^ 2
      = ‖α - lsMean d‖ ^ 2 + (2 : ℝ) • ⟪α - lsMean d, lsMean d - d ℓ⟫_ℝ
          + ‖lsMean d - d ℓ‖ ^ 2 := by
    intro ℓ
    have h : α - d ℓ = (α - lsMean d) + (lsMean d - d ℓ) := by abel
    rw [h, norm_add_sq_real, smul_eq_mul]
  rw [Finset.sum_congr rfl (fun ℓ _ => e ℓ), Finset.sum_add_distrib,
    Finset.sum_add_distrib, ← Finset.smul_sum, ← inner_sum,
    sum_sub_mean_eq_zero, inner_zero_right, smul_zero, add_zero,
    Finset.sum_const, Finset.card_univ, Fintype.card_fin, ← Nat.cast_smul_eq_nsmul (R := ℝ),
    smul_eq_mul]

/-- **Theorem 10 (variance decomposition)**: the least-squares loss
equals the squared distance to the barycentre plus the irreducible
variance; the Hessian is `2𝟙`, i.e. the loss is strongly convex. -/
theorem lsLoss_eq (d : Fin N → EuclideanSpace ℝ D) (α : EuclideanSpace ℝ D) :
    lsLoss d α = ‖α - lsMean d‖ ^ 2 + lsVariance d := by
  unfold lsLoss lsVariance
  rw [sum_dist_eq_smul_dist_mean, mul_add, ← mul_assoc,
    div_mul_cancel₀ _ cast_ne_zero', one_mul]

omit [NeZero N] in
/-- The variance term is non-negative. -/
lemma lsVariance_nonneg (d : Fin N → EuclideanSpace ℝ D) : 0 ≤ lsVariance d := by
  unfold lsVariance
  exact mul_nonneg (one_div_nonneg.mpr (Nat.cast_nonneg N))
    (Finset.sum_nonneg (fun ℓ _ => pow_nonneg (norm_nonneg _) 2))

/-- The barycentre attains the variance as its loss value. -/
theorem lsLoss_mean_eq_variance (d : Fin N → EuclideanSpace ℝ D) :
    lsLoss d (lsMean d) = lsVariance d := by
  rw [lsLoss_eq, sub_self, norm_zero, zero_pow two_ne_zero, zero_add]

/-- **Corollary 1 (a), (b)**: the unique global minimum of the loss is
the barycentre `d̄` — every α attaining the minimum value is `d̄`, so
every local minimum is the global one. -/
theorem lsLoss_eq_min_iff (d : Fin N → EuclideanSpace ℝ D)
    (α : EuclideanSpace ℝ D) :
    lsLoss d α = lsVariance d ↔ α = lsMean d := by
  rw [lsLoss_eq]
  constructor
  · intro h
    have h2 : ‖α - lsMean d‖ ^ 2 = 0 := by
      have := lsVariance_nonneg d
      linarith
    have h3 : ‖α - lsMean d‖ = 0 := pow_eq_zero_iff two_ne_zero |>.mp h2
    exact sub_eq_zero.mp (norm_eq_zero.mp h3)
  · intro h
    subst h
    rw [sub_self, norm_zero, zero_pow two_ne_zero, zero_add]

omit [NeZero N] in
/-- **Corollary 1 (c)**: every critical point is the global minimiser,
captured first-order-free as orthogonality to all directions. -/
theorem lsCritical_eq_mean (d : Fin N → EuclideanSpace ℝ D)
    (α : EuclideanSpace ℝ D)
    (h : ∀ v : EuclideanSpace ℝ D, ⟪α - lsMean d, v⟫_ℝ = 0) :
    α = lsMean d := by
  have h0 := h (α - lsMean d)
  rw [inner_self_eq_zero] at h0
  exact sub_eq_zero.mp h0

/-- Squared norms satisfy the exact convex-combination identity with
curvature `t(1−t)‖u−v‖²` on inner-product spaces. -/
lemma norm_sq_convex {t : ℝ} (ht₀ : 0 ≤ t) (ht₁ : t ≤ 1)
    (u v : EuclideanSpace ℝ D) :
    ‖t • u + (1 - t) • v‖ ^ 2
      = t * ‖u‖ ^ 2 + (1 - t) * ‖v‖ ^ 2 - t * (1 - t) * ‖u - v‖ ^ 2 := by
  have hu : ‖t • u‖ = t * ‖u‖ := by
    rw [norm_smul, Real.norm_of_nonneg ht₀]
  have hv : ‖(1 - t) • v‖ = (1 - t) * ‖v‖ := by
    rw [norm_smul, Real.norm_of_nonneg (by linarith)]
  rw [norm_add_sq_real, real_inner_smul_left, real_inner_smul_right,
    norm_sub_sq_real, hu, hv]
  ring

omit [Fintype D] in
/-- Affine combinations commute with subtracting the pivot `m`. -/
lemma conv_comb_sub (t : ℝ) (a b m : EuclideanSpace ℝ D) :
    t • a + (1 - t) • b - m = t • (a - m) + (1 - t) • (b - m) := by
  module

/-- **Theorem 10 (strong convexity, exact initial form)**: the loss
satisfies the strong-convexity identity with curvature constant `1` on
`‖α − β‖²` (unit coefficient before the paper's factor-2 gradient
convention, i.e. Hessian `2𝟙`); equality, not just inequality. -/
theorem lsLoss_strict_convex_eq (d : Fin N → EuclideanSpace ℝ D) {t : ℝ}
    (ht : t ∈ Set.Icc (0 : ℝ) 1) (α β : EuclideanSpace ℝ D) :
    lsLoss d (t • α + (1 - t) • β)
      = t * lsLoss d α + (1 - t) * lsLoss d β - t * (1 - t) * ‖α - β‖ ^ 2 := by
  have hm : t • α + (1 - t) • β - lsMean d
      = t • (α - lsMean d) + (1 - t) • (β - lsMean d) :=
    conv_comb_sub t α β (lsMean d)
  have hsub : (α - lsMean d) - (β - lsMean d) = α - β := by abel
  rw [lsLoss_eq, lsLoss_eq, lsLoss_eq, hm,
    norm_sq_convex ht.1 ht.2 (α - lsMean d) (β - lsMean d), hsub]
  ring

/-- **Theorem 10 (strong convexity, inequality form)**: the loss is
`t(1−t)‖α−β‖²`-strongly convex along segments. -/
theorem lsLoss_strong_convex (d : Fin N → EuclideanSpace ℝ D) {t : ℝ}
    (ht : t ∈ Set.Icc (0 : ℝ) 1) (α β : EuclideanSpace ℝ D) :
    lsLoss d (t • α + (1 - t) • β) + t * (1 - t) * ‖α - β‖ ^ 2
      ≤ t * lsLoss d α + (1 - t) * lsLoss d β := by
  have hc : 0 ≤ t * (1 - t) * ‖α - β‖ ^ 2 := by
    have ht₂ : 0 ≤ 1 - t := by linarith [ht.2]
    exact mul_nonneg (mul_nonneg ht.1 ht₂) (pow_nonneg (norm_nonneg _) 2)
  rw [lsLoss_strict_convex_eq d ht α β]
  linarith

end Qatlib.Papers.GenerativeAdv25.MainResults.PauliLeastSquares
