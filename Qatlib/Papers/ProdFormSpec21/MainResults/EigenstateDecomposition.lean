/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# Eigenstate decomposition and phase accumulation for Corollary 1

This module supplies the Gram--Schmidt content of [YiCrosson2022],
Corollary 1, Eqs. (16)--(17), in a general complex inner-product space
with its true Euclidean norm.  For unit vectors `φ` (the ideal evolved
eigenstate `U(t)|ψk⟩`) and `ψ` (the Trotterized state `T(δt)^L|ψk⟩`),
the residual `ψ - ⟪φ, ψ⟫ • φ` is orthogonal to `φ`, and Pythagoras
identifies the fidelity defect `1 - ‖⟪φ, ψ⟫‖²` with the squared
Euclidean norm of that residual. A separate finite-sum estimate bounds
the sum of real increments by `L` times a uniform per-step bound.
Identifying the physical phase defect with such a sum requires an
additional argument.

The deep Lemma 1 / Lemma 2 analytic inputs that estimate the residual
and the per-step phase in terms of `h`, `δt` and the gap `lam` are not
reproved here; the scalar combination with those inputs is
`Qatlib.Papers.ProdFormSpec21.MainResults.corollary1_eigenstate`.
[Fixed source](https://arxiv.org/abs/2102.12655v1).
-/

@[expose] public section

set_option autoImplicit false

namespace Qatlib.Papers.ProdFormSpec21.MainResults

open scoped BigOperators InnerProductSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

/-- **Corollary 1 decomposition, constructed.**  For a unit vector `φ`
and an arbitrary vector `ψ`, the residual `ψ - ⟪φ, ψ⟫_ℂ • φ` is
orthogonal to `φ`, the vector `ψ` is the sum of its `φ`-component and
the residual, and Pythagoras gives
`‖ψ‖² = ‖⟪φ, ψ⟫_ℂ‖² + ‖ψ - ⟪φ, ψ⟫_ℂ • φ‖²` in the Euclidean norm. -/
theorem orthogonal_residual_decomposition (φ ψ : E) (hφ : ‖φ‖ = 1) :
    ⟪φ, ψ - ⟪φ, ψ⟫_ℂ • φ⟫_ℂ = 0 ∧
      ψ = ⟪φ, ψ⟫_ℂ • φ + (ψ - ⟪φ, ψ⟫_ℂ • φ) ∧
      ‖ψ‖ ^ 2 = ‖⟪φ, ψ⟫_ℂ‖ ^ 2 + ‖ψ - ⟪φ, ψ⟫_ℂ • φ‖ ^ 2 := by
  have hself : ⟪φ, φ⟫_ℂ = 1 := by
    rw [inner_self_eq_norm_sq_to_K, hφ]
    norm_num
  have horth : ⟪φ, ψ - ⟪φ, ψ⟫_ℂ • φ⟫_ℂ = 0 := by
    rw [inner_sub_right, inner_smul_right, hself, mul_one, sub_self]
  refine ⟨horth, by abel, ?_⟩
  have horth' : ⟪⟪φ, ψ⟫_ℂ • φ, ψ - ⟪φ, ψ⟫_ℂ • φ⟫_ℂ = 0 := by
    rw [inner_smul_left, horth, mul_zero]
  have hpyth := norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero
    (⟪φ, ψ⟫_ℂ • φ) (ψ - ⟪φ, ψ⟫_ℂ • φ) horth'
  have hdecomp : ⟪φ, ψ⟫_ℂ • φ + (ψ - ⟪φ, ψ⟫_ℂ • φ) = ψ := by abel
  rw [hdecomp] at hpyth
  simpa only [pow_two, norm_smul, hφ, mul_one] using hpyth

/-- **Corollary 1, Eq. (17) fidelity branches.**  For unit vectors `φ`
and `ψ`, if the Euclidean residual norm is bounded by both
`h * δt / lam` and `L * h * δt ^ 2` (the two Lemma 1 / Appendix A
residual estimates), then the fidelity defect
`1 - ‖⟪φ, ψ⟫_ℂ‖²` is bounded by the minimum of the two squared scales
`(h * δt / lam)²` and `(L * h * δt ^ 2)²`. -/
theorem fidelity_defect_le_min_of_residual_le (φ ψ : E)
    (hφ : ‖φ‖ = 1) (hψ : ‖ψ‖ = 1)
    (h δt lam : ℝ) (L : ℕ) (_hlam : 0 < lam) (_hL : 0 < L)
    (hres₁ : ‖ψ - ⟪φ, ψ⟫_ℂ • φ‖ ≤ h * δt / lam)
    (hres₂ : ‖ψ - ⟪φ, ψ⟫_ℂ • φ‖ ≤ L * h * δt ^ 2) :
    1 - ‖⟪φ, ψ⟫_ℂ‖ ^ 2 ≤
      min ((h * δt / lam) ^ 2) ((L * h * δt ^ 2) ^ 2) := by
  obtain ⟨_, _, hpyth⟩ := orthogonal_residual_decomposition φ ψ hφ
  have hdef : 1 - ‖⟪φ, ψ⟫_ℂ‖ ^ 2 = ‖ψ - ⟪φ, ψ⟫_ℂ • φ‖ ^ 2 := by
    rw [hψ] at hpyth
    linarith
  rw [hdef]
  apply le_min
  · exact pow_le_pow_left₀ (norm_nonneg _) hres₁ 2
  · exact pow_le_pow_left₀ (norm_nonneg _) hres₂ 2

/-- **Finite accumulation of real phase increments.** If each of `L`
successive phase increments `θ j` satisfies `|θ j| ≤ h * δt ^ 2`, then
the accumulated phase satisfies `|∑ j, θ j| ≤ L * h * δt ^ 2`, by the
triangle inequality over the finite index set `Fin L`. -/
theorem phase_sum_abs_le (L : ℕ) (_hL : 0 < L) (h δt : ℝ)
    (θ : Fin L → ℝ) (hθ : ∀ j, |θ j| ≤ h * δt ^ 2) :
    |∑ j, θ j| ≤ (L : ℝ) * h * δt ^ 2 := by
  calc |∑ j, θ j| ≤ ∑ j, |θ j| := Finset.abs_sum_le_sum_abs θ Finset.univ
    _ ≤ ∑ _j : Fin L, (h * δt ^ 2) :=
        Finset.sum_le_sum fun j _ => hθ j
    _ = (L : ℝ) * (h * δt ^ 2) := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    _ = (L : ℝ) * h * δt ^ 2 := by ring

end Qatlib.Papers.ProdFormSpec21.MainResults
