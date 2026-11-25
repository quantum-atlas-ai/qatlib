/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Papers.SpectralGap11.MainResults.Optimality
public import Qatlib.Papers.SpectralGap11.MainResults.Stoquastic

@[expose] public section

set_option autoImplicit false
set_option warningAsError true

namespace QatlibTests.SpectralGap11Thm23Regression

open Qatlib.Papers.SpectralGap11.MainResults
open Qatlib.Papers.SpectralGap11.MainResults
open Matrix

/-- The ordinary-module consumer sees the uniform Theorem 2 bound: `1/2` is
fixed outside the gap quantifiers, and the upper factor is the hypothesis `κ`. -/
theorem theorem2_consumer :
    ∃ c₁ : ℝ, c₁ = 1 / 2 ∧ 0 < c₁ ∧
      ∀ Δ Δ' κ q : ℝ, QuantitativeBlackBoxOptimalGap Δ Δ' κ q →
        c₁ * Real.sqrt Δ ≤ Δ' ∧ Δ' ≤ κ * Real.sqrt Δ :=
  source_theorem2_quantitative

/-- The diagonal family is a stoquastic one-sparse spectral example. Its gap is
`1/M`, which is not the paper's `Θ(M^{-1/2})` lattice scaling. -/
theorem theorem3_diagonal_consumer :
    ∃ (M : ℕ) (x : Fin M), 1 < M ∧
      Stoquastic (diagonalStoquastic x) ∧
      OneSparse (diagonalStoquastic x) ∧
      diagonalStoquastic x *ᵥ markedBasis x = 0 ∧
      markedBasis x ≠ 0 ∧
      ∀ y, y ≠ x →
        diagonalStoquastic x *ᵥ markedBasis y =
          (M : ℝ)⁻¹ • markedBasis y := by
  refine ⟨2, 0, by norm_num, diagonalStoquastic_stoquastic 0,
    diagonalStoquastic_oneSparse 0, diagonalStoquastic_ground 0,
    markedBasis_ne_zero 0, ?_⟩
  intro y hy
  simpa using diagonalStoquastic_excited 0 y hy

/-- The ordinary-module consumer sees the conditional algebraic comparison and
not a claim that this comparison obstructs amplification of the diagonal family. -/
theorem theorem3_conditional_consumer (Δ Δ' κ q : ℝ)
    (hmodel : ConditionalSqrtBudget Δ Δ' κ q) :
    Δ' ≤ κ * Real.sqrt Δ :=
  conditional_sqrt_budget Δ Δ' κ q hmodel

end QatlibTests.SpectralGap11Thm23Regression
