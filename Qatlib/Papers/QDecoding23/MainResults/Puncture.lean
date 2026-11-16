/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

@[expose] public section


set_option autoImplicit false

namespace Qatlib.Papers.QDecoding23.MainResults

open Matrix
open scoped BigOperators

/-- An invertible selected generator submatrix reconstructs the original encoded
word from its selected coordinates, by cancellation of that submatrix. -/
theorem prop5_consistency {𝔽 : Type} [Field 𝔽]
    {k n : ℕ} (G : Matrix (Fin k) (Fin n) 𝔽) (s : Fin k → 𝔽) (σ : Fin k → Fin n)
    (hdet : (G.submatrix id σ).det ≠ 0) :
    let c : Fin n → 𝔽 := fun j => ∑ i, s i * G i j
    let cJ : Fin k → 𝔽 := fun i => c (σ i)
    let Ginv : Matrix (Fin k) (Fin k) 𝔽 := (G.submatrix id σ)⁻¹
    c = fun j => ∑ i, (∑ i', cJ i' * Ginv i' i) * G i j := by
  dsimp
  change s ᵥ* G = ((s ᵥ* (G.submatrix id σ)) ᵥ* (G.submatrix id σ)⁻¹) ᵥ* G
  have hc : (s ᵥ* G.submatrix id σ) ᵥ* (G.submatrix id σ)⁻¹ = s := by
    rw [Matrix.vecMul_vecMul, Matrix.mul_nonsing_inv _ (IsUnit.mk0 _ hdet),
      Matrix.vecMul_one]
  rw [hc]

end Qatlib.Papers.QDecoding23.MainResults
