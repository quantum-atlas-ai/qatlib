/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.WalkSearch.MnrsAmplify.Lemma1Stat

/-!
# States and success for tolerant amplification

Defines the unmarked remainder, normalized attempt recursion, and cumulative success value for
tolerant amplitude amplification in [MagniezNayakRolandSantha2011]. `tolerantSuccess` includes
the initial marked-state test and the subsequent tests after applying the supplied family of
isometries.

## Main statements

* `attemptState`: The sequence starting at `x₀` and recursively applying `A (i + 1)` followed by
  normalization of the unmarked component.
* `tolerantSuccess`: One minus the product of the initial and subsequent failure factors, using
  the marked masses of the states in the tolerant attempt recursion.

## References

* [Magniez et al., 2011][MagniezNayakRolandSantha2011]
-/

open scoped Real

variable {W : Type*} [NormedAddCommGroup W] [InnerProductSpace ℂ W] [FiniteDimensional ℂ W]

namespace Qatlib.Concepts.WalkSearch.MnrsAmplify

/-- The component of `ψ` remaining after subtracting its orthogonal projection onto the marked
subspace `M`. -/
noncomputable def unmarkedPart (M : Submodule ℂ W) (ψ : W) : W :=
  ψ - (M.subtypeL.comp M.orthogonalProjection) ψ

/-- The unmarked component of `ψ`, scaled by the reciprocal of its norm; a zero component
remains zero. -/
noncomputable def leftoverState (M : Submodule ℂ W) (ψ : W) : W :=
  (‖unmarkedPart M ψ‖⁻¹) • unmarkedPart M ψ

/-- The sequence starting at `x₀` and recursively applying `A (i + 1)` followed by normalization
of the unmarked component. -/
noncomputable def attemptState (M : Submodule ℂ W)
    (A : ℕ → (W ≃ₗᵢ[ℂ] W)) (x₀ : W) : ℕ → W
  | 0 => x₀
  | i + 1 => leftoverState M ((A (i + 1)) (attemptState M A x₀ i))

/-- One minus the product of the initial and subsequent failure factors, using the marked masses
of the states in the tolerant attempt recursion. -/
noncomputable def tolerantSuccess (M : Submodule ℂ W)
    (A : ℕ → (W ≃ₗᵢ[ℂ] W)) (x₀ : W) (nMax : ℕ) : ℝ :=
  1 - (1 - markedMass M x₀) *
    ∏ i ∈ Finset.Icc 1 nMax,
      (1 - markedMass M ((A i) (attemptState M A x₀ (i - 1))))
end Qatlib.Concepts.WalkSearch.MnrsAmplify
