/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.WalkSearch.MnrsAmplify.Lemma1Stat

open scoped Real

variable {W : Type*} [NormedAddCommGroup W] [InnerProductSpace ℂ W] [FiniteDimensional ℂ W]

namespace Qatlib.Concepts.WalkSearch.MnrsAmplify

noncomputable def unmarkedPart (M : Submodule ℂ W) (ψ : W) : W :=
  ψ - (M.subtypeL.comp M.orthogonalProjection) ψ

noncomputable def leftoverState (M : Submodule ℂ W) (ψ : W) : W :=
  (‖unmarkedPart M ψ‖⁻¹) • unmarkedPart M ψ

noncomputable def attemptState (M : Submodule ℂ W)
    (A : ℕ → (W ≃ₗᵢ[ℂ] W)) (x₀ : W) : ℕ → W
  | 0 => x₀
  | i + 1 => leftoverState M ((A (i + 1)) (attemptState M A x₀ i))

noncomputable def tolerantSuccess (M : Submodule ℂ W)
    (A : ℕ → (W ≃ₗᵢ[ℂ] W)) (x₀ : W) (nMax : ℕ) : ℝ :=
  1 - (1 - markedMass M x₀) *
    ∏ i ∈ Finset.Icc 1 nMax,
      (1 - markedMass M ((A i) (attemptState M A x₀ (i - 1))))
end Qatlib.Concepts.WalkSearch.MnrsAmplify
