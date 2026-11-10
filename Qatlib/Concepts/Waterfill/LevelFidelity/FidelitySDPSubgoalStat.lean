/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.Waterfill.LevelFidelity.FidelitySDPProgram
set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false
open Qatlib.Concepts.Waterfill.LevelFidelity.WaterLevelFidelity

namespace Qatlib.Concepts.Waterfill.LevelFidelity
open scoped BigOperators ComplexOrder

def SourceFidelitySDPSubgoal : Prop :=
  ∀ (m : ℕ) (π σ : Fin m → ℚ) (γlo γhi : ℝ),
    (∀ i, 0 ≤ π i) → (∀ i, 0 < σ i) →
    (∑ i, (π i : ℝ) ^ 2) = 1 → (∑ i, (σ i : ℝ) ^ 2) = 1 →
    γlo < γhi →
    (∀ i, 0 < π i → γlo * (σ i : ℝ) ≤ (π i : ℝ)) →
    (∃ i₀, 0 < π i₀ ∧ γlo * (σ i₀ : ℝ) = (π i₀ : ℝ)) →
    (∀ i, (π i : ℝ) ≤ γhi * (σ i : ℝ)) →
    (∃ i₁, 0 < π i₁ ∧ (π i₁ : ℝ) = γhi * (σ i₁ : ℝ)) →
    ∀ p : ℝ, waterPmin π σ ≤ p → p ≤ waterPmax π σ →
      ∃ gbar : ℝ, γlo ≤ gbar ∧ gbar ≤ γhi ∧
        levelDot π σ gbar ^ 2 = p * levelMass π σ gbar ∧
        let E := sourceWaterMatrix π σ gbar
        E.PosSemidef ∧
        (∀ i, (E i i).re ≤ (π i : ℝ) ^ 2) ∧
        (Matrix.trace E).re = levelMass π σ gbar ∧
        (∑ i, ∑ j, (σ i : ℂ) * E i j * (σ j : ℂ)).re =
          p * (Matrix.trace E).re ∧
        (∀ M : Matrix (Fin m) (Fin m) ℂ,
          M.PosSemidef → (∀ i, (M i i).re ≤ (π i : ℝ) ^ 2) →
          p * (Matrix.trace M).re ≤
            (∑ i, ∑ j, (σ i : ℂ) * M i j * (σ j : ℂ)).re →
          (Matrix.trace M).re ≤ levelMass π σ gbar)

end Qatlib.Concepts.Waterfill.LevelFidelity
