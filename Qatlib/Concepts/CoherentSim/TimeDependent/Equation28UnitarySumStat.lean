/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.CoherentSim.TimeDependent.Equation28Stat
set_option warningAsError false
set_option backward.isDefEq.respectTransparency false


namespace Qatlib.Concepts.CoherentSim.TimeDependent

def Equation28UnitarySum : Prop :=
  ∀ (I : Type) [Fintype I] [DecidableEq I] (L : ℕ)
    (α : Fin L → ℝ → ℝ) (Hl : Fin L → Matrix I I ℂ) (H : ℝ → Matrix I I ℂ)
    (τ Λ : ℝ) (M K : ℕ),
    (∀ ℓ, Hl ℓ ∈ Matrix.unitaryGroup I ℂ) →
    (∀ (ℓ : Fin L) (u : ℝ), 0 ≤ α ℓ u) →
    (∀ u ∈ Set.Icc 0 τ, H u = ∑ ℓ, (α ℓ u : ℂ) • Hl ℓ) →
    (∀ u ∈ Set.Icc 0 τ, ∑ ℓ, α ℓ u ≤ Λ) → 0 < M → 0 ≤ τ →
    ∃ (D : Type) (_ : Fintype D) (_ : DecidableEq D) (β : D → ℝ) (V : D → Matrix I I ℂ),
      (∀ d, 0 ≤ β d) ∧ (∀ d, V d ∈ Matrix.unitaryGroup I ℂ) ∧
      equation28Segment H τ M K = ∑ d, (β d : ℂ) • V d ∧
      1 ≤ ∑ d, β d ∧
      ∑ d, β d ≤ ∑ k ∈ Finset.range (K + 1), (Λ * τ) ^ k / (((k.factorial : ℕ) : ℝ))

end Qatlib.Concepts.CoherentSim.TimeDependent
