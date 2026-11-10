/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.QspSimulation.Achievability.AchievableSufficiencyRestrictedStat
set_option warningAsError false
set_option backward.isDefEq.respectTransparency false


open Qatlib.Concepts.QsvtCore.PhaseExistence

namespace Qatlib.Concepts.QspSimulation.Achievability

open Polynomial

def QspCompilationRestricted : Prop :=
  ∀ (N : ℕ) (h : ℝ → ℝ) (A Qt : Polynomial ℝ) (ε : ℝ),
    Even N → 0 < N →

    (∀ θ : ℝ, h (-θ) = -h θ) → (∀ θ : ℝ, h (θ + 2 * Real.pi) = h θ) →
    A.comp (-X) = A → Qt.comp (-X) = -Qt →
    A.degree ≤ (N : WithBot ℕ) → Qt.degree < (N : WithBot ℕ) →

    (0 < ε → ε ≤ 1/16 →
      (∀ θ ∈ Set.Icc 0 (2 * Real.pi),
        ‖((realEval A (Complex.ofReal (Real.cos (θ/2))))
            + Complex.I * ((Real.sin (θ/2) : ℝ) : ℂ) * (realEval Qt (Complex.ofReal (Real.cos (θ/2))))
            - Complex.exp (Complex.I * (h θ : ℂ)))‖ ≤ ε) →
      ∃ (γ₀ γ₁ : ℝ) (psis : List ℝ), psis.length + 1 = N ∧
        ∀ x ∈ Set.Icc (-1 : ℝ) 1,
          ‖(lcRepoAmp γ₀ γ₁ psis x -
            Complex.exp (Complex.I * (h (2 * Real.arccos x) : ℂ)))‖ ≤ 8 * ε ∧
          (lcRepoAmp γ₀ γ₁ psis x).re * (lcRepoAmp γ₀ γ₁ psis x).re
            + (lcRepoAmp γ₀ γ₁ psis x).im * (lcRepoAmp γ₀ γ₁ psis x).im ≥ (1 - 8 * ε) ^ 2 ∧
          (lcRepoAmp γ₀ γ₁ psis x).re * (lcRepoAmp γ₀ γ₁ psis x).re
            + (lcRepoAmp γ₀ γ₁ psis x).im * (lcRepoAmp γ₀ γ₁ psis x).im ≥ 1 - 16 * ε)

end Qatlib.Concepts.QspSimulation.Achievability
