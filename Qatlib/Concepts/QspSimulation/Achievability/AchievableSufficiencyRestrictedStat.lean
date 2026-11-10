/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.QsvtCore.PhaseExistence.Lc17Support
set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

open Qatlib.Concepts.QsvtCore.PhaseExistence

namespace Qatlib.Concepts.QspSimulation.Achievability

open Polynomial

def AchievableSufficiencyRestricted : Prop :=
  ∀ (d : ℕ) (A Qt : Polynomial ℝ), Even d → 0 < d →

    A.comp (-X) = A →

    Qt.comp (-X) = -Qt →
    A.degree ≤ (d : WithBot ℕ) → Qt.degree < (d : WithBot ℕ) →

    (∀ x ∈ Set.Icc (-1 : ℝ) 1,
      A.eval x * A.eval x + (1 - x * x) * (Qt.eval x * Qt.eval x) ≤ 1) →

    A.eval 1 = 1 →
    ∃ (γ₀ γ₁ : ℝ) (psis : List ℝ), psis.length + 1 = d ∧
      ∀ x ∈ Set.Icc (-1 : ℝ) 1,
        lcRepoAmp γ₀ γ₁ psis x =
          realEval A (Complex.ofReal x) + Complex.I * ((Real.sqrt (1 - x * x) : ℝ) : ℂ) * realEval Qt (Complex.ofReal x)

end Qatlib.Concepts.QspSimulation.Achievability
