/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.QsvtCore.PhaseExistence.Lc17Support

/-!
# Restricted polynomial realizability statement

This module states a sufficient condition for realizing an amplitude of the form an even
polynomial plus an imaginary square-root factor times an odd polynomial. For a positive even
degree parameter, the hypotheses impose degree bounds, a weighted squared-norm bound on the
interval from minus one to one, and endpoint normalization. The target phase representation uses
the QSP convention of [LowChuang2017].

## Main statements

* `AchievableSufficiencyRestricted` requires existence of endpoint phases and a phase list of
  length one less than the degree parameter, with amplitude equal to the prescribed expression
  throughout the interval.

## References

* [Low and Chuang, 2017][LowChuang2017], *Optimal Hamiltonian Simulation by Quantum Signal
  Processing*.
-/

set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

open Qatlib.Concepts.QsvtCore.PhaseExistence

namespace Qatlib.Concepts.QspSimulation.Achievability

open Polynomial

/-- For positive even `d`, specifies phase realizability of an even polynomial `A` and odd
polynomial `Qt` with degrees at most `d` and strictly below `d`, respectively, when their
weighted squared sum is at most one on the interval from minus one to one and `A.eval 1 =
1`. The resulting `lcRepoAmp` equals the prescribed complex amplitude throughout that
interval, using a phase list of length `d - 1`. -/
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
