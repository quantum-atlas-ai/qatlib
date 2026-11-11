/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Lean.Elab.Tactic.NormCast
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Qatlib.Concepts.EstimatorLaws.TvStability.SeparationCorRestrictedSubgoalStat
import Qatlib.Concepts.AmplitudeCore.PhaseEstimation.Lemma7Quan

/-!
# Restricted amplitude separation bound

Proves the restricted squared-sine perturbation bound obtained by shifting an angle by one
phase-grid step. It applies the existing angle-error estimate to the displacement `π / M`,
providing the amplitude-error comparison used in the estimation analysis of [Montanaro2015].

## Main statements

* `separationCorollaryRestrictedSubgoal` bounds the amplitude change by `2 * ε * sqrt (a * (1 -
  a)) + ε²` when `π / M ≤ ε`.

## References

* [Montanaro, 2015][Montanaro2015]
-/

open Qatlib.Concepts.AmplitudeCore.PhaseEstimation

namespace Qatlib.Concepts.EstimatorLaws.TvStability

/-- Proves the restricted amplitude-error bound for the shift `θ ↦ θ + π / M`, with `a = sin²
θ`, `0 ≤ θ ≤ π`, and `π / M ≤ ε`. The conclusion is the squared-sine perturbation estimate
used in the amplitude-estimation analysis of [Montanaro2015]. -/
theorem separationCorollaryRestrictedSubgoal : SeparationCorollaryRestrictedSubgoal := by
  intro a θ M hM ha hθ hθπ ε hε hεM
  have hMpos : (0 : ℝ) < M := by exact_mod_cast hM
  have hπMnn : 0 ≤ Real.pi / M := div_nonneg Real.pi_nonneg (Nat.cast_nonneg M)
  have hπM_le : Real.pi / M ≤ Real.pi := by
    rw [div_le_iff₀ hMpos]
    exact le_mul_of_one_le_right Real.pi_nonneg (by exact_mod_cast hM)
  have hdispl : |θ + Real.pi / M - θ| ≤ ε := by
    rw [show θ + Real.pi / M - θ = Real.pi / M from by ring, abs_of_nonneg hπMnn]
    exact hεM
  exact zoo_amplitude_estimation_angle_error a (Real.sin (θ + Real.pi / M) ^ 2) θ
    (θ + Real.pi / M) ε ha rfl hθ (by linarith [Real.pi_nonneg, hθπ])
    (add_nonneg hθ hπMnn) (by linarith [Real.pi_nonneg, hθπ, hπM_le]) hε.le hdispl

end Qatlib.Concepts.EstimatorLaws.TvStability
