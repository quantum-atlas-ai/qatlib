/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.GradientOracle.C2GradientAlg.NumericalGradientAlgorithmFast
import Mathlib.Data.Real.Sqrt
import Mathlib.Tactic
set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false

noncomputable section

namespace Qatlib.Papers.QBasinHopping05.MainResults

open Qatlib.Concepts.GradientOracle.C2GradientAlg
open Qatlib.Concepts.GradientOracle.ReadoutWindow
open Qatlib.Foundations.QueryWordCore.Circuit

def classicalCentralDifferenceEvaluations (p : ℕ) : ℕ := 2 * p

def quantumGradientEvaluations (_p : ℕ) : ℕ := 1

def basinHopperEffort (basins iterations gradientEvaluations : ℕ) : ℝ :=
  Real.sqrt (basins : ℝ) * (iterations : ℝ) * (gradientEvaluations : ℝ)

theorem quantum_beats_classical (p : ℕ) (hp : 1 ≤ p) :
    quantumGradientEvaluations p < classicalCentralDifferenceEvaluations p := by
  unfold quantumGradientEvaluations classicalCentralDifferenceEvaluations
  omega

theorem dimension_factor_acceleration (basins iterations p : ℕ) :
    basinHopperEffort basins iterations (classicalCentralDifferenceEvaluations p)
      = (2 * p : ℕ) * basinHopperEffort basins iterations (quantumGradientEvaluations p) := by
  unfold basinHopperEffort classicalCentralDifferenceEvaluations quantumGradientEvaluations
  push_cast
  ring

theorem quantum_effort_lt_classical (basins iterations p : ℕ)
    (hb : 0 < basins) (hi : 0 < iterations) (hp : 1 ≤ p) :
    basinHopperEffort basins iterations (quantumGradientEvaluations p)
      < basinHopperEffort basins iterations (classicalCentralDifferenceEvaluations p) := by
  unfold basinHopperEffort quantumGradientEvaluations classicalCentralDifferenceEvaluations
  push_cast
  have hb0 : (0 : ℝ) < Real.sqrt (basins : ℝ) :=
    Real.sqrt_pos.mpr (by exact_mod_cast hb)
  have hi0 : (0 : ℝ) < (iterations : ℝ) := by exact_mod_cast hi
  have hp2 : (1 : ℝ) < 2 * (p : ℝ) := by
    have hp1 : (1 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp
    linarith
  have hpos : (0 : ℝ) < Real.sqrt (basins : ℝ) * (iterations : ℝ) := mul_pos hb0 hi0
  have h := mul_lt_mul_of_pos_left hp2 hpos

  simpa [mul_comm, mul_assoc, mul_left_comm] using! h

theorem quantum_gradient_single_query :
    ∀ (d M Q n_o : ℕ) (hM : 0 < M) [NeZero Q], 2 ≤ M → Q = 2 ^ n_o → 0 < n_o →
      ∀ (f : EuclideanSpace ℝ (Fin d) → ℝ) (x : EuclideanSpace ℝ (Fin d))
        (H h w : ℝ),
        ContDiff ℝ 2 f → 0 ≤ H → (∀ y, ‖fderiv ℝ (fderiv ℝ f) y‖ ≤ H) →
        0 < h → 0 < w → w ≤ 1 / 8 →
        (∀ j : Fin d, |(fderiv ℝ f x) (EuclideanSpace.single j 1)| ≤ 1 / 4) →
        QueryCount (gradientValueProgram d M Q) = 1 := by
  intro d M Q n_o hM hNe hM2 hQ hn f x H h w hf hH hessian hh hw0 hw hg
  exact (@numericalGradientAlgorithm d M Q n_o hM hNe hM2 hQ hn
    f x H h w hf hH hessian hh hw0 hw hg).2.1

end Qatlib.Papers.QBasinHopping05.MainResults
