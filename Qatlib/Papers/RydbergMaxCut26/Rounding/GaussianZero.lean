/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.RydbergMaxCut26.Rounding.GaussianEndpoints
import Mathlib.Analysis.SpecialFunctions.OrdinaryHypergeometric
set_option warningAsError false

set_option autoImplicit false
noncomputable section
open MeasureTheory ProbabilityTheory

namespace Qatlib.Papers.RydbergMaxCut26.Rounding.GaussianMatrix

def bovThreeKernel (t : ℝ) : ℝ := (8/(3*Real.pi))*t*₂F₁ (1/2:ℝ) (1/2) (5/2) (t^2)

theorem bovThreeKernel_zero : bovThreeKernel 0=0 := by simp [bovThreeKernel]

theorem bov_three_orthogonal {I : Type} [Fintype I] (u v : Row I) (h : inner ℝ u v=0) :
    rawExpectation u v=bovThreeKernel (inner ℝ u v) := by
  rw [rawExpectation_eq,matrixExpectation_orthogonal u v h,h,bovThreeKernel_zero]

end Qatlib.Papers.RydbergMaxCut26.Rounding.GaussianMatrix
