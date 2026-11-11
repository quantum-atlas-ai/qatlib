/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.MatrixContour.ResidueFormula.CircleCauchy

/-! An actual one-pole circular-contour consumer for source Lemma 1. -/
set_option autoImplicit false
open scoped Matrix.Norms.L2Operator
namespace Qatlib.Papers.ContourSim25.ContourSeries
/-- Source Lemma 1 on a positively oriented circle with one simple pole and an
analytic matrix numerator. General contours and infinite pole families remain goals. -/
theorem matrix_simple_pole_cauchy {I : Type} [Fintype I] [DecidableEq I]
    {c w : ℂ} {R : ℝ} {f : ℂ → Matrix I I ℂ}
    (hf : DiffContOnCl ℂ f (Metric.ball c R)) (hw : w ∈ Metric.ball c R) :
    (∮ z in C(c,R), (z-w)⁻¹ • f z) = (2*Real.pi*Complex.I : ℂ) • f w :=
  Qatlib.Concepts.MatrixContour.ResidueFormula.matrix_simple_pole_cauchy hf hw
end Qatlib.Papers.ContourSim25.ContourSeries
