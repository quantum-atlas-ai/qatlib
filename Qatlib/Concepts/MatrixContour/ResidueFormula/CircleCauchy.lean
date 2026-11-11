/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.CStarAlgebra.Matrix
/-!
# Matrix-valued Cauchy on a circle

An actual restricted consumer for source Lemma 1. It treats holomorphic
matrix functions with one simple pole on a positively oriented circle; it
does not assume the unproved infinite-contour or time-ordered series identity.
-/
set_option autoImplicit false
open Filter
open scoped Topology ComplexConjugate Matrix.Norms.L2Operator
namespace Qatlib.Concepts.MatrixContour.ResidueFormula
/-- Banach-valued Cauchy immediately specializes to actual matrix simple-pole integrals. -/
theorem matrix_simple_pole_cauchy {I : Type} [Fintype I] [DecidableEq I]
    {c w : ℂ} {R : ℝ} {f : ℂ → Matrix I I ℂ}
    (hf : DiffContOnCl ℂ f (Metric.ball c R)) (hw : w ∈ Metric.ball c R) :
    (∮ z in C(c,R), (z-w)⁻¹ • f z) = (2*Real.pi*Complex.I : ℂ) • f w :=
  hf.circleIntegral_sub_inv_smul hw
end Qatlib.Concepts.MatrixContour.ResidueFormula
