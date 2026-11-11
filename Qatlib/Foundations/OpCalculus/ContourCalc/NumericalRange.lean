/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.InnerProductSpace.Basic

/-!
# Numerical-range model for matrix-function contours

The range uses unit vectors in the actual complex inner product space, rather
than a supplied set or a spectral enclosure.  `matrixNumericalRange` uses the
same Euclidean operator representation as the L2 matrix norm and block encodings.
-/
namespace Qatlib.Foundations.OpCalculus.ContourCalc

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

/-- Rayleigh quotients on the unit sphere.  The zero-dimensional range is empty. -/
def numericalRange (A : E →L[ℂ] E) : Set ℂ :=
  {w | ∃ x : E, ‖x‖ = 1 ∧ inner ℂ x (A x) = w}

/-- The shifted operator whose inverse is used by contour LCU. -/
def shiftedOperator (A : E →L[ℂ] E) (z : ℂ) : E →L[ℂ] E :=
  z • ContinuousLinearMap.id ℂ E - A

/-- Numerical range of a finite complex matrix with the Euclidean convention. -/
def matrixNumericalRange {I : Type*} [Fintype I] [DecidableEq I]
    (A : Matrix I I ℂ) : Set ℂ :=
  numericalRange (Matrix.toEuclideanCLM (n := I) (𝕜 := ℂ) A)

end Qatlib.Foundations.OpCalculus.ContourCalc
