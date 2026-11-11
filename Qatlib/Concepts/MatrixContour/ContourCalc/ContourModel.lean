/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.MatrixContour.ContourCalc.MatrixResolvent
import Mathlib.Data.Matrix.Block
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Qatlib.Foundations.OpCalculus.ContourCalc.BanachPolynomial

set_option backward.isDefEq.respectTransparency false
open Qatlib.Concepts.MatrixContour.ContourCalc
open Qatlib.Foundations.OpCalculus.ContourCalc

open Qatlib.Concepts.CoherentSim.CoherentOAA

/-! Literal finite models for numerical-range contour consumers. The resolvent
is the actual pseudoinverse target, not a supplied inverse. Local polynomials
are for quadrature error analysis; original-oracle implementations are separate. -/
set_option autoImplicit false
noncomputable section
namespace Qatlib.Concepts.MatrixContour.ContourCalc

open scoped BigOperators Matrix.Norms.L2Operator

/-- The label-first matrix direct sum, obtained by swapping the two block-diagonal indices. -/
def labelBlockDiagonal {I L : Type*} [DecidableEq L] (U : L → Matrix I I ℂ) :
    Matrix (L × I) (L × I) ℂ :=
  (Matrix.blockDiagonal U).submatrix Prod.swap Prod.swap

/-- Construction for matrix Shift in the contour model model. -/
def matrixShift {I : Type*} [Fintype I] [DecidableEq I]
    (A : Matrix I I ℂ) (z : ℂ) : Matrix I I ℂ := z • 1 - A

/-- Construction for matrix Resolvent in the contour model model. -/
def matrixResolvent {I : Type*} [Fintype I] [DecidableEq I]
    (A : Matrix I I ℂ) (z : ℂ) : Matrix I I ℂ := matrixPseudoinverse (matrixShift A z)

/-- Construction for local Resolvent Polynomial in the contour model model. -/
def localResolventPolynomial {I : Type*} [Fintype I] [DecidableEq I]
    (A : Matrix I I ℂ) (z₀ : ℂ) (m : ℕ) (z : ℂ) : Matrix I I ℂ :=
  ∑ n ∈ Finset.range (m + 1), (-(z - z₀)) ^ n • (matrixResolvent A z₀) ^ (n + 1)

/-- Construction for joint Normalized Shift in the contour model model. -/
def jointNormalizedShift {I L : Type*} [Fintype I] [DecidableEq I]
    [Fintype L] [DecidableEq L] (A : Matrix I I ℂ) (z : L → ℂ) (B₀ : ℝ) :
    Matrix (L × I) (L × I) ℂ :=
  labelBlockDiagonal (fun j => ((B₀⁻¹ : ℝ) : ℂ) • matrixShift A (z j))

/-- Construction for joint Matrix Resolvent in the contour model model. -/
def jointMatrixResolvent {I L : Type*} [Fintype I] [DecidableEq I]
    [Fintype L] [DecidableEq L] (A : Matrix I I ℂ) (z : L → ℂ) :
    Matrix (L × I) (L × I) ℂ := labelBlockDiagonal (fun j => matrixResolvent A (z j))

/-- Construction for joint Resolvent Condition in the contour model model. -/
def jointResolventCondition (B₀ r : ℝ) : ℝ := max 2 (B₀ / r)

/-- A straight panel parameterized by real width h. Its derivative is u;
its arclength is h * ‖u‖, which can be smaller than h. -/
def contourPanel (z₀ u : ℂ) (a h t : ℝ) : ℂ :=
  z₀ + ((t - (a + h / 2) : ℝ) : ℂ) * u

end Qatlib.Concepts.MatrixContour.ContourCalc
