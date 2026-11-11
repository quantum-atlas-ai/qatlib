/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Analysis.Asymptotics.SpecificAsymptotics
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Sqrt

/-!
# Polynomial circuit-cost models

This module defines explicit polynomial models for one-dimensional and dimension-dependent
Poisson-solver resource counts and controlled rotations. It also relates the accuracy-dependent
grid size `gridSize` to the logarithmic register-size model `registerSize`. These statements
concern the formulas and models in [WangEtAl2020].

## Main statements

* `oneDimQubitsModel` and `oneDimGatesModel`: define the one-dimensional resource polynomials.
* `registerSize_eq_log_gridSize`: expresses register size as a base-two logarithm of grid size.

## References

* [Wang et al., 2020][WangEtAl2020]
-/

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.FastPoisson19.CostModels

/-- The one-dimensional qubit-count model `m^2 + n * m`. -/
def oneDimQubitsModel (m n : ℝ) : ℝ := m ^ 2 + n * m

/-- The one-dimensional gate-count model `68 * m^3 + 66 * n * m^2`. -/
def oneDimGatesModel (m n : ℝ) : ℝ := 68 * m ^ 3 + 66 * n * m ^ 2

/-- The dimension-dependent qubit model, equal to `d` times the one-dimensional qubit model. -/
def dimensionQubitsModel (d m n : ℝ) : ℝ := d * oneDimQubitsModel m n

/-- The amplified dimension-dependent gate model, equal to `kappa * d` times the one-dimensional
gate model. -/
def dimensionGatesModel (d kappa m n : ℝ) : ℝ := kappa * d * oneDimGatesModel m n

/-- The controlled-rotation qubit model `(m^2 + 3 * m) + (m + 1)`. -/
def controlledRotationQubitsModel (m : ℝ) : ℝ := (m ^ 2 + 3 * m) + (m + 1)

/-- The controlled-rotation gate model `(34 * m^3 - 50 * m^2) + 4 * m`. -/
def controlledRotationGatesModel (m : ℝ) : ℝ := (34 * m ^ 3 - 50 * m ^ 2) + 4 * m

/-- The real grid-size model `eps^(-alpha)`. -/
def gridSize (eps alpha : ℝ) : ℝ := eps ^ (-alpha)

/-- The real register-size model `alpha * log (1 / eps) / log 2`. -/
def registerSize (eps alpha : ℝ) : ℝ := alpha * Real.log (1 / eps) / Real.log 2

/-- The classical dimensional model given by the grid size raised to the dimension. -/
def classicalDimensionalModel (eps alpha : ℝ) (d : ℕ) : ℝ :=
  (gridSize eps alpha) ^ (d : ℝ)

/-- The one-dimensional qubit model is nonnegative for nonnegative register parameters. -/
lemma oneDimQubitsModel_nonneg {m n : ℝ} (hm : 0 ≤ m) (hn : 0 ≤ n) :
    0 ≤ oneDimQubitsModel m n := by
  unfold oneDimQubitsModel
  positivity

/-- The one-dimensional gate model is nonnegative for nonnegative register parameters. -/
lemma oneDimGatesModel_nonneg {m n : ℝ} (hm : 0 ≤ m) (hn : 0 ≤ n) :
    0 ≤ oneDimGatesModel m n := by
  unfold oneDimGatesModel
  positivity

/-- The controlled-rotation qubit model is nonnegative for nonnegative `m`. -/
lemma controlledRotationQubitsModel_nonneg {m : ℝ} (hm : 0 ≤ m) :
    0 ≤ controlledRotationQubitsModel m := by
  unfold controlledRotationQubitsModel
  positivity

/-- For positive accuracy parameter, the register-size model is `log (gridSize eps alpha) / log
2`. -/
lemma registerSize_eq_log_gridSize {eps alpha : ℝ} (heps : 0 < eps) :
    registerSize eps alpha = Real.log (gridSize eps alpha) / Real.log 2 := by
  unfold registerSize gridSize
  rw [Real.log_rpow heps]
  have h1 : Real.log (1 / eps) = -Real.log eps := by
    rw [one_div, Real.log_inv]
  rw [h1]
  ring

/-- Unfolds the register-size model as `alpha * log (1 / eps) / log 2`. -/
lemma registerSize_eq_alpha_log_inv {eps alpha : ℝ} (_heps : 0 < eps) :
    registerSize eps alpha = alpha * Real.log (1 / eps) / Real.log 2 := rfl

end Qatlib.Papers.FastPoisson19.CostModels
