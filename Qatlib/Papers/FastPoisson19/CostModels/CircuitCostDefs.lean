/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Analysis.Asymptotics.SpecificAsymptotics
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Sqrt

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.FastPoisson19.CostModels

def oneDimQubitsModel (m n : ℝ) : ℝ := m ^ 2 + n * m

def oneDimGatesModel (m n : ℝ) : ℝ := 68 * m ^ 3 + 66 * n * m ^ 2

def dimensionQubitsModel (d m n : ℝ) : ℝ := d * oneDimQubitsModel m n

def dimensionGatesModel (d kappa m n : ℝ) : ℝ := kappa * d * oneDimGatesModel m n

def controlledRotationQubitsModel (m : ℝ) : ℝ := (m ^ 2 + 3 * m) + (m + 1)

def controlledRotationGatesModel (m : ℝ) : ℝ := (34 * m ^ 3 - 50 * m ^ 2) + 4 * m

def gridSize (eps alpha : ℝ) : ℝ := eps ^ (-alpha)

def registerSize (eps alpha : ℝ) : ℝ := alpha * Real.log (1 / eps) / Real.log 2

def classicalDimensionalModel (eps alpha : ℝ) (d : ℕ) : ℝ :=
  (gridSize eps alpha) ^ (d : ℝ)

lemma oneDimQubitsModel_nonneg {m n : ℝ} (hm : 0 ≤ m) (hn : 0 ≤ n) :
    0 ≤ oneDimQubitsModel m n := by
  unfold oneDimQubitsModel
  positivity

lemma oneDimGatesModel_nonneg {m n : ℝ} (hm : 0 ≤ m) (hn : 0 ≤ n) :
    0 ≤ oneDimGatesModel m n := by
  unfold oneDimGatesModel
  positivity

lemma controlledRotationQubitsModel_nonneg {m : ℝ} (hm : 0 ≤ m) :
    0 ≤ controlledRotationQubitsModel m := by
  unfold controlledRotationQubitsModel
  positivity

lemma registerSize_eq_log_gridSize {eps alpha : ℝ} (heps : 0 < eps) :
    registerSize eps alpha = Real.log (gridSize eps alpha) / Real.log 2 := by
  unfold registerSize gridSize
  rw [Real.log_rpow heps]
  have h1 : Real.log (1 / eps) = -Real.log eps := by
    rw [one_div, Real.log_inv]
  rw [h1]
  ring

lemma registerSize_eq_alpha_log_inv {eps alpha : ℝ} (_heps : 0 < eps) :
    registerSize eps alpha = alpha * Real.log (1 / eps) / Real.log 2 := rfl

end Qatlib.Papers.FastPoisson19.CostModels
