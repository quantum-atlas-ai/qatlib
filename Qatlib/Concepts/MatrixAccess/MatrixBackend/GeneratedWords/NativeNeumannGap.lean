/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords.NativeNeumannStability
import Qatlib.Concepts.MatrixAccess.MatrixBackend.NativeWords.RationalCircle
import Qatlib.Concepts.MatrixAccess.MatrixBackend.NativeWords.HouseholderRotationTable
import Qatlib.Concepts.MatrixContour.ContourCalc.ContourModel

set_option backward.isDefEq.respectTransparency false
open Qatlib.Concepts.CoherentSim.CoherentOAA

/-! Stability estimates with a strict defect contraction. -/
set_option autoImplicit false
noncomputable section

namespace Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords
open Qatlib.Concepts.MatrixAccess.MatrixBackend.NativeWords Qatlib.Foundations.OpCalculus.ContourCalc Qatlib.Concepts.MatrixContour.ContourCalc Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords

open Matrix Qatlib
open scoped Matrix.Norms.L2Operator

variable {I : Type} [Fintype I] [DecidableEq I]

/-- A dimension-free noncommutative power perturbation estimate.  This uses
one common strict contraction radius and includes the zeroth power and empty
matrices. -/
theorem l2_norm_pow_sub_pow_le_of_lt_one (U V : Matrix I I ℂ) (r : ℝ)
    (hr : r < 1) (hU : ‖U‖ ≤ r) (hV : ‖V‖ ≤ r) (n : ℕ) :
    ‖U ^ n - V ^ n‖ ≤ ‖U - V‖ / (1-r) := by
  have hr0 : 0 ≤ r := (norm_nonneg U).trans hU
  have hd : 0 ≤ ‖U - V‖ / (1-r) := div_nonneg (norm_nonneg _) (by linarith)
  have heq : (1-r) * (‖U-V‖ / (1-r)) = ‖U-V‖ := by
    have hpos : 0 < 1-r := by linarith
    field_simp [ne_of_gt hpos]
  have hu1 : ‖U‖ ≤ 1 := hU.trans hr.le
  induction n with
  | zero => simp; exact hd
  | succ n ih =>
    rw [pow_succ', pow_succ']
    have hh := Qatlib.Foundations.OperatorErrors.OperatorError.l2_norm_mul_sub_mul_le U (U^n) V (V^n)
    have hpower := Qatlib.Foundations.OperatorErrors.OperatorError.l2_norm_pow_le_one U hu1 n
    have hleft := mul_le_mul_of_nonneg_left hpower (norm_nonneg (U-V))
    have hright := mul_le_mul hV ih (norm_nonneg _) hr0
    nlinarith

end Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords
