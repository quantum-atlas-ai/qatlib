/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords.ShiftedEncodingModel
import Mathlib.Algebra.BigOperators.Fin
import Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords.Neumann.ShiftCoefficients
import Qatlib.Concepts.MatrixAccess.MatrixBackend.NativeWords.RationalCircle
import Qatlib.Concepts.MatrixAccess.MatrixBackend.NativeWords.HouseholderRotationTable
import Qatlib.Concepts.MatrixContour.ContourCalc.ContourModel

set_option backward.isDefEq.respectTransparency false

open Qatlib.Concepts.BlockEncoding
open Qatlib.Concepts.BlockEncoding.EncodingCore

/-!
# Exact laws for the literal padded shift coefficients

The padding is a pair of opposite identity coefficients.  It contributes its
entire nonnegative slack to the coefficient mass and cancels from the actual
matrix sum.  The algebraic sum identity requires no validity guard, inverse,
unitarity, or supplied compression, and includes empty matrix workspaces.
-/

set_option autoImplicit false
set_option maxHeartbeats 3000000

namespace Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords
open Qatlib.Concepts.MatrixAccess.MatrixBackend.NativeWords Qatlib.Foundations.OpCalculus.ContourCalc Qatlib.Concepts.MatrixContour.ContourCalc Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords



open scoped BigOperators Matrix.Norms.L2Operator



/-- G22: the literal coefficient table has the frozen mass and complete
whole-workspace matrix identity for every square matrix. -/
theorem shifted_coefficient_laws (z : ℂ) (α B₀ : ℝ)
    (hα : 0 ≤ α) (hbound : α + ‖z‖ ≤ B₀) :
    coefficientMass (Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords.Neumann.Shifts.shiftCoefficient z α B₀) = B₀ ∧
    ∀ (H : Type) [Fintype H] [DecidableEq H] (U : Matrix H H ℂ),
      (∑ s : Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords.Neumann.Shifts.ShiftSlot, Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords.Neumann.Shifts.shiftCoefficient z α B₀ s • Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords.Neumann.Shifts.shiftSlotMatrix U s) =
        z • (1 : Matrix H H ℂ) - (α : ℂ) • U := by
  refine ⟨Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords.Neumann.Shifts.shift_coefficient_mass z α B₀ hα hbound, ?_⟩
  intro H _ _ U
  exact Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords.Neumann.Shifts.shifted_coefficient_sum z α B₀ H U

end Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords
