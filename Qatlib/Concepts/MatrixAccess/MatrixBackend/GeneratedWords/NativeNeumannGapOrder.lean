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
/-! Order bound needed when comparing inverse-based defect polynomials. -/
set_option autoImplicit false
noncomputable section

namespace Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords
open Qatlib.Concepts.MatrixAccess.MatrixBackend.NativeWords Qatlib.Foundations.OpCalculus.ContourCalc Qatlib.Concepts.MatrixContour.ContourCalc Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords

open Matrix Qatlib
open scoped Matrix.Norms.L2Operator MatrixOrder ComplexOrder

noncomputable local instance {I : Type} [Fintype I] [DecidableEq I] :
    CStarAlgebra (Matrix I I ℂ) where

variable {I : Type} [Fintype I] [DecidableEq I]

/-- For a contraction, the complement of every left-defect power is also a
contraction. This includes exponent zero and the empty data space. -/
theorem leftDefect_power_complement_norm_le_one (X : Matrix I I ℂ)
    (hX : ‖X‖ ≤ 1) (b : ℕ) : ‖1 - (1 - X * Xᴴ)^b‖ ≤ 1 := by
  let D : Matrix I I ℂ := 1 - X * Xᴴ
  have hp : 0 ≤ X * Xᴴ := (Matrix.posSemidef_self_mul_conjTranspose X).nonneg
  have hn : ‖X * Xᴴ‖ ≤ 1 := by
    have h := Matrix.l2_opNorm_conjTranspose_mul_self Xᴴ
    simp only [Matrix.conjTranspose_conjTranspose, Matrix.l2_opNorm_conjTranspose] at h
    rw [h]
    nlinarith [norm_nonneg X]
  have hle : X * Xᴴ ≤ 1 :=
    (CStarAlgebra.norm_le_one_iff_of_nonneg (X * Xᴴ) hp).mp hn
  have hD : 0 ≤ D := sub_nonneg.mpr hle
  have hDle : D ≤ 1 := sub_le_self _ hp
  have hDb : 0 ≤ D^b := CStarAlgebra.pow_nonneg D b hD
  have hDble : D^b ≤ 1 := by
    have h := CStarAlgebra.pow_antitone hDle hD (show 0 ≤ b from Nat.zero_le b)
    simpa using h
  have hc : 0 ≤ 1 - D^b := sub_nonneg.mpr hDble
  exact (CStarAlgebra.norm_le_one_iff_of_nonneg (1 - D^b) hc).mpr (sub_le_self _ hDb)

end Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords
