/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import QuantumInfo.ForMathlib.HermitianMat.Sqrt
import Mathlib.Tactic
set_option warningAsError false

set_option autoImplicit false
noncomputable section
open Matrix
namespace Qatlib.Foundations.MatrixAlgebra.MatrixGram
variable {I : Type} [Fintype I] [DecidableEq I]

def gramFactor (D : Matrix I I ℝ) (hD : D.PosSemidef) : Matrix I I ℝ :=
  (HermitianMat.sqrt (⟨D,hD.isHermitian⟩ : HermitianMat I ℝ)).mat

theorem gramFactor_identity (D : Matrix I I ℝ) (hD : D.PosSemidef) :
    (gramFactor D hD)ᵀ*gramFactor D hD=D := by
  have hs : (gramFactor D hD)ᵀ=gramFactor D hD := by
    simpa only [gramFactor,Matrix.conjTranspose_eq_transpose_of_trivial] using!
      (HermitianMat.sqrt (⟨D,hD.isHermitian⟩ : HermitianMat I ℝ)).H
  rw [hs]
  exact HermitianMat.sqrt_sq (HermitianMat.zero_le_iff.mpr hD)
end Qatlib.Foundations.MatrixAlgebra.MatrixGram
