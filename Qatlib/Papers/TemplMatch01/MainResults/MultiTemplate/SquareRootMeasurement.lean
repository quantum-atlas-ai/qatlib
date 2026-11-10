/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.MixedFidelity.FidelityMetric.MixedFidelityDefs
set_option warningAsError false

namespace Qatlib.Papers.TemplMatch01.MainResults.MultiTemplate

open Qatlib.Foundations.PureStateMath
open Matrix BigOperators
open scoped ComplexOrder MatrixOrder Matrix

set_option autoImplicit false

variable {d M : ℕ}

noncomputable def squareRootEffect (W : Operator d) (v : Fin d → ℂ) : Operator d :=
  W * Matrix.vecMulVec v (star v) * W

theorem squareRootMeasurement_isPOVM
    (W G : Operator d) (v : Fin M → Fin d → ℂ) (hW : Wᴴ = W)
    (hG : G = ∑ m, Matrix.vecMulVec (v m) (star (v m)))
    (hWG : W * G * W = 1) :
    (∑ m, squareRootEffect W (v m)) = 1 ∧
      ∀ m, (squareRootEffect W (v m)).PosSemidef := by
  constructor
  · have hsum : (∑ m, squareRootEffect W (v m))
        = W * (∑ m, Matrix.vecMulVec (v m) (star (v m))) * W := by
      simp only [squareRootEffect]
      rw [Matrix.mul_sum, Matrix.sum_mul]
    rw [hsum, ← hG, hWG]
  · intro m
    have hP : (Matrix.vecMulVec (v m) (star (v m))).PosSemidef :=
      Matrix.posSemidef_vecMulVec_self_star _
    have h := hP.mul_mul_conjTranspose_same W
    simpa [squareRootEffect, hW] using h

end Qatlib.Papers.TemplMatch01.MainResults.MultiTemplate
