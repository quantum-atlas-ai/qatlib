/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Papers.KnottedLight08.NullLinking.MagneticFiberTransport
public import Qatlib.Papers.KnotLight13.TorusFamily.BatemanRayDifferential

public import Mathlib.LinearAlgebra.Determinant
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic

import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Ring

/-!
# Cofactor identity for the magnetic ray map

[IrvineBouwmeester2008KnottedLight], Eq. (2),
[DOI](https://doi.org/10.1038/nphys1056).
The cofactor identity for the cross product gives the algebraic
transformation law for two spatial gradients under the ray map.
-/

@[expose] public section
set_option autoImplicit false

namespace Qatlib.Papers.KnottedLight08.NullLinking

open Qatlib.Papers.KnottedLight08.HopfField (cross3)

/-- Applying a matrix to the cross product of two pulled-back covectors
gives its determinant times the original cross product. -/
theorem mulVec_cross_of_transposed_covectors (M : Matrix (Fin 3) (Fin 3) ℂ)
    (a b : Fin 3 → ℂ) (j : Fin 3) :
    (M.mulVec (cross3 (M.transpose.mulVec a) (M.transpose.mulVec b))) j =
      Matrix.det M * cross3 a b j := by
  fin_cases j <;>
    simp [Matrix.mulVec, dotProduct, cross3, Matrix.det_fin_three, Fin.sum_univ_three] <;> ring

end Qatlib.Papers.KnottedLight08.NullLinking
