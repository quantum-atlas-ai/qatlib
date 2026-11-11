/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Foundations.MatrixGeometry.StochasticFrame.RowFrame
import Mathlib.Analysis.InnerProductSpace.Adjoint

/-!
# Reflections from isometric matrix frames

Defines `rangeReflection C` as `2 • (C * Cᴴ) - 1`. For a frame with `Cᴴ * C = 1`, its range
matrix is idempotent and the reflection is a Hermitian involution satisfying the unitary matrix
identity. See [ClaudonPiquemalMonmarche2025] for related background.

## Main statements

* `range_projector_squared`: If `Cᴴ * C = 1`, the range matrix `C * Cᴴ` is idempotent.
* `rangeReflection_unitary`: If `Cᴴ * C = 1`, the adjoint of the range-reflection matrix
  multiplied by that matrix equals the identity.

## References

* [Claudon et al., 2025][ClaudonPiquemalMonmarche2025]
-/

set_option autoImplicit false
noncomputable section
open Matrix
open scoped Classical BigOperators
namespace Qatlib.Foundations.MatrixGeometry.StochasticFrame
variable {M N : Type*} [Fintype M] [Fintype N] [DecidableEq M] [DecidableEq N]
omit [DecidableEq M] in

/-- If `Cᴴ * C = 1`, the range matrix `C * Cᴴ` is idempotent. -/
theorem range_projector_squared (C : Matrix M N ℂ) (hC : Cᴴ*C=1) :
    (C*Cᴴ)*(C*Cᴴ)=C*Cᴴ := by
  calc
    _ = C*(Cᴴ*C)*Cᴴ := by simp only [Matrix.mul_assoc]
    _ = _ := by rw [hC,Matrix.mul_one]

/-- The matrix `2 • (C * Cᴴ) - 1`, giving reflection across the range when `C` is an isometric
frame. -/
def rangeReflection (C : Matrix M N ℂ) : Matrix M M ℂ := (2 : ℂ) • (C*Cᴴ)-1
omit [Fintype M] [DecidableEq N] in

/-- The range-reflection matrix is Hermitian for every complex matrix `C`. -/
theorem rangeReflection_adjoint (C : Matrix M N ℂ) : (rangeReflection C)ᴴ=rangeReflection C := by
  simp [rangeReflection,Matrix.conjTranspose_mul]

/-- If `Cᴴ * C = 1`, the range-reflection matrix squares to the identity. -/
theorem rangeReflection_squared (C : Matrix M N ℂ) (hC : Cᴴ*C=1) :
    rangeReflection C*rangeReflection C=1 := by
  let A := C*Cᴴ
  have hA : A*A=A := range_projector_squared C hC
  change ((2 : ℂ) • A-1)*((2 : ℂ) • A-1)=1
  simp only [two_smul]
  have he : (A+A-1)*(A+A-1)=A*A+A*A+A*A+A*A-(A+A+A+A)+1 := by noncomm_ring
  rw [he,hA]
  abel

/-- If `Cᴴ * C = 1`, the adjoint of the range-reflection matrix multiplied by that matrix equals
the identity. -/
theorem rangeReflection_unitary (C : Matrix M N ℂ) (hC : Cᴴ*C=1) :
    (rangeReflection C)ᴴ*rangeReflection C=1 := by
  rw [rangeReflection_adjoint,rangeReflection_squared C hC]
end Qatlib.Foundations.MatrixGeometry.StochasticFrame
