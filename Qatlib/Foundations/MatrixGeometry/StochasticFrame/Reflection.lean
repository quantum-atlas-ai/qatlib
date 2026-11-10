/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Foundations.MatrixGeometry.StochasticFrame.RowFrame
import Mathlib.Analysis.InnerProductSpace.Adjoint

set_option autoImplicit false
noncomputable section
open Matrix
open scoped Classical BigOperators
namespace Qatlib.Foundations.MatrixGeometry.StochasticFrame
variable {M N : Type*} [Fintype M] [Fintype N] [DecidableEq M] [DecidableEq N]
omit [DecidableEq M] in

theorem range_projector_squared (C : Matrix M N ℂ) (hC : Cᴴ*C=1) :
    (C*Cᴴ)*(C*Cᴴ)=C*Cᴴ := by
  calc
    _ = C*(Cᴴ*C)*Cᴴ := by simp only [Matrix.mul_assoc]
    _ = _ := by rw [hC,Matrix.mul_one]

def rangeReflection (C : Matrix M N ℂ) : Matrix M M ℂ := (2 : ℂ) • (C*Cᴴ)-1
omit [Fintype M] [DecidableEq N] in

theorem rangeReflection_adjoint (C : Matrix M N ℂ) : (rangeReflection C)ᴴ=rangeReflection C := by
  simp [rangeReflection,Matrix.conjTranspose_mul]

theorem rangeReflection_squared (C : Matrix M N ℂ) (hC : Cᴴ*C=1) :
    rangeReflection C*rangeReflection C=1 := by
  let A := C*Cᴴ
  have hA : A*A=A := range_projector_squared C hC
  change ((2 : ℂ) • A-1)*((2 : ℂ) • A-1)=1
  simp only [two_smul]
  have he : (A+A-1)*(A+A-1)=A*A+A*A+A*A+A*A-(A+A+A+A)+1 := by noncomm_ring
  rw [he,hA]
  abel

theorem rangeReflection_unitary (C : Matrix M N ℂ) (hC : Cᴴ*C=1) :
    (rangeReflection C)ᴴ*rangeReflection C=1 := by
  rw [rangeReflection_adjoint,rangeReflection_squared C hC]
end Qatlib.Foundations.MatrixGeometry.StochasticFrame
