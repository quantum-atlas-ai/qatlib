/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Foundations.MatrixAlgebra.CliffordWalk.Euler

/-! # Actual Clifford-generator rotations and their native exponentials -/
set_option autoImplicit false
set_option maxHeartbeats 1200000
noncomputable section
open Matrix
open scoped Matrix.Norms.L2Operator
namespace Qatlib.Foundations.MatrixAlgebra.CliffordWalk

open Qatlib.Foundations.MatrixAlgebra.CliffordWalk

/-! The zero-angle instance is an executable identity for clients that need to
reset a Clifford rotation without unfolding the matrix exponential. -/

/-- A physical Clifford rotation at zero angle is exactly the identity. -/
theorem rotation_zero {I : Type*} [Fintype I] [DecidableEq I]
    (P : Matrix I I ℂ) (hP : P * P = 1) : rotation P 0 = 1 := by
  rw [rotation_euler P hP 0]
  simp


end Qatlib.Foundations.MatrixAlgebra.CliffordWalk
