/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Matrix.Mul
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.LinearAlgebra.Matrix.Diagonal
import Mathlib.Data.Real.Basic
import Mathlib.Analysis.Complex.Trigonometric
import Mathlib.Tactic

/-!
# Lattice gauge initialization and resource counts

`u5Rot` is the real two-dimensional rotation used in the initialization model, with both
orthogonality identities proved explicitly. The functions `u5ApplyCount`, `u5LocalOpCount`, and
`u5WorstOpCount` record algebraic resource counts and their dependence on lattice size. See
[ByrnesYamamoto2006] for the paper context.

## Main statements

* `u5Rot_orthogonal`: The transpose of `u5Rot φ` multiplied by `u5Rot φ` is the identity.
* `u5_local_op_count_linear`: Increasing `M` by one increases the local initialization operation
  count by `c * d`.
* `u5_worst_is_plaquette_times_qubits`: The worst-case initialization count factors as `(d * M)
  * (D * d * M)`.

## References

* [Byrnes and Yamamoto, 2006][ByrnesYamamoto2006]
-/

set_option autoImplicit false

noncomputable section

open Matrix
open Real

namespace Qatlib.Papers.LatGaugeSim05.MainResults

/-- The real two-dimensional rotation matrix with angle `φ`. -/
def u5Rot (φ : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  !![Real.cos φ, -Real.sin φ; Real.sin φ, Real.cos φ]

/-- The transpose of `u5Rot φ` multiplied by `u5Rot φ` is the identity [ByrnesYamamoto2006]. -/
theorem u5Rot_orthogonal (φ : ℝ) : (u5Rot φ)ᵀ * u5Rot φ = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [u5Rot, Matrix.mul_apply, Matrix.transpose_apply, Fin.sum_univ_two,
      Matrix.one_apply] <;>
    nlinarith [Real.cos_sq_add_sin_sq φ, Real.sin_sq_add_cos_sq φ]

/-- The product of `u5Rot φ` with its transpose is the identity [ByrnesYamamoto2006]. -/
theorem u5Rot_orthogonal' (φ : ℝ) : u5Rot φ * (u5Rot φ)ᵀ = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [u5Rot, Matrix.mul_apply, Matrix.transpose_apply, Fin.sum_univ_two,
      Matrix.one_apply] <;>
    nlinarith [Real.cos_sq_add_sin_sq φ, Real.sin_sq_add_cos_sq φ]

/-- The initialization application count `c * (d * M)`. -/
def u5ApplyCount (M d c : ℕ) : ℕ := c * (d * M)

/-- The local initialization operation count `c * (M * d)`. -/
def u5LocalOpCount (M d c : ℕ) : ℕ := c * (M * d)

/-- The worst-case initialization operation count `D * d ^ 2 * M ^ 2`. -/
def u5WorstOpCount (M d D : ℕ) : ℕ := D * d ^ 2 * M ^ 2

/-- The initialization application count equals `c * d * M` [ByrnesYamamoto2006]. -/
theorem u5_apply_count_eq (M d c : ℕ) : u5ApplyCount M d c = c * d * M := by
  simp only [u5ApplyCount]; ring

/-- Increasing `M` by one increases the local initialization operation count by `c * d`
[ByrnesYamamoto2006]. -/
theorem u5_local_op_count_linear (d c : ℕ) (M : ℕ) :
    u5LocalOpCount (M + 1) d c = u5LocalOpCount M d c + c * d := by
  simp only [u5LocalOpCount]; ring

/-- The worst-case initialization count factors as `(d * M) * (D * d * M)` [ByrnesYamamoto2006]. -/
theorem u5_worst_is_plaquette_times_qubits (M d D : ℕ) :
    u5WorstOpCount M d D = (d * M) * (D * d * M) := by
  simp only [u5WorstOpCount]; ring

/-- The worst-case initialization count equals `D * d ^ 2 * M ^ 2` [ByrnesYamamoto2006]. -/
theorem u5_worst_op_count_quadratic (M d D : ℕ) :
    u5WorstOpCount M d D = D * d ^ 2 * M ^ 2 := by
  simp only [u5WorstOpCount]

end Qatlib.Papers.LatGaugeSim05.MainResults
