/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Foundations.MatrixAlgebra.DirichletModes

/-!
# Dirichlet modes in the Poisson grid convention

`matrix`, `vector`, and `value` express the discrete Dirichlet Laplacian, sine modes, and
eigenvalues using a grid parameter `N` with `N - 1` interior points. For `N ≥ 2`, they agree
with the existing `DirichletModes` definitions and inherit the eigenvector and positivity
results. These statements concern the formulas and models in [WangEtAl2020].

## Main statements

* `actual_source_eigenvector`: each sine mode is an eigenvector with the stated eigenvalue.
* `actual_source_symmetric`: the matrix is symmetric.
* `actual_source_value_positive`: every listed eigenvalue is positive.

## References

* [Wang et al., 2020][WangEtAl2020]
-/

set_option autoImplicit false
noncomputable section
open Matrix
namespace Qatlib.Papers.FastPoisson19.DirichletModes
open Qatlib.Foundations.MatrixAlgebra

/-- The `(N - 1)`-dimensional Dirichlet tridiagonal matrix with diagonal `2 * N^2` and adjacent
entries `-N^2`. -/
def matrix (N : ℕ) : Matrix (Fin (N-1)) (Fin (N-1)) ℝ := fun i j =>
  (N : ℝ) ^ 2 * ((if i = j then 2 else 0) - (if j.val+1=i.val then 1 else 0) -
    (if i.val+1=j.val then 1 else 0))

/-- The sine mode with coordinate `sqrt (2 / N) * sin ((k + 1) * (j + 1) * π / N)`. -/
def vector (N : ℕ) (j : Fin (N-1)) (k : Fin (N-1)) : ℝ :=
  Real.sqrt (2 / (N : ℝ)) * Real.sin (((k.val+1 : ℕ) : ℝ) *
    (((j.val+1 : ℕ) : ℝ) * Real.pi / (N : ℝ)))

/-- The eigenvalue expression `4 * N^2 * sin ((j + 1) * π / (2 * N))^2`. -/
def value (N : ℕ) (j : Fin (N-1)) : ℝ :=
  4 * (N : ℝ) ^ 2 * Real.sin ((((j.val+1 : ℕ) : ℝ)*Real.pi/(N : ℝ))/2) ^ 2

/-- For `N ≥ 2`, identifies the grid-convention matrix with `DirichletModes.laplacian (N - 1)`. -/
theorem matrix_eq_actual (N : ℕ) (hN : 2 ≤ N) : matrix N = DirichletModes.laplacian (N-1) := by
  ext i j
  rw [DirichletModes.laplacian_apply, Nat.sub_add_cancel (by omega : 1 ≤ N)]
  rfl

/-- For `N ≥ 2`, identifies the grid-convention vector with `DirichletModes.sourceMode (N - 1)
j`. -/
theorem vector_eq_actual (N : ℕ) (hN : 2 ≤ N) (j : Fin (N-1)) :
    vector N j = DirichletModes.sourceMode (N-1) j := by
  ext k
  simp only [vector, DirichletModes.sourceMode, Pi.smul_apply, smul_eq_mul,
    DirichletModes.sine, DirichletModes.angle, Nat.sub_add_cancel (by omega : 1 ≤ N)]

/-- For `N ≥ 2`, identifies the grid-convention eigenvalue with `DirichletModes.eigenvalue (N -
1) j`. -/
theorem value_eq_actual (N : ℕ) (hN : 2 ≤ N) (j : Fin (N-1)) :
    value N j = DirichletModes.eigenvalue (N-1) j := by
  simp only [value, DirichletModes.eigenvalue, DirichletModes.angle,
    Nat.sub_add_cancel (by omega : 1 ≤ N)]

/-- For `N ≥ 2`, the sine mode is a nonzero eigenvector of the matrix linear map with eigenvalue
`value N j`. -/
theorem actual_source_eigenvector (N : ℕ) (hN : 2 ≤ N) (j : Fin (N-1)) :
    Module.End.HasEigenvector (Matrix.toLin' (matrix N)) (value N j) (vector N j) := by
  rw [matrix_eq_actual N hN, vector_eq_actual N hN, value_eq_actual N hN]
  exact DirichletModes.sourceMode_hasEigenvector (N-1) j

/-- For `N ≥ 2`, multiplying the matrix by the sine mode scales the mode by `value N j`. -/
theorem actual_source_mulVec (N : ℕ) (hN : 2 ≤ N) (j : Fin (N-1)) :
    matrix N *ᵥ vector N j = value N j • vector N j := by
  rw [matrix_eq_actual N hN, vector_eq_actual N hN, value_eq_actual N hN]
  exact DirichletModes.laplacian_sourceMode (N-1) j

/-- For `N ≥ 2`, the grid-convention Dirichlet matrix is symmetric. -/
theorem actual_source_symmetric (N : ℕ) (hN : 2 ≤ N) : (matrix N).IsSymm := by
  rw [matrix_eq_actual N hN]
  exact DirichletModes.laplacian_symmetric (N-1)

/-- For `N ≥ 2`, every grid-convention Dirichlet eigenvalue is strictly positive. -/
theorem actual_source_value_positive (N : ℕ) (hN : 2 ≤ N) (j : Fin (N-1)) : 0 < value N j := by
  rw [value_eq_actual N hN]
  exact DirichletModes.eigenvalue_pos (N-1) j
end Qatlib.Papers.FastPoisson19.DirichletModes
