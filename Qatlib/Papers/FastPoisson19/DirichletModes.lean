/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Foundations.MatrixAlgebra.DirichletModes

set_option autoImplicit false
noncomputable section
open Matrix
namespace Qatlib.Papers.FastPoisson19.DirichletModes
open Qatlib.Foundations.MatrixAlgebra

def matrix (N : ℕ) : Matrix (Fin (N-1)) (Fin (N-1)) ℝ := fun i j =>
  (N : ℝ) ^ 2 * ((if i = j then 2 else 0) - (if j.val+1=i.val then 1 else 0) -
    (if i.val+1=j.val then 1 else 0))

def vector (N : ℕ) (j : Fin (N-1)) (k : Fin (N-1)) : ℝ :=
  Real.sqrt (2 / (N : ℝ)) * Real.sin (((k.val+1 : ℕ) : ℝ) *
    (((j.val+1 : ℕ) : ℝ) * Real.pi / (N : ℝ)))

def value (N : ℕ) (j : Fin (N-1)) : ℝ :=
  4 * (N : ℝ) ^ 2 * Real.sin ((((j.val+1 : ℕ) : ℝ)*Real.pi/(N : ℝ))/2) ^ 2

theorem matrix_eq_actual (N : ℕ) (hN : 2 ≤ N) : matrix N = DirichletModes.laplacian (N-1) := by
  ext i j
  rw [DirichletModes.laplacian_apply, Nat.sub_add_cancel (by omega : 1 ≤ N)]
  rfl

theorem vector_eq_actual (N : ℕ) (hN : 2 ≤ N) (j : Fin (N-1)) :
    vector N j = DirichletModes.sourceMode (N-1) j := by
  ext k
  simp only [vector, DirichletModes.sourceMode, Pi.smul_apply, smul_eq_mul,
    DirichletModes.sine, DirichletModes.angle, Nat.sub_add_cancel (by omega : 1 ≤ N)]

theorem value_eq_actual (N : ℕ) (hN : 2 ≤ N) (j : Fin (N-1)) :
    value N j = DirichletModes.eigenvalue (N-1) j := by
  simp only [value, DirichletModes.eigenvalue, DirichletModes.angle,
    Nat.sub_add_cancel (by omega : 1 ≤ N)]

theorem actual_source_eigenvector (N : ℕ) (hN : 2 ≤ N) (j : Fin (N-1)) :
    Module.End.HasEigenvector (Matrix.toLin' (matrix N)) (value N j) (vector N j) := by
  rw [matrix_eq_actual N hN, vector_eq_actual N hN, value_eq_actual N hN]
  exact DirichletModes.sourceMode_hasEigenvector (N-1) j

theorem actual_source_mulVec (N : ℕ) (hN : 2 ≤ N) (j : Fin (N-1)) :
    matrix N *ᵥ vector N j = value N j • vector N j := by
  rw [matrix_eq_actual N hN, vector_eq_actual N hN, value_eq_actual N hN]
  exact DirichletModes.laplacian_sourceMode (N-1) j

theorem actual_source_symmetric (N : ℕ) (hN : 2 ≤ N) : (matrix N).IsSymm := by
  rw [matrix_eq_actual N hN]
  exact DirichletModes.laplacian_symmetric (N-1)

theorem actual_source_value_positive (N : ℕ) (hN : 2 ≤ N) (j : Fin (N-1)) : 0 < value N j := by
  rw [value_eq_actual N hN]
  exact DirichletModes.eigenvalue_pos (N-1) j
end Qatlib.Papers.FastPoisson19.DirichletModes
