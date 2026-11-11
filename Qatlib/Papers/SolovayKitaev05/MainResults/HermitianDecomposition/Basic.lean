/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.LinearAlgebra.Matrix.Hermitian

/-!
# Hermitian commutators for zero-diagonal two-dimensional matrices

This module proves `exists_hermitian_commutator_zero_diagonal`, expressing `I` times a
two-dimensional Hermitian matrix with zero diagonal as a commutator of Hermitian matrices. The
result supplies a concrete algebraic decomposition for the higher-dimensional Solovay–Kitaev
discussion in [DawsonNielsen2006].

## Main statements

* `exists_hermitian_commutator_zero_diagonal`: For every complex `b`, there exist Hermitian
  two-by-two matrices whose commutator is `I` times the matrix with off-diagonal entries `b` and
  `star b` and zero diagonal, as used in [DawsonNielsen2006].

## References

* [Dawson and Nielsen, 2006][DawsonNielsen2006]
-/

namespace Qatlib.Papers.SolovayKitaev05.MainResults.HermitianDecomposition

open Matrix
open scoped Matrix.Norms.L2Operator

set_option autoImplicit false

/-- For every complex `b`, there exist Hermitian two-by-two matrices whose commutator is `I`
times the matrix with off-diagonal entries `b` and `star b` and zero diagonal, as used in
[DawsonNielsen2006]. -/
theorem exists_hermitian_commutator_zero_diagonal (b : ℂ) :
    ∃ F G : Matrix (Fin 2) (Fin 2) ℂ,
      F.IsHermitian ∧ G.IsHermitian ∧
        F * G - G * F = Complex.I • !![0, b; star b, 0] := by
  refine ⟨!![0, -Complex.I * b; star (-Complex.I * b), 0],
    !![(1 / 2 : ℂ), 0; 0, -(1 / 2 : ℂ)], ?_, ?_, ?_⟩
  · rw [Matrix.IsHermitian]
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.conjTranspose_apply]
  · rw [Matrix.IsHermitian]
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.conjTranspose_apply]
  · ext i j
    fin_cases i <;> fin_cases j <;>
      · apply Complex.ext <;> simp <;> ring

end Qatlib.Papers.SolovayKitaev05.MainResults.HermitianDecomposition
