/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.Matrix.HermitianFunctionalCalculus
import Mathlib.LinearAlgebra.Matrix.PosDef
import Qatlib.Foundations.PureStateMath.Qubit

/-!
# Density operators, partial trace, and matrix norms

This module defines finite complex `Operator` matrices, density operators, and pure density
operators characterized by idempotence. The map `PartialTrace` traces out the right subsystem
and preserves positivity and trace, yielding reduced density operators as in the standard
density-matrix formalism [Watrous2018].

The norm definitions `SchattenOne`, `SchattenTwo`, and `OperatorSpectralNorm` provide trace,
Hilbert-Schmidt, and Euclidean operator norms [Bhatia1997].

## Main statements

* `isDensityOperator_partialTrace`: The reduced matrix of a positive semidefinite trace-one
  matrix is a density operator.
* `trace_partialTrace`: Partial trace preserves the full trace.
* `partialTrace_posSemidef`: Partial trace preserves positive semidefiniteness.

## References

* [Watrous, 2018][Watrous2018]
* [Bhatia, 1997][Bhatia1997]
-/

namespace Qatlib.Foundations.PureStateMath

open scoped ComplexOrder

variable {D E : ℕ}

/-- Complex square matrices indexed by `Fin D`, representing operators in dimension `D`. -/
abbrev Operator (D : ℕ) := Matrix (Fin D) (Fin D) ℂ

/-- The Schatten 1-norm, defined as the real part of the trace of the positive square root of
`A.conjTranspose * A`. -/
noncomputable def SchattenOne (A : Operator D) : ℝ :=
  (Matrix.trace (cfc Real.sqrt (A.conjTranspose * A))).re

/-- The Schatten 2-norm, defined as the square root of the real part of the trace of
`A.conjTranspose * A`. -/
noncomputable def SchattenTwo (A : Operator D) : ℝ :=
  Real.sqrt ((Matrix.trace (A.conjTranspose * A)).re)

/-- The predicate that an operator is positive semidefinite and has trace one. -/
def IsDensityOperator (ρ : Operator D) : Prop :=
  ρ.PosSemidef ∧ Matrix.trace ρ = 1

/-- The predicate that an operator is a density operator and is idempotent under matrix
multiplication. -/
def IsPureDensityOperator (ρ : Operator D) : Prop :=
  IsDensityOperator ρ ∧ ρ * ρ = ρ

/-- The subtype of dimension-`D` operators satisfying `IsDensityOperator`. -/
abbrev DensityOperator (D : ℕ) := {ρ : Operator D // IsDensityOperator ρ}

/-- The partial trace over the right subsystem, summing matrix entries with matching
second-subsystem indices. -/
noncomputable def PartialTrace (A : Matrix (Fin D × Fin E) (Fin D × Fin E) ℂ) :
    Operator D :=
  fun i j => ∑ a : Fin E, A (i, a) (j, a)

/-- The operator norm of the continuous linear map induced by a matrix on complex Euclidean
space. -/
noncomputable def OperatorSpectralNorm (A : Operator D) : ℝ :=
  ‖(Matrix.toEuclideanCLM : Operator D ≃⋆ₐ[ℂ]
      (EuclideanSpace ℂ (Fin D) →L[ℂ] EuclideanSpace ℂ (Fin D))) A‖

/-- The trace of the partial trace of a bipartite matrix equals its full trace. -/
theorem trace_partialTrace (A : Matrix (Fin D × Fin E) (Fin D × Fin E) ℂ) :
    Matrix.trace (PartialTrace A) = Matrix.trace A := by
  simp [PartialTrace, Matrix.trace, Fintype.sum_prod_type]

/-- The partial trace of a positive semidefinite matrix is positive semidefinite. -/
theorem partialTrace_posSemidef {A : Matrix (Fin D × Fin E) (Fin D × Fin E) ℂ}
    (hA : A.PosSemidef) : (PartialTrace A).PosSemidef := by
  have h := Matrix.posSemidef_sum (Finset.univ : Finset (Fin E))
    (fun a _ => hA.submatrix (fun i => (i, a)))
  have hsum : PartialTrace A = ∑ a : Fin E, A.submatrix (fun i => (i, a))
      (fun i => (i, a)) := by
    ext i j
    simp [PartialTrace, Matrix.sum_apply, Matrix.submatrix_apply]
  rw [hsum]
  simpa using h

/-- The partial trace of a positive semidefinite trace-one matrix is a density operator. -/
theorem isDensityOperator_partialTrace {A : Matrix (Fin D × Fin E) (Fin D × Fin E) ℂ}
    (hA : A.PosSemidef) (htrace : Matrix.trace A = 1) : IsDensityOperator (PartialTrace A) :=
  ⟨partialTrace_posSemidef hA, (trace_partialTrace A).trans htrace⟩

/-- The partial trace of the zero bipartite matrix is zero. -/
@[simp] theorem partialTrace_zero :
    PartialTrace (0 : Matrix (Fin D × Fin E) (Fin D × Fin E) ℂ) = 0 := by
  ext i j
  simp [PartialTrace]

/-- The Schatten 2-norm of the zero operator is zero. -/
@[simp] theorem schattenTwo_zero : SchattenTwo (0 : Operator D) = 0 := by
  simp [SchattenTwo]

/-- The Schatten 2-norm is nonnegative. -/
theorem schattenTwo_nonneg (A : Operator D) : 0 ≤ SchattenTwo A :=
  Real.sqrt_nonneg _

/-- The spectral operator norm is nonnegative. -/
theorem operatorSpectralNorm_nonneg (A : Operator D) : 0 ≤ OperatorSpectralNorm A :=
  norm_nonneg _

/-- The zero operator is not a density operator. -/
theorem not_isDensityOperator_zero : ¬ IsDensityOperator (0 : Operator D) := by
  rintro ⟨_, h⟩
  simp at h

end Qatlib.Foundations.PureStateMath
