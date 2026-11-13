/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Analysis.CStarAlgebra.Matrix
import Qatlib.Foundations.PureStateMath.MixedState
import Qatlib.Foundations.PureStateMath.Reflection.ReflectionLaws
import QuantumInfo.ForMathlib.MatrixNorm.TraceNorm

/-!
# Definitions of root fidelity and trace distance

`Froot` is the trace norm of the product of positive square roots, and `traceDistance` is half
the trace norm of an operator difference. Both expressions are nonnegative without
density-operator hypotheses.

`IsPurification`, `IsProbVector`, and `diagDensity` provide the pure-state and classical
representations used by the fidelity theorems. `CommutesToClassical` states the conditional
existence of a simultaneous unitary diagonalization into probability matrices. See
[Uhlmann1976].

## Main statements

* `Froot`: the root-fidelity expression.
* `traceDistance`: the half trace-norm distance.
* `IsPurification`: normalization and the prescribed reduced operator.
* `CommutesToClassical`: a conditional classical representation for commuting operators.

## References

* [Uhlmann, 1976][Uhlmann1976]
* [Wilde, 2017][Wilde2017]
-/

open Qatlib.Foundations.PureStateMath.Reflection
open Qatlib.Foundations.PureStateMath

namespace Qatlib.Concepts.MixedFidelity.FidelityMetric

open Matrix
open scoped MatrixOrder ComplexOrder

variable {D E : ℕ}

/-- The root-fidelity expression `Matrix.traceNorm (CFC.sqrt ρ * CFC.sqrt σ)`. -/
noncomputable def Froot (ρ σ : Operator D) : ℝ :=
  Matrix.traceNorm (CFC.sqrt ρ * CFC.sqrt σ)

/-- The root-fidelity expression is nonnegative for any two operators. -/
theorem Froot_nonneg (ρ σ : Operator D) : 0 ≤ Froot ρ σ := by
  simp only [Froot]
  exact Matrix.traceNorm_nonneg _

/-- Half the trace norm of the difference of two operators. -/
noncomputable def traceDistance (ρ σ : Operator D) : ℝ :=
  Matrix.traceNorm (ρ - σ) / 2

/-- The trace distance is nonnegative for any two operators. -/
theorem traceDistance_nonneg (ρ σ : Operator D) : 0 ≤ traceDistance ρ σ := by
  simp only [traceDistance]
  exact div_nonneg (Matrix.traceNorm_nonneg _) zero_le_two

/-- A normalized bipartite vector whose pure outer product has partial trace `ρ`. -/
def IsPurification (ψ : QState (Fin D × Fin E)) (ρ : Operator D) : Prop :=
  Normalized ψ ∧ PartialTrace (outerProduct ψ) = ρ

/-- The condition that every entry of a finite real vector is nonnegative and its entries sum to
one. -/
def IsProbVector (p : Fin D → ℝ) : Prop :=
  (∀ i, 0 ≤ p i) ∧ ∑ i, p i = 1

/-- The diagonal complex operator with diagonal entries given by the real vector `p`. -/
def diagDensity (p : Fin D → ℝ) : Operator D :=
  Matrix.diagonal fun i => (p i : ℂ)

/-- The entries of `diagDensity p` are `p i` on the diagonal and zero elsewhere. -/
@[simp]
theorem diagDensity_apply (p : Fin D → ℝ) (i j : Fin D) :
    diagDensity p i j = if i = j then (p i : ℂ) else 0 := by
  simp [diagDensity, Matrix.diagonal_apply]

/-- The proposition that, if `ρ` and `σ` commute, they possess a common unitary conjugation to
diagonal probability matrices. -/
def CommutesToClassical (ρ σ : Operator D) : Prop :=
  ρ * σ = σ * ρ → ∃ (U : Matrix (Fin D) (Fin D) ℂ) (p q : Fin D → ℝ),
    U ∈ Matrix.unitaryGroup (Fin D) ℂ ∧ IsProbVector p ∧ IsProbVector q ∧
    U * ρ * Uᴴ = diagDensity p ∧ U * σ * Uᴴ = diagDensity q

end Qatlib.Concepts.MixedFidelity.FidelityMetric
