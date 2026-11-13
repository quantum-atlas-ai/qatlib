/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Analysis.SpecialFunctions.Complex.Analytic
import Mathlib.Analysis.Complex.Norm
import Mathlib.Analysis.Normed.Group.Defs
import Mathlib.Algebra.BigOperators.Group.Finset.Defs
import Mathlib.Data.Matrix.Mul
import Mathlib.LinearAlgebra.Matrix.ConjTranspose
import Mathlib.Data.Complex.Basic
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Matrix.ColumnRowPartitioned
import Qatlib.Concepts.Execution.WorkspaceCP.ProjectedUnitaryEncoding
import Qatlib.Foundations.PureStateMath.Qubit

/-!
# Effective-gap adjacency and uncorrected contract

Defines `effectiveGapAdjacency` by adjoining a distinguished target column to a complex
biadjacency matrix and forming the Hermitian block adjacency. It also defines
`EffectiveSpectralGap`, the root spectral-mass assertion based on a kernel-overlap inequality.

The contract omits a nonzero-witness condition and is retained as an uncorrected formulation of
the effective-gap setting in [Reichardt2011].

## Main statements

* `effectiveGapAdjacency`: constructs the target-augmented bipartite adjacency.
* `EffectiveSpectralGap`: states the uncorrected bound `8 * γ^2 / δ` for low-energy root mass.

## References

* [Reichardt, 2011][Reichardt2011]
-/

set_option backward.isDefEq.respectTransparency false
open Qatlib.Foundations.PureStateMath

open Qatlib.Concepts.Execution.WorkspaceCP

namespace Qatlib.Concepts.QueryComplexity.Reflections

open Matrix
open scoped BigOperators

/-- The Hermitian bipartite adjacency with biadjacency columns consisting of the target vector
`t` followed by the columns of `B`. -/
noncomputable def effectiveGapAdjacency {T U : Type} [DecidableEq T] [DecidableEq U]
    (B : Matrix T U ℂ) (t : QState T) : Matrix (T ⊕ (Unit ⊕ U)) (T ⊕ (Unit ⊕ U)) ℂ :=
  fun p q =>
    match p, q with
    | Sum.inl r, Sum.inr (Sum.inl ()) => t r
    | Sum.inl r, Sum.inr (Sum.inr u) => B r u
    | Sum.inr (Sum.inl ()), Sum.inl r => star (t r)
    | Sum.inr (Sum.inr u), Sum.inl r => star (B r u)
    | _, _ => 0

/-- The uncorrected effective spectral-gap contract bounding root spectral mass below energy `γ`
by `8 * γ^2 / δ` from a kernel witness and overlap inequality, without a nonzero-witness
requirement. -/
def EffectiveSpectralGap : Prop :=
  ∀ (T U : Type) [Fintype T] [DecidableEq T] [Fintype U] [DecidableEq U]
    (B : Matrix T U ℂ) (t ψ : QState T) (δ : ℝ),
    0 < δ →
    (Bᴴ *ᵥ ψ) = 0 →
    ‖Inner t ψ‖ ^ 2 ≥ δ * ∑ u : T, ‖ψ u‖ ^ 2 →
    ∀ γ : ℝ, 0 ≤ γ →
    ∀ (k : ℕ) (Vfr : Matrix (T ⊕ (Unit ⊕ U)) (Fin k) ℂ) (ρ : Fin k → ℝ),
      Qatlib.Concepts.Execution.WorkspaceCP.IsIsometry Vfr →
      Vfr * Vfrᴴ = 1 →
      effectiveGapAdjacency B t * Vfr = Vfr * Matrix.diagonal (fun i => ((ρ i : ℝ) : ℂ)) →
      (∑ i : Fin k,
          (if |ρ i| ≤ γ then ‖Vfr (Sum.inr (Sum.inl ())) i‖ ^ 2 else 0))
        ≤ 8 * γ ^ 2 / δ

end Qatlib.Concepts.QueryComplexity.Reflections
