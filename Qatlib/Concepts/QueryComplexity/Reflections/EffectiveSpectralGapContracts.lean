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
set_option backward.isDefEq.respectTransparency false
set_option warningAsError false
open Qatlib.Foundations.PureStateMath

open Qatlib.Concepts.Execution.WorkspaceCP

namespace Qatlib.Concepts.QueryComplexity.Reflections

open Matrix
open scoped BigOperators

noncomputable def effectiveGapAdjacency {T U : Type} [DecidableEq T] [DecidableEq U]
    (B : Matrix T U ℂ) (t : QState T) : Matrix (T ⊕ (Unit ⊕ U)) (T ⊕ (Unit ⊕ U)) ℂ :=
  fun p q =>
    match p, q with
    | Sum.inl r, Sum.inr (Sum.inl ()) => t r
    | Sum.inl r, Sum.inr (Sum.inr u) => B r u
    | Sum.inr (Sum.inl ()), Sum.inl r => star (t r)
    | Sum.inr (Sum.inr u), Sum.inl r => star (B r u)
    | _, _ => 0

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
