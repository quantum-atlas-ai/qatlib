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
import Qatlib.Concepts.Execution.WorkspaceCP.ProjectedUnitaryEncoding
import Qatlib.Concepts.QueryComplexity.Reflections.SpanProgramGraph
import Qatlib.Foundations.PureStateMath.Qubit

/-!
# Uncorrected bipartite effective-gap contract

Defines `BipartiteEffectiveGap`, a proposition combining positive-input kernel concentration and
negative-input low-energy spectral bounds under a witness norm budget alone. This contract uses
`markedAdjacency` and does not require source dual feasibility.

The formulation is retained for comparison with the corrected graph construction associated with
[Reichardt2011]; this module defines the proposition without proving it.

## Main statements

* `BipartiteEffectiveGap`: packages the uncorrected root kernel-mass and low-energy spectral
  assertions.

## References

* [Reichardt, 2011][Reichardt2011]
-/

set_option backward.isDefEq.respectTransparency false
set_option warningAsError false
open Qatlib.Foundations.PureStateMath

namespace Qatlib.Concepts.QueryComplexity.Reflections

open Matrix
open scoped BigOperators

/-- The uncorrected contract asserting a positive-input kernel witness with root mass at least
`9/10` and a negative-input low-energy mass bound of `72 * (1 + 1/W) * c^2` from a witness
norm budget alone. -/
def BipartiteEffectiveGap : Prop :=
  ∀ (X : Type) [Fintype X] [DecidableEq X] (n m : ℕ)
    (input : X → Fin n → Bool) (f : X → Bool) (v : X → Fin n → Fin m → ℂ) (W : ℝ),
    (∀ x : X, ∑ j : Fin n, ∑ k : Fin m, ‖v x j k‖ ^ 2 ≤ W) →
    1 ≤ W →
    (∀ x : X, f x = true →
      ∃ ψ : QState (ColLab X f n m),
        markedAdjacency input f v W x *ᵥ Sum.elim 0 ψ = 0 ∧
        ‖ψ (Sum.inl ())‖ ^ 2
          ≥ (9 : ℝ) / 10 * ∑ c : ColLab X f n m, ‖ψ c‖ ^ 2) ∧
    (∀ x : X, f x = false → ∀ c : ℝ, 0 ≤ c →
      ∀ (k : ℕ) (Vfr : Matrix (RowLab X f n m ⊕ ColLab X f n m) (Fin k) ℂ)
        (ρ : Fin k → ℝ),
        Qatlib.Concepts.Execution.WorkspaceCP.IsIsometry Vfr →
        Vfr * Vfrᴴ = 1 →
        markedAdjacency input f v W x * Vfr = Vfr * Matrix.diagonal (fun i => ((ρ i : ℝ) : ℂ)) →
        (∑ i : Fin k,
            (if |ρ i| ≤ c / W then ‖Vfr (Sum.inr (Sum.inl ())) i‖ ^ 2 else 0))
          ≤ (72 : ℝ) * (1 + 1 / W) * c ^ 2)

end Qatlib.Concepts.QueryComplexity.Reflections
