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
import Qatlib.Concepts.QueryComplexity.Reflections.SpanProgramGraph

/-!
# Uncorrected kernel-witness contract

Defines `KernelWitness`, an existential specification of positive and negative kernel vectors
under a witness norm budget. It asks for root concentration on positive inputs and target
overlap on negative inputs, but permits both vectors to be zero.

The proposition is retained for comparison with the explicit nonzero witness construction
associated with [Reichardt2011].

## Main statements

* `KernelWitness`: packages kernel equations and homogeneous overlap inequalities without
  nonzero-witness requirements.

## References

* [Reichardt, 2011][Reichardt2011]
-/

open Qatlib.Foundations.PureStateMath

namespace Qatlib.Concepts.QueryComplexity.Reflections

open Matrix
open scoped BigOperators

/-- The uncorrected existential contract for positive and negative kernel witnesses with
root-mass and target-overlap inequalities; its witnesses are permitted to be zero. -/
def KernelWitness : Prop :=
  ∀ (X : Type) [Fintype X] [DecidableEq X] (n m : ℕ)
    (input : X → Fin n → Bool) (f : X → Bool) (v : X → Fin n → Fin m → ℂ) (W : ℝ),
    (∀ x : X, ∑ j : Fin n, ∑ k : Fin m, ‖v x j k‖ ^ 2 ≤ W) →
    1 ≤ W →
    (∀ x : X, f x = true →
      ∃ ψ : QState (ColLab X f n m),
        markedBiadj input f v W x *ᵥ ψ = 0 ∧
        ‖ψ (Sum.inl ())‖ ^ 2
          ≥ (9 : ℝ) / 10 * ∑ c : ColLab X f n m, ‖ψ c‖ ^ 2) ∧
    (∀ x : X, f x = false →
      ∃ ψ : QState (RowLab X f n m),
        (restrictedBiadj input f v x)ᴴ *ᵥ ψ = 0 ∧
        ‖Inner (tvec W) (fun x' => ψ (Sum.inl x'))‖ ^ 2
          ≥ (1 / (9 * W * (W + 1))) * ∑ l : RowLab X f n m, ‖ψ l‖ ^ 2)

end Qatlib.Concepts.QueryComplexity.Reflections
