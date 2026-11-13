/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.GramQueryCore.GammaDuality.FilteredGamma2Optimization

/-!
# Optimized adversary query lower bound specification

`OptimizedAdversaryQueryLowerBound` formulates the adversary lower bound for Boolean function
evaluation on a nonempty finite input domain. Its hypotheses refer to a fixed unitary workspace
circuit, a normalized initial state and a Born event distinguishing the two output values.

The mathematical context is discussed in [LeeEtAl2011].

## Main statements

* `OptimizedAdversaryQueryLowerBound`: The query cost inequality with the bounded error overlap
  factor.

## References

* [Lee et al., 2011][LeeEtAl2011]
-/

set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false
open Qatlib.Foundations.QueryWordCore.Circuit
open Qatlib.Foundations.PureStateMath

open Qatlib.Concepts.GramQueryCore.GammaDuality
open Qatlib.Concepts.QueryComplexity.AdversarySearch

namespace Qatlib.Concepts.ConversionCore.OptimizedBound
open Matrix
open scoped ENNReal

/-- The statement that a unitary Boolean query circuit succeeding with error ε in [0, 1/2]
satisfies `(1 − 2√(ε(1 − ε))) * generalAdversaryValue input f ≤ 2 * QueryCount C`, expressed
in the extended nonnegative reals. -/
def OptimizedAdversaryQueryLowerBound : Prop :=
  ∀ (X W : Type) [Fintype X] [DecidableEq X] [Nonempty X] [Fintype W] [DecidableEq W]
    (n : ℕ) (input : X → Fin n → Bool) (f : X → Bool)
    (C : Circuit ((Fin n × Bool) × W)) (ψ : QState ((Fin n × Bool) × W))
    (E : Finset ((Fin n × Bool) × W)) (ε : ℝ),
    IsUnitaryCircuit C → Normalized ψ → 0 ≤ ε → ε ≤ 1 / 2 →
    (∀ x, 1 - ε ≤ MeasureProb (Run (workspaceBitOracle (W := W) (input x)) C ψ)
      (if f x then E else Eᶜ)) →
    ENNReal.ofReal (1 - 2 * Real.sqrt (ε * (1 - ε))) * generalAdversaryValue input f ≤
      ENNReal.ofReal (2 * (QueryCount C : ℝ))

end Qatlib.Concepts.ConversionCore.OptimizedBound
