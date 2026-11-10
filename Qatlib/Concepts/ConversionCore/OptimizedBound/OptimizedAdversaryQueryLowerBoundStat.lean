/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.GramQueryCore.GammaDuality.FilteredGamma2Optimization
set_option backward.isDefEq.respectTransparency false
set_option warningAsError false

set_option autoImplicit false
open Qatlib.Foundations.QueryWordCore.Circuit
open Qatlib.Foundations.PureStateMath

open Qatlib.Concepts.GramQueryCore.GammaDuality
open Qatlib.Concepts.QueryComplexity.AdversarySearch

namespace Qatlib.Concepts.ConversionCore.OptimizedBound
open Matrix
open scoped ENNReal

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
