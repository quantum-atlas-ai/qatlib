/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.InteractionEvo.EffCosts.EffectiveDysonDefinitions

/-!
# Integrable mean derivative grid error contract

This module defines `EffectiveMeanDerivativeGridError`, the three-term accuracy specification
for strict truncated Dyson grids. Its hypotheses require a bounded continuous Hermitian field,
an integrable derivative norm, and a short-time bound. The specification follows the Dyson error
decomposition in the setting of [LowWiebe2018].

## Main statements

* `EffectiveMeanDerivativeGridError`: Euler, derivative-integral, and factorial-tail error
  terms.

## References

* [Low and Wiebe, 2018][LowWiebe2018]
-/

set_option warningAsError false
set_option backward.isDefEq.respectTransparency false
open Qatlib.Concepts.InteractionEvo.EffCosts
open Qatlib.Concepts.InteractionEvo.MeanDerivGrid
open Qatlib.Concepts.InteractionEvo.MeanDerivGrid.InteractionPicture2018
set_option autoImplicit false
open Qatlib.Concepts.InteractionEvo.MeanDerivGrid.DysonMeanDerivativeGrid
open Qatlib.Concepts.TimeEvolution.TimeOrderedEvolution

namespace Qatlib.Concepts.InteractionEvo.MeanDerivGrid
open Qatlib.Concepts.InteractionEvo.ComputedGrid Qatlib.Concepts.InteractionEvo.EffCosts
open Qatlib.Concepts.InteractionEvo.MeanDerivGrid
open Qatlib.Concepts.InteractionEvo.MeanDerivGrid.InteractionPicture2018 Matrix
open scoped Classical BigOperators Matrix.Norms.L2Operator ComplexOrder
/-- The universal three-term bound `exp(alpha t) alpha² t² / (2 M) + (t / M) ∫₀ᵗ ‖Hd u‖ + 2
(alpha t)^(K+1) / (K+1)!` for truncated grids under the stated bounded-field,
derivative-norm integrability, and short-time hypotheses. -/
noncomputable def EffectiveMeanDerivativeGridError : Prop :=
  ∀ (I : Type) [Fintype I] [DecidableEq I] (H Hd : ℝ → Matrix I I ℂ)
      (t alpha : ℝ) (M K : ℕ),
    Continuous H → IntervalIntegrable (fun u => ‖Hd u‖) MeasureTheory.volume 0 t →
    (∀ u ∈ Set.Icc 0 t, HasDerivAt H (Hd u) u) →
    0 ≤ t → 0 ≤ alpha → 0 < M →
    (∀ u ∈ Set.Icc 0 t, (H u).IsHermitian ∧ ‖H u‖ ≤ alpha) →
    alpha*t ≤ Real.log 2 →
    ‖dysonGridTruncatedSum H t M K - orderedEvolution (fun u => Complex.I • H u) 0 t‖ ≤
      Real.exp (alpha*t)*alpha^2*t^2/(2*M) +
        (t/M)*(∫ u in (0 : ℝ)..t, ‖Hd u‖) +
          (2 : ℝ)*(alpha*t)^(K+1)/(Nat.factorial (K+1) : ℝ)
end Qatlib.Concepts.InteractionEvo.MeanDerivGrid
