/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.SdpDuality.ConeSeparation.SdpRunMacros

/-!
# Failed-round primal witness contract

`SdpLargerTriggerRun` states the primal certificate guarantee when a round fails after a prefix
of successful oracle contracts. The conclusion provides primal feasibility, the trace bound R,
and objective at least (1 − δ)α.

For the mathematical background, see [BrandaoSvore2017].

## Main statements

* `SdpLargerTriggerRun`: The contract stating that a round failure after the specified
  successful prefix yields a positive semidefinite primal feasible witness of trace at most R
  and objective at least (1 − δ)α.

## References

* [Brandao and Svore, 2017][BrandaoSvore2017]
-/

set_option backward.isDefEq.respectTransparency false

open Qatlib.Foundations.PureStateMath

open Qatlib.Concepts.SdpDuality.ConeSeparation
open Qatlib.Concepts.MatrixWeights.WeightsCore

namespace Qatlib.Concepts.SdpMmwSolver.BranchProofs

open Matrix
open scoped Classical BigOperators Matrix.Norms.L2Operator ComplexOrder

/-- The contract stating that a round failure after the specified successful prefix yields a
positive semidefinite primal feasible witness of trace at most R and objective at least (1 −
δ)α. -/
def SdpLargerTriggerRun : Prop :=
  ∀ (D m : ℕ) (A : Fin m → Operator D) (Cv : Operator D) (b : Fin m → ℝ)
    (y : ℕ → Fin m → ℝ) (j₀ : Fin m) (α R δ ε η : ℝ) (t₀ : ℕ),
    0 < D → 0 < α → 0 < R → 0 < δ → δ ≤ 1 → 0 < ε → ε ≤ δ/(16*R) →
    (∀ i, (A i).IsHermitian) → Cv.IsHermitian →
    (∀ i, 1 ≤ b i) → A j₀ = 1 → b j₀ = R →
    (∀ t ∈ Finset.range t₀, SdpRoundOracleContract D m A Cv b α ε η y t) →
    SdpRoundOracleFailure D m A Cv b α R ε η y t₀ →
    ∃ X : Operator D, X.PosSemidef ∧
      (∀ i, (Matrix.trace (A i * X)).re ≤ b i) ∧
      (Matrix.trace X).re ≤ R ∧
      (1 - δ)*α ≤ (Matrix.trace (Cv * X)).re

end Qatlib.Concepts.SdpMmwSolver.BranchProofs
