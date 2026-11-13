/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.SdpDuality.ConeSeparation.Macros

/-!
# Dual payoff range contract

`SdpDualPayoffRange` states the operator interval guarantee needed by matrix multiplicative
weights. Nonnegative responses with weighted cost at most α, together with input norm bounds and
α ≥ 1, ensure Hermitian payoffs between zero and the identity.

For the mathematical background, see [BrandaoSvore2017].

## Main statements

* `SdpDualPayoffRange`: The contract asserting that normalized dual payoffs are Hermitian and
  lie between zero and the identity under the stated norm, coefficient, and width hypotheses.

## References

* [Brandao and Svore, 2017][BrandaoSvore2017]
-/

set_option backward.isDefEq.respectTransparency false

open Qatlib.Foundations.PureStateMath

open Qatlib.Concepts.SdpDuality.ConeSeparation

namespace Qatlib.Concepts.SdpMmwSolver.SdpContract

open Matrix
open scoped Classical BigOperators Matrix.Norms.L2Operator ComplexOrder MatrixOrder

/-- The contract asserting that normalized dual payoffs are Hermitian and lie between zero and
the identity under the stated norm, coefficient, and width hypotheses. -/
def SdpDualPayoffRange : Prop :=
  ∀ (D m : ℕ) (A : Fin m → Operator D) (Cv : Operator D) (b : Fin m → ℝ)
    (y : ℕ → Fin m → ℝ) (α : ℝ),
    0 < D → 0 < α → 1 ≤ α →
    (∀ i, (A i).IsHermitian ∧ ‖A i‖ ≤ 1) →
    Cv.IsHermitian ∧ ‖Cv‖ ≤ 1 →
    (∀ i, 1 ≤ b i) →
    (∀ t, (∀ i, 0 ≤ y t i) ∧ (∑ i, b i * y t i ≤ α)) →
    ∀ s, (sdpDualPayoff D m A Cv α y s).IsHermitian ∧
      (0 : Operator D) ≤ sdpDualPayoff D m A Cv α y s ∧
      sdpDualPayoff D m A Cv α y s ≤ 1

end Qatlib.Concepts.SdpMmwSolver.SdpContract
