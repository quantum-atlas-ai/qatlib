/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.SdpDuality.ConeSeparation.SdpRunMacros

/-!
# Numerical quantities for sampled SDP payoffs

`sdpEventProbability`, `sdpSampledWidthBudget`, and `sdpSampledSeparationSlack` define the
finite probability and error budgets used in oracle diagnostics. `sdpSparsifiedPayoff` averages
sampled constraint matrices, while `sdpScaledSparsifiedPayoff` additionally restores a
prescribed total mass.

For the mathematical background, see [BrandaoSvore2017].

## Main statements

* `sdpScaledSparsifiedPayoff`: The normalized SDP payoff formed from the empirical average of
  sampled constraint matrices multiplied by `mass`.

## References

* [Brandao and Svore, 2017][BrandaoSvore2017]
-/

set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false
noncomputable section
open Qatlib.Foundations.PureStateMath

namespace Qatlib.Concepts.SdpMmwSolver.OracleError

open Matrix
open scoped Classical BigOperators Matrix.Norms.L2Operator ComplexOrder

/-- The fraction of indices in `Fin R` satisfying `P`, with Lean's total division convention
when R = 0. -/
def sdpEventProbability {R : ℕ} (P : Fin R → Prop) : ℝ :=
  (Finset.univ.filter P).card / (R : ℝ)

/-- The sampled width budget α(1 + 2R(κ + ν)). -/
def sdpSampledWidthBudget (α R κ ν : ℝ) : ℝ := α * (1 + 2 * R * (κ + ν))

/-- The sampled separation slack 2α(κ + ν). -/
def sdpSampledSeparationSlack (α κ ν : ℝ) : ℝ := 2 * α * (κ + ν)

/-- The normalized SDP payoff formed from the unweighted empirical average of sampled constraint
matrices. -/
def sdpSparsifiedPayoff (D m Q : ℕ) (A : Fin m → Operator D) (Cv : Operator D)
    (α : ℝ) (idx : Fin Q → Fin m) : Operator D :=
  ((4 * α : ℝ))⁻¹ • (((Q : ℝ)⁻¹ • (∑ j : Fin Q, A (idx j))) - Cv + (2 * α) • (1 : Operator D))

/-- The normalized SDP payoff formed from the empirical average of sampled constraint matrices
multiplied by `mass`. -/
def sdpScaledSparsifiedPayoff (D m Q : ℕ) (A : Fin m → Operator D) (Cv : Operator D)
    (α mass : ℝ) (idx : Fin Q → Fin m) : Operator D :=
  ((4 * α : ℝ))⁻¹ •
    (mass • ((Q : ℝ)⁻¹ • (∑ j : Fin Q, A (idx j))) - Cv +
      (2 * α) • (1 : Operator D))

end Qatlib.Concepts.SdpMmwSolver.OracleError
