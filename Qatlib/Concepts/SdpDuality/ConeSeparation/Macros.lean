/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.MatrixWeights.WeightsCore

/-!
# Normalized payoffs and averaged SDP certificates

This module supplies three formulas used to organize matrix multiplicative weights certificates
for semidefinite programs. `sdpDualPayoff` shifts and rescales each dual matrix combination,
while `sdpDualCertificate` averages the round vectors and adds an offset at a designated
constraint. The algorithmic background is the quantum SDP framework of [BrandaoSvore2017].

The round budget `sdpDualCertRounds` is a natural ceiling expression involving `Real.log D`.
These are definitions for arbitrary inputs; hypotheses ensuring useful spectral, feasibility, or
positivity properties belong to the statements that use them.

## Main statements

* `sdpDualPayoff`: the shifted matrix combination divided by `4*α`.
* `sdpDualCertificate`: the average of `T` rounds plus the designated offset `δ*α/(2*R)`.
* `sdpDualCertRounds`: the ceiling of `16*R*Real.log D/(δ*η)`, followed by one extra round.

## References

* [Brandao and Svore, 2017][BrandaoSvore2017]
-/

set_option backward.isDefEq.respectTransparency false
open Qatlib.Foundations.PureStateMath

set_option autoImplicit false
noncomputable section
namespace Qatlib.Concepts.SdpDuality.ConeSeparation

open Matrix
open scoped Classical BigOperators Matrix.Norms.L2Operator ComplexOrder

/-- Defines the round payoff as `(4*α)⁻¹ • (∑ i, y s i • A i - Cv + (2*α) • 1)`, shifting and
rescaling the dual matrix combination. -/
def sdpDualPayoff (D m : ℕ) (A : Fin m → Operator D) (Cv : Operator D) (α : ℝ)
    (y : ℕ → Fin m → ℝ) : ℕ → Operator D :=
  fun s => ((4*α : ℝ))⁻¹ • ((∑ i, y s i • A i) - Cv + (2*α) • (1 : Operator D))

/-- Defines the coordinatewise average of the first `T` round vectors, with the extra mass
`δ*α/(2*R)` added at `j₀`. -/
def sdpDualCertificate (m : ℕ) (δ α R : ℝ) (j₀ : Fin m) (y : ℕ → Fin m → ℝ) (T : ℕ) :
    Fin m → ℝ :=
  fun j => (if j = j₀ then δ*α/(2*R) else 0) + (∑ t ∈ Finset.range T, y t j)/T

/-- Defines the natural round count `Nat.ceil (16*R*Real.log D/(δ*η)) + 1`. -/
def sdpDualCertRounds (D : ℕ) (R δ η : ℝ) : ℕ :=
  Nat.ceil (16*R*Real.log D/(δ*η)) + 1

end Qatlib.Concepts.SdpDuality.ConeSeparation
