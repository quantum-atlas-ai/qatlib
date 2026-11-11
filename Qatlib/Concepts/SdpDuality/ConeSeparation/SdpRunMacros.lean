/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.SdpDuality.ConeSeparation.Macros

/-!
# SDP round contracts and dual sampling expressions

This module defines `SdpRoundOracleContract` and `SdpRoundOracleFailure` for matrix
multiplicative weights states. The former imposes nonnegative weights, a cost bound, and an
approximate payoff inequality; the latter gives a lower cost bound for every vector meeting a
relaxed payoff threshold.

`sdpDualSampleScale` and `sdpDualSampleDist` extract the total mass and normalized coordinates
of the corrected dual certificate. These definitions express oracle and output quantities used
in the quantum SDP framework of [BrandaoSvore2017].

## Main definitions

* `SdpRoundOracleContract`: successful round conditions.
* `SdpRoundOracleFailure`: relaxed payoff separator condition.
* `sdpDualSampleDist`: normalization of the dual certificate.

## References

* [Brandao and Svore, 2017][BrandaoSvore2017]
-/

set_option warningAsError false
set_option backward.isDefEq.respectTransparency false
open Qatlib.Foundations.QueryWordCore.Circuit Qatlib.Concepts.ReferenceError.MixturePaths
open Qatlib.Concepts.MatrixWeights.WeightsCore
open Qatlib.Foundations.PureStateMath

set_option autoImplicit false
noncomputable section
namespace Qatlib.Concepts.SdpDuality.ConeSeparation

open Matrix
open scoped Classical BigOperators Matrix.Norms.L2Operator ComplexOrder

/-- The round oracle condition requiring nonnegative dual weights, cost at most `α`, and payoff
within `2 * α * ε` of the objective on the current multiplicative weights state. -/
def SdpRoundOracleContract (D m : ℕ) (A : Fin m → Operator D) (Cv : Operator D)
    (b : Fin m → ℝ) (α ε η : ℝ) (y : ℕ → Fin m → ℝ) (t : ℕ) : Prop :=
  (∀ i, 0 ≤ y t i) ∧ (∑ i, b i * y t i ≤ α) ∧
    (∑ i, y t i * (Matrix.trace (A i * mmwState D (sdpDualPayoff D m A Cv α y) η t)).re ≥
      (Matrix.trace (Cv * mmwState D (sdpDualPayoff D m A Cv α y) η t)).re - 2*α*ε)

/-- The failure certificate asserting that any nonnegative vector reaching the relaxed payoff
threshold has cost at least `α * (1 - 3 * R * ε)`. -/
def SdpRoundOracleFailure (D m : ℕ) (A : Fin m → Operator D) (Cv : Operator D)
    (b : Fin m → ℝ) (α R ε η : ℝ) (y : ℕ → Fin m → ℝ) (t₀ : ℕ) : Prop :=
  ∀ z : Fin m → ℝ, (∀ i, 0 ≤ z i) →
    (∑ i, z i * (Matrix.trace (A i * mmwState D (sdpDualPayoff D m A Cv α y) η t₀)).re ≥
      (Matrix.trace (Cv * mmwState D (sdpDualPayoff D m A Cv α y) η t₀)).re - 3*α*ε) →
    α*(1 - 3*R*ε) ≤ ∑ i, z i * b i

/-- The sum of the coordinates of the corrected SDP dual certificate. -/
def sdpDualSampleScale (m : ℕ) (δ α R : ℝ) (j₀ : Fin m) (y : ℕ → Fin m → ℝ) (T : ℕ) : ℝ :=
  ∑ i, sdpDualCertificate m δ α R j₀ y T i

/-- The corrected SDP dual certificate divided coordinatewise by its total mass. -/
def sdpDualSampleDist (m : ℕ) (δ α R : ℝ) (j₀ : Fin m) (y : ℕ → Fin m → ℝ) (T : ℕ) :
    Fin m → ℝ :=
  fun i => sdpDualCertificate m δ α R j₀ y T i / sdpDualSampleScale m δ α R j₀ y T

end Qatlib.Concepts.SdpDuality.ConeSeparation
