/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.SdpDuality.ConeSeparation.Macros
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

def SdpRoundOracleContract (D m : ℕ) (A : Fin m → Operator D) (Cv : Operator D)
    (b : Fin m → ℝ) (α ε η : ℝ) (y : ℕ → Fin m → ℝ) (t : ℕ) : Prop :=
  (∀ i, 0 ≤ y t i) ∧ (∑ i, b i * y t i ≤ α) ∧
    (∑ i, y t i * (Matrix.trace (A i * mmwState D (sdpDualPayoff D m A Cv α y) η t)).re ≥
      (Matrix.trace (Cv * mmwState D (sdpDualPayoff D m A Cv α y) η t)).re - 2*α*ε)

def SdpRoundOracleFailure (D m : ℕ) (A : Fin m → Operator D) (Cv : Operator D)
    (b : Fin m → ℝ) (α R ε η : ℝ) (y : ℕ → Fin m → ℝ) (t₀ : ℕ) : Prop :=
  ∀ z : Fin m → ℝ, (∀ i, 0 ≤ z i) →
    (∑ i, z i * (Matrix.trace (A i * mmwState D (sdpDualPayoff D m A Cv α y) η t₀)).re ≥
      (Matrix.trace (Cv * mmwState D (sdpDualPayoff D m A Cv α y) η t₀)).re - 3*α*ε) →
    α*(1 - 3*R*ε) ≤ ∑ i, z i * b i

def sdpDualSampleScale (m : ℕ) (δ α R : ℝ) (j₀ : Fin m) (y : ℕ → Fin m → ℝ) (T : ℕ) : ℝ :=
  ∑ i, sdpDualCertificate m δ α R j₀ y T i

def sdpDualSampleDist (m : ℕ) (δ α R : ℝ) (j₀ : Fin m) (y : ℕ → Fin m → ℝ) (T : ℕ) :
    Fin m → ℝ :=
  fun i => sdpDualCertificate m δ α R j₀ y T i / sdpDualSampleScale m δ α R j₀ y T

end Qatlib.Concepts.SdpDuality.ConeSeparation
