/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.SdpDuality.ConeSeparation.SdpRunMacros
set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

open Qatlib.Foundations.PureStateMath

open Qatlib.Concepts.SdpDuality.ConeSeparation

namespace Qatlib.Concepts.SdpMmwSolver.SdpContract

open Matrix
open scoped Classical BigOperators Matrix.Norms.L2Operator ComplexOrder

def SdpRunDecisionContract : Prop :=
  ∀ (D m : ℕ) (A : Fin m → Operator D) (Cv : Operator D) (b : Fin m → ℝ)
    (y : ℕ → Fin m → ℝ) (j₀ : Fin m) (α R δ ε η : ℝ),
    0 < D → 0 < α → 1 ≤ α → 0 < R → 0 < δ → δ ≤ 1 → 0 < ε → 0 < η →
    η + ε ≤ δ/(8*R) → ε ≤ δ/(16*R) →
    (∀ i, (A i).IsHermitian ∧ ‖A i‖ ≤ 1) →
    Cv.IsHermitian ∧ ‖Cv‖ ≤ 1 →
    (∀ i, 1 ≤ b i) → A j₀ = 1 → b j₀ = R →
    ((∃ t₀ : ℕ, t₀ < sdpDualCertRounds D R δ η ∧
        (∀ t ∈ Finset.range t₀, SdpRoundOracleContract D m A Cv b α ε η y t) ∧
        SdpRoundOracleFailure D m A Cv b α R ε η y t₀) →
      ∃ X : Operator D, X.PosSemidef ∧
        (∀ i, (Matrix.trace (A i * X)).re ≤ b i) ∧
        (Matrix.trace X).re ≤ R ∧
        (1 - δ)*α ≤ (Matrix.trace (Cv * X)).re) ∧
    ((∀ t : ℕ, SdpRoundOracleContract D m A Cv b α ε η y t) →
      (0 < sdpDualSampleScale m δ α R j₀ y (sdpDualCertRounds D R δ η) ∧
      (∀ i, 0 ≤ sdpDualSampleDist m δ α R j₀ y (sdpDualCertRounds D R δ η) i) ∧
      (∑ i, sdpDualSampleDist m δ α R j₀ y (sdpDualCertRounds D R δ η) i) = 1 ∧
      (∀ i, sdpDualCertificate m δ α R j₀ y (sdpDualCertRounds D R δ η) i =
        sdpDualSampleScale m δ α R j₀ y (sdpDualCertRounds D R δ η) *
          sdpDualSampleDist m δ α R j₀ y (sdpDualCertRounds D R δ η) i) ∧
      (∑ i, sdpDualCertificate m δ α R j₀ y (sdpDualCertRounds D R δ η) i * b i ≤
        (1+δ)*α) ∧
      ((∑ i, sdpDualCertificate m δ α R j₀ y (sdpDualCertRounds D R δ η) i • A i) -
          Cv).PosSemidef ∧
      (∀ X : Operator D, X.PosSemidef →
        (∀ i, (Matrix.trace (A i * X)).re ≤ b i) →
        (Matrix.trace (Cv * X)).re ≤ (1+δ)*α)))

end Qatlib.Concepts.SdpMmwSolver.SdpContract
