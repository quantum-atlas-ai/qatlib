/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.SdpDuality.ConeSeparation.Macros
set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

open Qatlib.Foundations.PureStateMath

open Qatlib.Concepts.SdpDuality.ConeSeparation
open Qatlib.Concepts.MatrixWeights.WeightsCore

namespace Qatlib.Concepts.SdpMmwSolver.BranchProofs

open Matrix
open scoped Classical BigOperators Matrix.Norms.L2Operator ComplexOrder

def SdpDualCertificateMacro : Prop :=
  ∀ (D m : ℕ) (A : Fin m → Operator D) (Cv : Operator D) (b : Fin m → ℝ)
    (y : ℕ → Fin m → ℝ) (j₀ : Fin m) (α R δ ε η : ℝ),
    0 < D → 0 < α → 1 ≤ α → 0 < R → 0 < δ → 0 < ε → 0 < η →
    η + ε ≤ δ/(8*R) →
    (∀ i, (A i).IsHermitian ∧ ‖A i‖ ≤ 1) →
    Cv.IsHermitian ∧ ‖Cv‖ ≤ 1 →
    (∀ i, 1 ≤ b i) →
    A j₀ = 1 → b j₀ = R →
    (∀ t, (∀ i, 0 ≤ y t i) ∧ (∑ i, b i * y t i ≤ α) ∧
      (∑ i, y t i * (Matrix.trace (A i * mmwState D (sdpDualPayoff D m A Cv α y) η t)).re ≥
        (Matrix.trace (Cv * mmwState D (sdpDualPayoff D m A Cv α y) η t)).re - 2*α*ε)) →
    (∀ i, 0 ≤ sdpDualCertificate m δ α R j₀ y (sdpDualCertRounds D R δ η) i) ∧
    (∑ i, sdpDualCertificate m δ α R j₀ y (sdpDualCertRounds D R δ η) i * b i ≤ (1+δ)*α) ∧
    ((∑ i, sdpDualCertificate m δ α R j₀ y (sdpDualCertRounds D R δ η) i • A i) - Cv).PosSemidef

end Qatlib.Concepts.SdpMmwSolver.BranchProofs
