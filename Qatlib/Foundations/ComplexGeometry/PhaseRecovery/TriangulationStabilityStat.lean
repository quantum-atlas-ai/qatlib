/-
Copyright (c) 2026 Quantum Atlas Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quantum Atlas Contributors
-/

module

public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Inverse
public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

@[expose] public section

namespace Qatlib.Foundations.ComplexGeometry.PhaseRecovery

def TriangulationStability : Prop :=
  ∀ (r c θ τ lam ε : ℝ) (R' S' T' C' τ' : ℝ),
    0 < r → 0 < c → 0 < lam → 0 < ε → ε ≤ 1 / 10 → ε * lam ^ 2 * c ^ 2 ≤ r ^ 2 / 10 →
    |R' - r ^ 2| ≤ ε * lam ^ 2 * c ^ 2 →
    |S' - (r ^ 2 + lam ^ 2 * c ^ 2 - 2 * lam * r * c * Real.cos (θ - τ))|
      ≤ ε * lam ^ 2 * c ^ 2 →
    |T' - (r ^ 2 + lam ^ 2 * c ^ 2 - 2 * lam * r * c * Real.sin (θ - τ))|
      ≤ ε * lam ^ 2 * c ^ 2 →
    |C' - lam ^ 2 * c ^ 2| ≤ ε * lam ^ 2 * c ^ 2 →
    ‖Complex.exp ((τ' + (if R' + C' - T' < 0 then -1 else 1)
          * Real.arccos ((R' + C' - S') / (2 * Real.sqrt (R' * C')))) * Complex.I)
        - Complex.exp (θ * Complex.I)‖
      ≤ ‖Complex.exp (τ' * Complex.I) - Complex.exp (τ * Complex.I)‖
        + 1.37 * Real.sqrt ε * (Real.sqrt (lam ^ 2 * c ^ 2 / r ^ 2) + 1)

end Qatlib.Foundations.ComplexGeometry.PhaseRecovery
