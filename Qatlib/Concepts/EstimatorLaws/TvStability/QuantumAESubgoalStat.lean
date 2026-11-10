/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.SpectralFilter.PhaseReadout.PhaseEstimation
set_option warningAsError false

open Matrix

open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.SpectralFilter.PhaseReadout

namespace Qatlib.Concepts.EstimatorLaws.TvStability

def QuantumAESubgoal : Prop :=
  ∀ (M : ℕ) (I : Type) [Fintype I] [DecidableEq I] (W : Matrix I I ℂ),
    W ∈ Matrix.unitaryGroup I ℂ → 0 < M →
    ∀ (ψ₀ ψ₁ : QState I), Normalized ψ₀ → Normalized ψ₁ → Inner ψ₀ ψ₁ = 0 →
    ∀ (θ : ℝ) (j : Fin M),
      W *ᵥ ψ₀ = ((Real.cos (2 * θ) : ℝ) : ℂ) • ψ₀ - ((Real.sin (2 * θ) : ℝ) : ℂ) • ψ₁ →
      W *ᵥ ψ₁ = ((Real.sin (2 * θ) : ℝ) : ℂ) • ψ₀ + ((Real.cos (2 * θ) : ℝ) : ℂ) • ψ₁ →
      2 * θ = 2 * Real.pi * (j.val : ℝ) / M →
      (ApplyGate (TensorGate (QFTMatrix M)ᴴ (1 : Matrix I I ℂ))
          (ControlledPowers W M *ᵥ TensorState
            (fun _ : Fin M => ((Real.sqrt (M : ℝ) : ℂ))⁻¹)
            (((Real.sqrt 2 : ℝ) : ℂ)⁻¹ • (ψ₀ + (Complex.I) • ψ₁))))
        = TensorState (Ket j) (((Real.sqrt 2 : ℝ) : ℂ)⁻¹ • (ψ₀ + Complex.I • ψ₁)) ∧
      Real.sin (Real.pi * (j.val : ℝ) / M) ^ 2 = Real.sin θ ^ 2

end Qatlib.Concepts.EstimatorLaws.TvStability
