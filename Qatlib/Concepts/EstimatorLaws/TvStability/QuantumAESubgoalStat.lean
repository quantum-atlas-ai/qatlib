/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.SpectralFilter.PhaseReadout.PhaseEstimation

/-!
# Exact-grid amplitude-estimation contract

States exact-grid phase readout for the normalized complex eigenstate of an orthonormal
two-dimensional rotation plane. The proposition isolates the exact readout and squared-sine
decoding properties used in amplitude-estimation arguments such as those in [Montanaro2015].

## Main statements

* `QuantumAESubgoal` requires a unitary rotation action, an angle exactly on the `M`-point grid,
  and concludes exact phase-register output together with squared-sine decoding.

## References

* [Montanaro, 2015][Montanaro2015]
-/

open Matrix

open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.SpectralFilter.PhaseReadout

namespace Qatlib.Concepts.EstimatorLaws.TvStability

/-- The proposition requiring exact phase-estimation output on `(ψ₀ + i ψ₁) / sqrt 2` when a
unitary rotates the orthonormal plane by `2 * θ` and that angle lies on the `M`-point grid.
It also specifies that the decoded squared sine equals `sin² θ`. -/
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
