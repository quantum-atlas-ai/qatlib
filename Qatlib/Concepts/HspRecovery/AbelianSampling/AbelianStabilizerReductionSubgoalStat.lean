/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.SpectralFilter.PhaseReadout.PhaseEstimation

/-!
# Specification of exact stabilizer phase readout

`AbelianStabilizerReductionSubgoal` specifies the exact action of controlled powers and an
inverse Fourier transform on a finite eigenvector superposition. Each uniform control register
is replaced by the basis ket for its eigenvalue label, with the coefficient and eigenvector
retained. [Kitaev1995]

## Main statements

* `AbelianStabilizerReductionSubgoal`: the proposition specifying linear exact phase readout.

## References

* [Kitaev, 1995][Kitaev1995]
-/

open Matrix

open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.SpectralFilter.PhaseReadout

namespace Qatlib.Concepts.HspRecovery.AbelianSampling

/-- The proposition that controlled powers and an inverse Fourier transform replace the uniform
control state by the exact phase ket in every term of a finite eigenvector superposition on
the `M`th root of unity grid. -/
def AbelianStabilizerReductionSubgoal : Prop :=
  ∀ (M : ℕ), 0 < M →
  ∀ (Idx I : Type) [Fintype Idx] [DecidableEq Idx] [Fintype I] [DecidableEq I]
    (U : Matrix I I ℂ) (c : Idx → ℂ) (ψ : Idx → QState I) (k : Idx → Fin M),
    (∀ i, U *ᵥ (ψ i) = (primRoot M ^ (((k i).val : ℤ))) • (ψ i)) →
    ApplyGate (TensorGate (QFTMatrix M)ᴴ (1 : Matrix I I ℂ))
        (ControlledPowers U M *ᵥ (∑ i, c i • TensorState
          (fun _ : Fin M => (Real.sqrt (M : ℝ) : ℂ)⁻¹) (ψ i)))
      = ∑ i, c i • TensorState (Ket (k i)) (ψ i)

end Qatlib.Concepts.HspRecovery.AbelianSampling
