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

namespace Qatlib.Concepts.HspRecovery.AbelianSampling

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
