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

namespace Qatlib.Concepts.HspRecovery.KitaevReadout

def PhaseEstimationExactSubgoal : Prop :=
  ∀ (M : ℕ) (I : Type) [Fintype I] [DecidableEq I] (U : Matrix I I ℂ),
    0 < M → ∀ (ψ : QState I), Normalized ψ → ∀ (j : Fin M),
      U *ᵥ ψ = (primRoot M ^ ((j.val : ℤ))) • ψ →
      ApplyGate (TensorGate (QFTMatrix M)ᴴ (1 : Matrix I I ℂ))
          (ControlledPowers U M *ᵥ TensorState (fun _ : Fin M =>
            (Real.sqrt (M : ℝ) : ℂ)⁻¹) ψ)
        = TensorState (Ket j) ψ ∧
      MeasureProb (ApplyGate (TensorGate (QFTMatrix M)ᴴ (1 : Matrix I I ℂ))
          (ControlledPowers U M *ᵥ TensorState (fun _ : Fin M =>
            (Real.sqrt (M : ℝ) : ℂ)⁻¹) ψ))
        ({j} ×ˢ (Finset.univ : Finset I)) = 1

end Qatlib.Concepts.HspRecovery.KitaevReadout
