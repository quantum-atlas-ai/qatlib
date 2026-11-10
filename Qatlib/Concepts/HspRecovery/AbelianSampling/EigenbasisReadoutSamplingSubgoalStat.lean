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

def EigenbasisReadoutSamplingSubgoal : Prop :=
  ∀ (M : ℕ), 0 < M →
  ∀ (Idx I : Type) [Fintype Idx] [DecidableEq Idx] [Fintype I] [DecidableEq I]
    (U : Matrix I I ℂ) (ψ : Idx → QState I) (k : Idx → Fin M) (c : Idx → ℂ)
    (S : Finset (Fin M)),
    (∀ i j, Inner (ψ i) (ψ j) = if i = j then 1 else 0) →
    (∀ i, U *ᵥ ψ i = (primRoot M ^ (((k i).val : ℤ))) • ψ i) →
    (∑ i, ‖c i‖ ^ 2 = 1) →
    MeasureProb (ApplyGate (TensorGate (QFTMatrix M)ᴴ (1 : Matrix I I ℂ))
        (ControlledPowers U M *ᵥ (∑ i, c i • TensorState
          (fun _ : Fin M => (Real.sqrt (M : ℝ) : ℂ)⁻¹) (ψ i))))
        ((S : Finset (Fin M)) ×ˢ (Finset.univ : Finset I))
      = ∑ i ∈ Finset.univ.filter (fun i => k i ∈ S), ‖c i‖ ^ 2

end Qatlib.Concepts.HspRecovery.AbelianSampling
