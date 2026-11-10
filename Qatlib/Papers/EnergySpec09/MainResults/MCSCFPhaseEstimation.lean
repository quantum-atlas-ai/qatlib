/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.SpectralFilter.PhaseReadout.PhaseEstimation
import Qatlib.Foundations.InstrumentCore.Measurement.MeasurementLaws
set_option warningAsError false

set_option autoImplicit false
noncomputable section

open Matrix
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.SpectralFilter.PhaseReadout

open scoped BigOperators Classical

namespace Qatlib.Papers.EnergySpec09.MainResults

variable {I : Type*} [Fintype I] [DecidableEq I]

noncomputable def qpeOutput (M : ℕ) (U : Matrix I I ℂ) (ψ : QState I) : QState (Fin M × I) :=
  ApplyGate (TensorGate (QFTMatrix M)ᴴ (1 : Matrix I I ℂ))
    (ControlledPowers U M *ᵥ
      TensorState (fun _ : Fin M => (Real.sqrt (M : ℝ) : ℂ)⁻¹) ψ)

theorem mcscf_eigenstate_readout_exact {M : ℕ} (hM : 0 < M) {U : Matrix I I ℂ}
    {ψ : QState I} (hψn : Normalized ψ) (j : Fin M)
    (heig : U *ᵥ ψ = (primRoot M ^ ((j.val : ℤ))) • ψ) :
    MeasureProb (qpeOutput M U ψ) ({j} ×ˢ (Finset.univ : Finset I)) = 1 := by
  unfold qpeOutput
  exact (qpe_exact_readout hM hψn j heig).2

theorem mcscf_superposition_readout {M : ℕ} (hM : 0 < M) (U : Matrix I I ℂ)
    {Idx : Type*} [Fintype Idx] (c : Idx → ℂ) (φ : Idx → QState I) (k : Idx → Fin M)
    (heig : ∀ i, U *ᵥ (φ i) = (primRoot M ^ (((k i).val : ℤ))) • (φ i)) :
    ApplyGate (TensorGate (QFTMatrix M)ᴴ (1 : Matrix I I ℂ))
        (ControlledPowers U M *ᵥ (∑ i, c i • TensorState
          (fun _ : Fin M => (Real.sqrt (M : ℝ) : ℂ)⁻¹) (φ i)))
      = ∑ i, c i • TensorState (Ket (k i)) (φ i) :=
  qpe_exact_readout_linear M hM U c φ k heig

end Qatlib.Papers.EnergySpec09.MainResults
