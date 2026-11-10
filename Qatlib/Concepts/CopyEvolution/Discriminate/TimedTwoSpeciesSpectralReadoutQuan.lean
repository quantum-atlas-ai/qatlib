/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.CopyEvolution.Discriminate.TimedTwoSpeciesSpectralReadoutStat
open Qatlib.Concepts.BlockEncoding.LCU Qatlib.Foundations.PureStateMath.BornBridge
set_option warningAsError false
set_option backward.isDefEq.respectTransparency false


open Qatlib.Concepts.FreshCopyExec.QpeConsumers
open Qatlib.Concepts.SpectralReadout.OffGridPhaseReadout

set_option autoImplicit false
namespace Qatlib.Concepts.CopyEvolution.Discriminate
open Matrix
open scoped Classical BigOperators ComplexOrder

theorem timedTwoSpeciesSpectralReadout : TimedTwoSpeciesSpectralReadout := by
  intro d M n τ ρ σ V x χ hM hn hρ hσ hV hs hχ
  have hstate := timed_two_species_qpe_actual_program_state_error d M n τ hM hn ρ σ χ hρ hσ hχ
  refine ⟨hstate.1, hstate.2.1, ?_, rfl, ?_⟩
  · rw [copyQPELabelMass_sum, hstate.2.1, Complex.one_re]
  · intro E
    have he : (∑ z ∈ E, copyQPELabelMass d M (timedTwoSpeciesQPEIdealOutput d M τ ρ σ χ) z) =
        ∑ j, ((Vᴴ * χ * V) j j).re * (∑ z ∈ E, ‖qpeKernel M (-τ * x j / (2 * Real.pi)) z‖ ^ 2) := by
      simp only [timedTwoSpeciesQPEIdealOutput_spectral_label d M τ (by omega) ρ σ V x hV hs χ hχ]
      rw [Finset.sum_comm]
      exact Finset.sum_congr rfl (fun j _ => (Finset.mul_sum _ _ _).symm)
    have h := (copyQPELabelMass_event_error d M E
      (timedTwoSpeciesQPEOutput d M n τ ρ σ χ)
      (timedTwoSpeciesQPEIdealOutput d M τ ρ σ χ)).trans hstate.2.2
    rwa [he] at h

end Qatlib.Concepts.CopyEvolution.Discriminate
