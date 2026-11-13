/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.CopyEvolution.Discriminate.TimedTwoSpeciesSpectralReadoutStat

/-!
# Timed spectral-readout guarantees

This module proves `TimedTwoSpeciesSpectralReadout`, combining the timed finite-copy QPE state
estimate with the ideal spectral label formula. For a density input and a unitary
diagonalization of `ρ - σ`, every label event approximates the corresponding spectral QPE kernel
mixture within `32 * (M - 1) * τ ^ 2 / n`.

The result also includes normalization of the output and label masses, together with the four
QPE resource counts. It supplies finite-copy spectral guarantees for the discrimination
construction of [LloydMohseniRebentrost2014].

## Main statements

* `timedTwoSpeciesSpectralReadout`: normalized spectral readout with finite-copy event error and
  exact resource counts.

## References

* [Lloyd, Mohseni, and Rebentrost, 2014][LloydMohseniRebentrost2014]
-/

open Qatlib.Concepts.BlockEncoding.LCU Qatlib.Foundations.PureStateMath.BornBridge
set_option backward.isDefEq.respectTransparency false

open Qatlib.Concepts.FreshCopyExec.QpeConsumers
open Qatlib.Concepts.SpectralReadout.OffGridPhaseReadout

set_option autoImplicit false
namespace Qatlib.Concepts.CopyEvolution.Discriminate
open Matrix
open scoped Classical BigOperators ComplexOrder

/-- The timed two-species spectral-readout specification holds, giving a normalized output and
label law, exact resource counts, and event-mass error at most `32 * (M - 1) * τ ^ 2 / n`.
This supports the discrimination application of [LloydMohseniRebentrost2014]. -/
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
