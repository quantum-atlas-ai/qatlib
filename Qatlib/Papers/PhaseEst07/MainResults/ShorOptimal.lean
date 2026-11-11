/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.PhaseEst07.MainResults.OptimalPOVM
import Qatlib.Papers.PhaseEst07.MainResults.DiscretePOVM

/-!
# Fourier measurement identities for the Shor example

The function `sourceShorSpectrum` records the powers-of-two spectrum used in the Shor example.
The theorem `source_shor_qft_measurement_optimal` packages phase-state orthonormality, Fourier
preparation, and the explicit constant-one-kernel Holevo cost under the stated coefficient and
amplitude hypotheses. The phase-estimation setting is described in [VanDamEtAl2007].

## Main statements

* `source_shor_spectrum_one`: The first value of `sourceShorSpectrum` is one.
* `source_shor_qft_measurement_optimal`: For positive index size, nonnegative cost coefficients,
  and positive amplitudes, the phase states are orthonormal, the Fourier transform prepares them
  from basis states, and the constant-one kernel has the displayed Holevo cost.

## References

* [van Dam et al., 2007][VanDamEtAl2007]
-/

set_option warningAsError false

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.PhaseEst07.MainResults.ShorOptimal

open Qatlib.Concepts.SpectralFilter.PhaseReadout
open Qatlib.Foundations.PureStateMath
open Qatlib.Papers.PhaseEst07.MainResults.OptimalPOVM
open Qatlib.Papers.PhaseEst07.MainResults.DiscretePOVM
open Matrix
open scoped BigOperators

/-- The spectrum value `2 ^ (l - 1)`, using natural-number subtraction. -/
def sourceShorSpectrum (l : ℕ) : ℕ := 2 ^ (l - 1)

/-- The first value of `sourceShorSpectrum` is one. -/
theorem source_shor_spectrum_one : sourceShorSpectrum 1 = 1 := by
  unfold sourceShorSpectrum
  norm_num

/-- For positive index size, nonnegative cost coefficients, and positive amplitudes, the phase
states are orthonormal, the Fourier transform prepares them from basis states, and the
constant-one kernel has the displayed Holevo cost. See [van Dam et al.,
2007][VanDamEtAl2007]. -/
theorem source_shor_qft_measurement_optimal {q : ℕ} (hq : 1 ≤ q) (c : ℕ → ℝ)
    (hc : ∀ l, 0 ≤ c l) (ψ : Fin q → ℝ) (hψ : ∀ k, 0 < ψ k) :
    (∀ s t : Fin q, Inner (PhaseState q s) (PhaseState q t) = if s = t then 1 else 0) ∧
    (∀ s : Fin q, ApplyGate (QFTMatrix q) (Ket s) = PhaseState q s) ∧
    (sourceHolevoCost c ψ sourceUnitChi
      = - c 0 - (1 / 2) * ∑ l ∈ Finset.Icc 1 (q - 1), |c l| *
          ∑ h : Fin q, ∑ k : Fin q,
            (if sourceDist h k = l then ψ h * ψ k else 0)) := by
  have hqpos : 0 < q := by omega
  refine ⟨?_, ?_, ?_⟩
  · intro s t
    exact source_phase_state_orthonormal q hqpos s t
  · intro s
    exact source_qft_prepares_phase_state q s
  · exact (source_holevo_cost_optimal hq c hc ψ hψ sourceUnitChi
      (fun _ _ => by simp [sourceUnitChi])).2

end Qatlib.Papers.PhaseEst07.MainResults.ShorOptimal
