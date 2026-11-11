/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.CopyEvolution.Discriminate.TimedTwoSpeciesCopyPhaseReadout

/-!
# Specification of timed spectral readout

This module defines `TimedTwoSpeciesSpectralReadout`, the proposition specifying
phase-estimation output for a density-operator difference evolved for time `τ`. Its ideal
comparison law is a spectral-weighted sum of squared `qpeKernel` amplitudes at phases `-τ * x j
/ (2 * π)`.

The proposition requires density and label-law normalization, explicit resource counts, and an
event-mass error at most `32 * (M - 1) * τ ^ 2 / n` for positive copy count and `M ≥ 2`. This
states a finite-copy version of the spectral readout underlying [LloydMohseniRebentrost2014].

## Main statements

* `TimedTwoSpeciesSpectralReadout`: the timed output, event-accuracy, and resource
  specification.

## References

* [Lloyd, Mohseni, and Rebentrost, 2014][LloydMohseniRebentrost2014]
-/

open Qatlib.Concepts.BlockEncoding.LCU Qatlib.Foundations.PureStateMath.BornBridge
set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

open Qatlib.Concepts.QueryComplexity.DegreeMethod

open Qatlib.Concepts.FreshCopyExec.QpeConsumers
open Qatlib.Concepts.SpectralReadout.OffGridPhaseReadout

open Qatlib.Foundations.PureStateMath

set_option autoImplicit false
namespace Qatlib.Concepts.CopyEvolution.Discriminate
open Matrix
open scoped ComplexOrder BigOperators

/-- The proposition asserting density and label-law normalization, exact QPE resource counts,
and a finite-copy event-mass bound against the ideal spectral QPE kernel mixture at time
`τ`. -/
def TimedTwoSpeciesSpectralReadout : Prop :=
  ∀ (d M n : ℕ) (τ : ℝ) (ρ σ V : Operator d) (x : Fin d → ℝ)
    (χ : Operator d),
    2 ≤ M → 0 < n → IsDensityOperator ρ → IsDensityOperator σ →
    V ∈ Matrix.unitaryGroup (Fin d) ℂ →
    ρ-σ = V * Matrix.diagonal (fun j => (x j : ℂ)) * Vᴴ →
    IsDensityOperator χ →
    (timedTwoSpeciesQPEOutput d M n τ ρ σ χ).PosSemidef ∧
    Matrix.trace (timedTwoSpeciesQPEOutput d M n τ ρ σ χ) = 1 ∧
    (∑ z : Fin M, copyQPELabelMass d M (timedTwoSpeciesQPEOutput d M n τ ρ σ χ) z) = 1 ∧
    twoSpeciesQPEResources M n = (2*(M-1)*n,2*(M-1)*n,2*(M-1)*n,0) ∧
    ∀ E : Finset (Fin M),
      |(∑ z ∈ E, copyQPELabelMass d M (timedTwoSpeciesQPEOutput d M n τ ρ σ χ) z) -
        (∑ j, ((Vᴴ*χ*V) j j).re * (∑ z ∈ E, ‖qpeKernel M (-τ*x j/(2*Real.pi)) z‖^2))|
        ≤ 32*(M-1 : ℕ)*τ^2/(n : ℝ)

end Qatlib.Concepts.CopyEvolution.Discriminate
