/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.SpectralFilter.PhaseReadout.PhaseEstimation
import Qatlib.Foundations.InstrumentCore.Measurement.MeasurementLaws

/-!
# Phase-estimation readout for molecular initial states

This module gives the exact phase-estimation semantics used for the MCSCF initial-state scheme
of [WangEtAl2008]. The state `qpeOutput` starts with a uniform phase register, applies
`ControlledPowers`, and then applies the adjoint Fourier transform to that register.

The readout theorems assume that each relevant eigenvalue is an exact power of the chosen
primitive root. They establish exact eigenstate readout and the linear action on a finite
eigenstate expansion.

## Main statements

* `mcscf_eigenstate_readout_exact`: a normalized eigenstate with phase label `j` yields that
  label with probability one.
* `mcscf_superposition_readout`: a finite eigenstate expansion becomes the corresponding sum of
  phase-label kets tensored with the unchanged eigenstates.

## References

* [Wang et al., 2008][WangEtAl2008]
-/

set_option warningAsError false

set_option autoImplicit false
noncomputable section

open Matrix
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.SpectralFilter.PhaseReadout

open scoped BigOperators Classical

namespace Qatlib.Papers.EnergySpec09.MainResults

variable {I : Type*} [Fintype I] [DecidableEq I]

/-- The phase-estimation output obtained from a uniform `Fin M` phase register tensored with
`ψ`, followed by controlled powers of `U` and the adjoint Fourier transform on the phase
register. -/
noncomputable def qpeOutput (M : ℕ) (U : Matrix I I ℂ) (ψ : QState I) : QState (Fin M × I) :=
  ApplyGate (TensorGate (QFTMatrix M)ᴴ (1 : Matrix I I ℂ))
    (ControlledPowers U M *ᵥ
      TensorState (fun _ : Fin M => (Real.sqrt (M : ℝ) : ℂ)⁻¹) ψ)

/-- A normalized eigenstate whose eigenvalue has exact phase label `j : Fin M` yields that label
with probability one when `M` is positive. This is the exact-grid eigenstate readout used
for the MCSCF scheme in [WangEtAl2008]. -/
theorem mcscf_eigenstate_readout_exact {M : ℕ} (hM : 0 < M) {U : Matrix I I ℂ}
    {ψ : QState I} (hψn : Normalized ψ) (j : Fin M)
    (heig : U *ᵥ ψ = (primRoot M ^ ((j.val : ℤ))) • ψ) :
    MeasureProb (qpeOutput M U ψ) ({j} ×ˢ (Finset.univ : Finset I)) = 1 := by
  unfold qpeOutput
  exact (qpe_exact_readout hM hψn j heig).2

/-- For a finite expansion of eigenstates with exactly representable phases, phase estimation
produces the coefficient-weighted sum of phase-label kets tensored with the corresponding
eigenstates. This is the linear readout identity underlying the scheme in [WangEtAl2008]. -/
theorem mcscf_superposition_readout {M : ℕ} (hM : 0 < M) (U : Matrix I I ℂ)
    {Idx : Type*} [Fintype Idx] (c : Idx → ℂ) (φ : Idx → QState I) (k : Idx → Fin M)
    (heig : ∀ i, U *ᵥ (φ i) = (primRoot M ^ (((k i).val : ℤ))) • (φ i)) :
    ApplyGate (TensorGate (QFTMatrix M)ᴴ (1 : Matrix I I ℂ))
        (ControlledPowers U M *ᵥ (∑ i, c i • TensorState
          (fun _ : Fin M => (Real.sqrt (M : ℝ) : ℂ)⁻¹) (φ i)))
      = ∑ i, c i • TensorState (Ket (k i)) (φ i) :=
  qpe_exact_readout_linear M hM U c φ k heig

end Qatlib.Papers.EnergySpec09.MainResults
