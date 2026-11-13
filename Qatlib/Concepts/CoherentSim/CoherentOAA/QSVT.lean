/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.TrotterFormula.SuzukiFourth.QSP
import Qatlib.Concepts.CoherentSim.CoherentOAA.Qubitization

/-!
# Phased alternating sequences for QSVT

This module defines the phased alternating sequence of an oracle and its adjoint, with rotations
about the two signal projectors. Its action on a signal pair is determined by the signal and
residual response polynomials, following [GilyenSuLowWiebe2019].

The parity of the phase-list length selects the source frame. Compression removes the residual
term and gives the odd cross-frame and even same-frame singular-pair identities.

## Main statements

* `phasedAlternating_unitary`: unit phases and orthogonal signal projectors give a unitary
  sequence.
* `SignalPair.phased_response`: the full signal-pair action is the two-polynomial response.
* `qsvt_odd`: odd sequences transform a supplied singular pair between frames.
* `qsvt_even_left`: even sequences transform the left singular sector within its frame.

## References

* [Gilyén et al., 2019][GilyenSuLowWiebe2019]
-/

open Qatlib.Concepts.TrotterFormula.SuzukiFourth
open Qatlib.Concepts.Execution.WorkspaceCP

open Qatlib.Concepts.PhaseGeometry.Phase
open Qatlib.Foundations.InstrumentCore.ProjectiveMeasurement

namespace Qatlib.Concepts.CoherentSim.CoherentOAA

open Matrix Polynomial
open Qatlib
open Qatlib
open Qatlib
open Qatlib
variable {H K : Type*} [Fintype H] [DecidableEq H]

/-- The recursive phased sequence alternating `U` and `Uᴴ`, exchanging the signal projectors at
each step and ending with the base rotation. See [Gilyén et al., Definition
15][GilyenSuLowWiebe2019]. -/
noncomputable def phasedAlternating (U P Q : Matrix H H ℂ) (base : ℂ) :
    List ℂ → Matrix H H ℂ
  | [] => phaseRotation Q base
  | z :: zs => phaseRotation Q z * U * phasedAlternating Uᴴ Q P base zs

/-- The parity-dependent source, equal to `l` for an empty list and exchanging `r` and `l` at
each list step. -/
def alternatingSource {α : Type*} (r l : α) : List ℂ → α
  | [] => l
  | _ :: zs => alternatingSource l r zs

/-- The alternating source is `l` for even list length and `r` for odd list length. -/
theorem alternatingSource_eq {α : Type*} (r l : α) (zs : List ℂ) :
    alternatingSource r l zs = if zs.length % 2 = 0 then l else r := by
  induction zs generalizing r l with
  | nil => simp [alternatingSource]
  | cons z zs ih =>
    rw [alternatingSource, ih]
    by_cases h : zs.length % 2 = 0
    · have hs : (zs.length + 1) % 2 ≠ 0 := by omega
      simp [List.length_cons, h, hs]
    · have hs : (zs.length + 1) % 2 = 0 := by omega
      simp [List.length_cons, h, hs]

/-- The phased alternating sequence is unitary when the oracle is unitary, the signal projectors
are orthogonal, and every phase has unit modulus. -/
theorem phasedAlternating_unitary {U P Q : Matrix H H ℂ}
    (hU : U ∈ Matrix.unitaryGroup H ℂ) (hP : IsOrthogonalProjector P)
    (hQ : IsOrthogonalProjector Q) {base : ℂ} (hb : IsPhase base)
    (zs : List ℂ) (hzs : ∀ z ∈ zs, IsPhase z) :
    phasedAlternating U P Q base zs ∈ Matrix.unitaryGroup H ℂ := by
  induction zs generalizing U P Q with
  | nil => exact phaseRotation_unitary hQ hb
  | cons z zs ih =>
    exact (Matrix.unitaryGroup H ℂ).mul_mem
      ((Matrix.unitaryGroup H ℂ).mul_mem
        (phaseRotation_unitary hQ (hzs z (by simp))) hU)
      (ih (adjoint_unitary hU) hQ hP (fun w hw => hzs w (List.mem_cons_of_mem z hw)))

/-- The phased sequence acts on its parity-selected signal source by the signal response times
`l` plus the residual response times the left residual. -/
theorem SignalPair.phased_response {U P Q : Matrix H H ℂ} {σ : ℂ}
    {r l : Matrix H K ℂ} (h : SignalPair U P Q σ r l) (base : ℂ) (zs : List ℂ) :
    phasedAlternating U P Q base zs * alternatingSource r l zs =
      (responseP base zs).eval σ • l +
        (responseQ base zs).eval σ • leftResidual U σ r l := by
  induction zs generalizing U P Q r l with
  | nil =>
    simpa [phasedAlternating, alternatingSource] using
      phaseRotation_mul_of_fixed h.left_fixed base
  | cons z zs ih =>
    rw [phasedAlternating, alternatingSource, Matrix.mul_assoc, ih h.adjoint]
    have hs := h.step z ((responseP base zs).eval σ) ((responseQ base zs).eval σ)
    simpa [leftResidual, rightResidual, responseP_cons, responseQ_cons] using hs

/-- Projection onto the left signal space removes the residual response and leaves the signal
polynomial evaluated at `σ` times `l`. -/
theorem SignalPair.projected_response {U P Q : Matrix H H ℂ} {σ : ℂ}
    {r l : Matrix H K ℂ} (h : SignalPair U P Q σ r l) (base : ℂ) (zs : List ℂ) :
    Q * phasedAlternating U P Q base zs * alternatingSource r l zs =
      (responseP base zs).eval σ • l := by
  rw [Matrix.mul_assoc, h.phased_response]
  simp [Matrix.mul_add, h.left_fixed, h.leftResidual_zero]

section Rectangular

variable {I O : Type*} [Fintype I] [Fintype O] [DecidableEq I] [DecidableEq O]

/-- For a supplied singular pair, left compression of the phased sequence acting on its
parity-selected source equals the response polynomial at `σ` times `w`. -/
theorem qsvt_singularPair {A : Matrix O I ℂ} {U : Matrix H H ℂ}
    {L : Matrix H O ℂ} {R : Matrix H I ℂ}
    (h : ProjectedUnitaryEncoding A U L R) {σ : ℂ}
    {v : Matrix I K ℂ} {w : Matrix O K ℂ}
    (hav : A * v = σ • w) (haw : Aᴴ * w = σ • v) (base : ℂ) (zs : List ℂ) :
    Lᴴ * (phasedAlternating U (rangeProjector R) (rangeProjector L) base zs *
      alternatingSource (R * v) (L * w) zs) = (responseP base zs).eval σ • w := by
  have hp := (signalPair_of_encoding h hav haw).projected_response base zs
  have hL : Lᴴ * L = 1 := h.left_isometry
  have he := congrArg (fun M : Matrix H K ℂ => Lᴴ * M) hp
  simpa [rangeProjector, ← Matrix.mul_assoc, hL] using he

/-- For odd phase-list length, cross-frame compression transforms the supplied singular pair by
the response polynomial evaluated at `σ`. -/
theorem qsvt_odd {A : Matrix O I ℂ} {U : Matrix H H ℂ}
    {L : Matrix H O ℂ} {R : Matrix H I ℂ}
    (h : ProjectedUnitaryEncoding A U L R) {σ : ℂ}
    {v : Matrix I K ℂ} {w : Matrix O K ℂ}
    (hav : A * v = σ • w) (haw : Aᴴ * w = σ • v) (base : ℂ) (zs : List ℂ)
    (hodd : zs.length % 2 = 1) :
    compress L (phasedAlternating U (rangeProjector R) (rangeProjector L) base zs) R * v =
      (responseP base zs).eval σ • w := by
  have he := qsvt_singularPair h hav haw base zs
  simpa [compress, Matrix.mul_assoc, alternatingSource_eq, hodd] using he

/-- For even phase-list length, left-frame compression acts on the supplied left singular sector
by the response polynomial evaluated at `σ`. -/
theorem qsvt_even_left {A : Matrix O I ℂ} {U : Matrix H H ℂ}
    {L : Matrix H O ℂ} {R : Matrix H I ℂ}
    (h : ProjectedUnitaryEncoding A U L R) {σ : ℂ}
    {v : Matrix I K ℂ} {w : Matrix O K ℂ}
    (hav : A * v = σ • w) (haw : Aᴴ * w = σ • v) (base : ℂ) (zs : List ℂ)
    (heven : zs.length % 2 = 0) :
    compress L (phasedAlternating U (rangeProjector R) (rangeProjector L) base zs) L * w =
      (responseP base zs).eval σ • w := by
  have he := qsvt_singularPair h hav haw base zs
  simpa [compress, Matrix.mul_assoc, alternatingSource_eq, heven] using he

/-- For even phase-list length, right-frame compression of the adjoint-oracle sequence acts on
the supplied right singular sector by the response polynomial evaluated at `σ`. -/
theorem qsvt_even_right {A : Matrix O I ℂ} {U : Matrix H H ℂ}
    {L : Matrix H O ℂ} {R : Matrix H I ℂ}
    (h : ProjectedUnitaryEncoding A U L R) {σ : ℂ}
    {v : Matrix I K ℂ} {w : Matrix O K ℂ}
    (hav : A * v = σ • w) (haw : Aᴴ * w = σ • v) (base : ℂ) (zs : List ℂ)
    (heven : zs.length % 2 = 0) :
    compress R (phasedAlternating Uᴴ (rangeProjector L) (rangeProjector R) base zs) R * v =
      (responseP base zs).eval σ • v := by
  exact qsvt_even_left h.adjoint haw (by simpa using hav) base zs heven

end Rectangular

end Qatlib.Concepts.CoherentSim.CoherentOAA
