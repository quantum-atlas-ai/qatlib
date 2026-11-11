/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.QsvtCore.PhaseExistence.GslwSourceQsvt

set_option backward.isDefEq.respectTransparency false

/-!
# GrandUnif21 Theorem 1 — Quantum Signal Processing

Source: arXiv:2105.02859v3, Sec. II A, Theorem 1 and Eq. (4) (lines 93--107 of the
metadata extraction).  The QSP word
`e^{i φ₀ Z} ∏_{k=1}^{d} W(a) e^{i φ_k Z}` acts on the single signal qubit as the
matrix `!![P(a), i Q(a) √(1-a²); i Q*(a) √(1-a²), P*(a)]`, and a legal phase
table of length `d` exists for exactly the polynomial pairs satisfying the
printed conditions (i)--(iii): `deg P ≤ d`, `deg Q ≤ d-1`, the response parity,
and the normalization `P P* + (1-X²) Q Q* = 1` on `[-1,1]`.

The paper-layer statement below is the forward implication used by every later
theorem of the paper.  It is proved by transporting the concrete `Fin 2` signal
word through the Gilyén--Su--Low--Wiebe Eq. (3) shape identity, reusing

* `QuantumAlgorithm.Papers.QSingValue19.PhaseExistence.PhaseSynthesis.CompletedPair`
  (`completedPair_iff_eq3`) for the printed conditions (i)--(iii), and
* `QuantumAlgorithm.Papers.QSingValue19.PhaseExistence.SignalWordTransport`
  for the four-corner display of Eq. (4).

Boundary: matrix-level identity at real signal values `a ∈ [-1,1]`; no gate
compilation, phase-recovery algorithm or numerical stability claim.
-/

set_option autoImplicit false
noncomputable section

open Matrix Polynomial
open Qatlib.Concepts.PhaseGeometry.Phase
open Qatlib.Concepts.TrotterFormula.SuzukiFourth
open Qatlib.Concepts.QsvtCore.PhaseExistence
open Qatlib.Concepts.QsvtCore.PhaseExistence.PhaseSynthesis
open Qatlib.Concepts.QsvtCore.PhaseExistence.GslwSourceQsvt

namespace Qatlib.Papers.GrandUnif21.MainResults.QuantumSignalProcessing

/-- GrandUnif21 Theorem 1, Eq. (4), arXiv:2105.02859v3 p. 5 (metadata lines
93--107): for every completed polynomial pair of degree `d` (conditions
(i)--(iii) of the printed theorem) there is a legal phase table of length `d`
whose QSP word is the printed response matrix at every `a ∈ [-1,1]`.

The hypothesis `CompletedPair d P Q` is the library rendering of the printed
conditions: `deg P ≤ d`, `deg Q < d`, response parity, and the normalization
identity `P·P* + (1-X²)·Q·Q* = 1`. -/
theorem source_theorem1_qsp_response
    {d : ℕ} {P Q : Polynomial ℂ} (h : CompletedPair d P Q) :
    ∃ (base : ℂ) (zs : List ℂ),
      IsPhase base ∧ (∀ z ∈ zs, IsPhase z) ∧ zs.length = d ∧
        ∀ x : ℝ, x ∈ Set.Icc (-1 : ℝ) 1 →
          signalWord x base zs =
            !![P.eval (x : ℂ),
               Complex.I * Real.sqrt (1 - x ^ 2) * Q.eval (x : ℂ);
               Complex.I * Real.sqrt (1 - x ^ 2) *
                 (conjugatePolynomial Q).eval (x : ℂ),
               (conjugatePolynomial P).eval (x : ℂ)] := by
  obtain ⟨base, zs, hb, hzs, hlen, hpair⟩ :=
    (completedPair_iff_eq3 (k := d) (P := P) (Q := Q)).mp h
  refine ⟨base, zs, hb, hzs, hlen, ?_⟩
  intro x hx
  have hshape := signalWordTransport base zs x hx
  rw [hpair] at hshape
  simpa using hshape

/-- The converse direction of GrandUnif21 Theorem 1: any legal QSP word of
length `d` produces a completed pair of degree `d`.  This is the direction the
paper uses to conclude that the printed polynomial conditions are exhaustive. -/
theorem source_theorem1_qsp_conditions
    {d : ℕ} {base : ℂ} {zs : List ℂ}
    (hb : IsPhase base) (hzs : ∀ z ∈ zs, IsPhase z) (hlen : zs.length = d) :
    CompletedPair d (responseP base zs) (responseQ base zs) := by
  subst hlen
  exact completedPair_response hb zs hzs

end Qatlib.Papers.GrandUnif21.MainResults.QuantumSignalProcessing
