/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Foundations.InstrumentCore.Measurement.Basic
import Qatlib.Papers.VarTimeAmpAmp10.CoherentAA.TightAASuccessBound

set_option backward.isDefEq.respectTransparency false

/-!
# Source Lemma 1 — the tight amplitude-amplification success bound

Fixed source: Ambainis, *Variable time amplitude amplification and a faster
quantum algorithm for solving systems of linear equations*, fixed preprint
**arXiv:1010.4458v2** (14 Nov 2010).  Lemma 1 is printed on p.5 (eqs. (2)–(3));
the reference is Aaronson–Ambainis.

Source statement.  Let `A` be a quantum algorithm that outputs `|ψ⟩` with
probability `δ ≤ ε`.  If the iteration count satisfies

  `m ≤ π/(4·arcsin√ε) − 1/2`   (2)

then there is an algorithm `A′` using `2m+1` calls to `A` and `A⁻¹` that outputs
`|ψ⟩` with probability

  `δ_new ≥ (1 − (2m+1)²δ/3)·(2m+1)²δ`.   (3)

The frozen library proves exactly this about the *actual* prepared
amplitude-amplification circuit: `QuantumAlgorithm.Papers.VarTimeAmpAmp10.
CoherentAA.clause88` gives, for the real circuit `preparedAACircuit A j₀ r` run on
`|j₀⟩`, the bound `tightAASuccess δ r ≤ MeasureProb out S`, the preservation of
the target direction, and `2r+1` input queries.  The paper-layer theorem below
restates those three conclusions of (3) (probability, output direction, query
count) for an explicit circuit and proves them by that frozen result.
-/

open Qatlib.Foundations.InstrumentCore.Measurement
open Qatlib.Concepts.AdaptiveCP.BranchTrace.CompletelyPositive
open Qatlib.Concepts.PhaseErrorBound.PhaseErrorSum
open Qatlib.Foundations.QueryWordCore.Circuit
open Qatlib.Concepts.PhaseErrorBound.PhaseErrorSum.ResourceCost
open Qatlib.Concepts.LchsSimulation.StaticLchs
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.SpectralReadout.PhaseReadout
open Qatlib.Papers.VarTimeAmpAmp10.CoherentAA
open scoped Classical BigOperators ENNReal Matrix.Norms.L2Operator

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.VarTimeAmpAmp10.CoherentAA

/-- Fixed arXiv:1010.4458v2, Lemma 1 (printed p.5, eqs. (2)–(3)).

For a unitary preparation `A` on a finite register `I` whose success mass on the
readout set `S` is `δ ≤ ε`, and an odd amplification count `r` inside the
source's window `r ≤ π/(4 arcsin√ε) − 1/2`, the actual amplified circuit
`preparedAACircuit A j₀ r` succeeds on `S` with probability at least
`tightAASuccess δ r = (1 − (2r+1)²δ/3)(2r+1)²δ`, keeps the prepared success
direction, and uses exactly `2r+1` calls to `A`/`A⁻¹`.

Reused frozen result: `QuantumAlgorithm.Papers.VarTimeAmpAmp10.CoherentAA.clause88`
(second conjunct), whose first conjunct `coherentAmplification_answer` supplies
the `sin²` law of the same circuit. -/
theorem source_lemma1 (I : Type) [Fintype I] [DecidableEq I]
    (A : Matrix I I ℂ) (j₀ : I) (S : Finset I) (ε δ : ℝ) (r : ℕ)
    (hA : A ∈ Matrix.unitaryGroup I ℂ)
    (hε0 : 0 < ε) (hε1 : ε ≤ 1) (hδ0 : 0 ≤ δ) (hδε : δ ≤ ε)
    (hwin : (r : ℝ) ≤ tightAAWindow ε)
    (hδ : MeasureProb (preparedAAState A j₀) S = δ) :
    tightAASuccess δ r ≤
        MeasureProb (Run (preparedMark S) (preparedAACircuit A j₀ r) (Ket j₀)) S ∧
      (∃ c : ℂ, Collapse (Run (preparedMark S) (preparedAACircuit A j₀ r) (Ket j₀)) S
        = c • Collapse (preparedAAState A j₀) S) ∧
      preparedInputQueries (preparedAAWord j₀ r) = 2 * r + 1 := by
  exact clause88.2 I A j₀ S ε δ r hA hε0 hε1 hδ0 hδε hwin hδ

end Qatlib.Papers.VarTimeAmpAmp10.CoherentAA
