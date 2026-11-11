/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.SolovayKitaev05.MainResults.FixedGateSynthesisDefs
import Qatlib.Concepts.MatrixAccess.RitzPipeline.FixedGateSynthesis
import Qatlib.Concepts.NumericalWord.MixedWordError.FixedGateSynthesis
import Qatlib.Concepts.MatrixAccess.RitzPipeline.FixedGateCompiler

/-!
# Fixed-gate synthesis acceptance and resource ledgers

This module assembles acceptance, structural, and resource facts for fixed-gate synthesis
requests in the setting of [DawsonNielsen2006]. It proves exact acceptance of fixed primitives,
dyadic angle bounds, and legality, width, and polynomial word-length properties for supplied
middle-window synthesizers; `clause1_endpoint`, `clause2_endpoint`, and `clause3_endpoint`
package these facts.

## Main statements

* `clause1_endpoint`: Fixed primitives are accepted exactly, dyadic phase angles satisfy the
  stated size bounds, and supplied middle-window segments have zero oracle calls,
  fixed-primitive gates, and sufficient width.
* `clause3_endpoint`: Supplied middle-window synthesizers satisfy polynomial word-length bounds;
  request bit counts agree with `synthInputBits`, and synthesis gate counts equal letter counts.

## References

* [Dawson and Nielsen, 2006][DawsonNielsen2006]
-/

set_option backward.isDefEq.respectTransparency false
set_option warningAsError false
open Qatlib.Concepts.NumericalWord.MixedWordError
open Qatlib.Foundations.InstrumentCore.ProjectiveMeasurement Qatlib.Concepts.PhaseErrorBound.PhaseErrorSum
open Qatlib.Concepts.MatrixAccess.RitzPipeline

namespace Qatlib.Papers.SolovayKitaev05.MainResults

open Matrix
open Qatlib

open scoped Classical BigOperators

set_option autoImplicit false

/-- A fixed primitive gate is accepted at every requested precision when represented by its
singleton word. -/
theorem fixed_primitive_exact {w : ℕ} (g : LocalQFTGate w) (k : ℕ)
    (hg : IsFixedPrim g) : Accepts w g k ⟨w, [g]⟩ :=
  exactAccepts_of_isFixedPrim g k hg

/-- The absolute dyadic phase angle is `2*pi / 2^e`, independently of its sign flag. -/
theorem dyadic_phase_angle_abs (e : ℕ) (neg : Bool) :
    |dyadicPhaseAngle e neg| = 2 * Real.pi / (2 ^ e : ℝ) :=
  Qatlib.Concepts.MatrixAccess.RitzPipeline.dyadicPhaseAngle_abs e neg

/-- If `k + 2 ≤ e`, half the absolute dyadic phase angle is at most `tolerance k`. -/
theorem small_angle_below_tolerance (e k : ℕ) (neg : Bool) (he : k + 2 ≤ e) :
    |dyadicPhaseAngle e neg| / 2 ≤ tolerance k :=
  Qatlib.Concepts.MatrixAccess.RitzPipeline.smallAngle_tol_le e k neg he

/-- The next segment produced by a supplied middle-window synthesizer makes no answer-oracle
calls. -/
theorem middle_window_zero_oracle (S : MiddleWindowSynthesizer) (w : ℕ)
    (g : LocalQFTGate w) (k : ℕ) : answerOracleCalls (nextSegment S w g k) = 0 :=
  nextSegment_zero_oracle S g k

/-- Every gate in the next segment produced by a supplied middle-window synthesizer is a fixed
primitive. -/
theorem middle_window_legal (S : MiddleWindowSynthesizer) (w : ℕ)
    (g : LocalQFTGate w) (k : ℕ) :
    ∀ h ∈ (nextSegment S w g k).word, IsFixedPrim h :=
  nextSegment_legal S g k

/-- The next segment's width equals the input width plus some natural-number ancilla count. -/
theorem middle_window_width (S : MiddleWindowSynthesizer) (w : ℕ)
    (g : LocalQFTGate w) (k : ℕ) :
    ∃ a : ℕ, (nextSegment S w g k).width = w + a :=
  nextSegment_width S g k

/-- For each supplied middle-window synthesizer, next-segment word length is bounded by a
polynomial in request size for precision at least one. -/
theorem middle_window_ledger (S : MiddleWindowSynthesizer) :
    ∃ C D : ℕ, ∀ (w : ℕ) (g : LocalQFTGate w) (k : ℕ), 1 ≤ k →
      (nextSegment S w g k).word.length ≤ C * (requestSize w g k) ^ D :=
  nextSegment_ledger S

/-- The synthesis-word gate count equals its letter count, and its oracle-call count is zero. -/
theorem synthesis_word_ledger (p : SynthWord) :
    synthWordGates p = p.letters.length ∧ synthWordOracleCalls p = 0 :=
  ⟨rfl, rfl⟩

/-- An accepted synthesis word has input width plus some ancillas, is legal, and makes no oracle
calls. -/
theorem accepted_word_structure {w : ℕ} (g : LocalQFTGate w) (k : ℕ) (p : SynthWord)
    (h : synthesisWordAccepted w g k p) :
    (∃ a : ℕ, p.width = w + a) ∧ synthWordLegal p ∧ synthWordOracleCalls p = 0 := by
  rcases h with ⟨ha, hl, ho, _, _⟩
  exact ⟨ha, hl, ho⟩

/-- A valid angle input approximates any specified gate angle within `2^(-bits)` and is an
integer multiple of `1 / 2^bits`. -/
theorem angle_input_is_dyadic {w : ℕ} (g : LocalQFTGate w) (bits : ℕ) (q : ℚ)
    (h : Qatlib.Concepts.NumericalWord.MixedWordError.angleInputOK g bits q) :
    ∀ θ, gateAngle g = some θ →
      |((q : ℝ) - θ)| ≤ ((2 : ℝ) ⁻¹) ^ bits ∧ ∃ m : ℤ, q = m / ((2 : ℚ) ^ bits) := by
  intro θ hθ
  unfold Qatlib.Concepts.NumericalWord.MixedWordError.angleInputOK at h
  rw [hθ] at h
  exact h

/-- Fixed primitives are accepted exactly, dyadic phase angles satisfy the stated size bounds,
and supplied middle-window segments have zero oracle calls, fixed-primitive gates, and
sufficient width. -/
theorem clause1_endpoint :
    (∀ {w : ℕ} (g : LocalQFTGate w) (k : ℕ), IsFixedPrim g →
      Accepts w g k ⟨w, [g]⟩) ∧
    (∀ (e : ℕ) (neg : Bool), |dyadicPhaseAngle e neg| = 2 * Real.pi / (2 ^ e : ℝ)) ∧
    (∀ (e k : ℕ) (neg : Bool), k + 2 ≤ e →
      |dyadicPhaseAngle e neg| / 2 ≤ tolerance k) ∧
    (∀ (S : MiddleWindowSynthesizer) (w : ℕ) (g : LocalQFTGate w) (k : ℕ),
      answerOracleCalls (nextSegment S w g k) = 0) ∧
    (∀ (S : MiddleWindowSynthesizer) (w : ℕ) (g : LocalQFTGate w) (k : ℕ),
      ∀ h ∈ (nextSegment S w g k).word, IsFixedPrim h) ∧
    (∀ (S : MiddleWindowSynthesizer) (w : ℕ) (g : LocalQFTGate w) (k : ℕ),
      ∃ a : ℕ, (nextSegment S w g k).width = w + a) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro w g k hg
    exact fixed_primitive_exact g k hg
  · intro e neg
    exact dyadic_phase_angle_abs e neg
  · intro e k neg he
    exact small_angle_below_tolerance e k neg he
  · intro S w g k
    exact middle_window_zero_oracle S w g k
  · intro S w g k
    exact middle_window_legal S w g k
  · intro S w g k
    exact middle_window_width S w g k

/-- Valid angle inputs are dyadic approximations, synthesis gate counts equal letter counts, and
accepted synthesis words have legal gates, sufficient width, and zero oracle calls. -/
theorem clause2_endpoint :
    (∀ {w : ℕ} (g : LocalQFTGate w) (bits : ℕ) (q : ℚ), Qatlib.Concepts.NumericalWord.MixedWordError.angleInputOK g bits q →
      ∀ θ, gateAngle g = some θ →
        |((q : ℝ) - θ)| ≤ ((2 : ℝ) ⁻¹) ^ bits ∧
          ∃ m : ℤ, q = m / ((2 : ℚ) ^ bits)) ∧
    (∀ (p : SynthWord), synthWordGates p = p.letters.length ∧
      synthWordOracleCalls p = 0) ∧
    (∀ {w : ℕ} (g : LocalQFTGate w) (k : ℕ) (p : SynthWord),
      synthesisWordAccepted w g k p →
        (∃ a : ℕ, p.width = w + a) ∧ synthWordLegal p ∧ synthWordOracleCalls p = 0) := by
  refine ⟨?_, ?_, ?_⟩
  · intro w g bits q h θ hθ
    exact angle_input_is_dyadic g bits q h θ hθ
  · intro p
    exact synthesis_word_ledger p
  · intro w g k p h
    exact accepted_word_structure g k p h

/-- Supplied middle-window synthesizers satisfy polynomial word-length bounds; request bit
counts agree with `synthInputBits`, and synthesis gate counts equal letter counts. -/
theorem clause3_endpoint :
    (∀ (S : MiddleWindowSynthesizer), ∃ C D : ℕ,
      ∀ (w : ℕ) (g : LocalQFTGate w) (k : ℕ), 1 ≤ k →
        (nextSegment S w g k).word.length ≤ C * (requestSize w g k) ^ D) ∧
    (∀ {w : ℕ} (r : SynthesisRequest w),
      requestBits r = Qatlib.Concepts.NumericalWord.MixedWordError.synthInputBits w r.gate r.precision) ∧
    (∀ (p : SynthWord), synthWordGates p = p.letters.length) := by
  refine ⟨?_, ?_, ?_⟩
  · intro S
    exact middle_window_ledger S
  · intro w r
    rfl
  · intro p
    exact (synthesis_word_ledger p).1

end Qatlib.Papers.SolovayKitaev05.MainResults
