/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.MbqcFlow.FlowDecision.MbqcFlowCore

/-!
# Causal Pauli corrections supplied by flow

This module extracts flow witnesses for an MBQC graph and proves that `flowCorrection`, with
output flow values masked, consists of Pauli wire corrections and is causal in the flow order.
It also defines `PatternRealizesEmbedding` through equality of corrected density branches with a
prescribed matrix action, within the one-way framework of [DanosKashefi2006].

## Main statements

* `flowPattern_corrections_pauli_causal`: An MBQC flow possesses strict-order witnesses whose
  output-masked flow corrections are Pauli wire operators and depend causally on measurement
  outcomes.
* `PatternRealizesEmbedding`: The existence of a measurement order and Pauli wire corrections
  making every XY-plane density branch equal to `U * ρ * Uᴴ`.

## References

* [Danos and Kashefi, 2006][DanosKashefi2006]
-/

set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false
noncomputable section

open Matrix
open Qatlib.Concepts.MbqcFlow.FlowDecision Qatlib.Foundations.PureStateMath
open scoped Classical BigOperators ComplexOrder

namespace Qatlib.Papers.OneWayDanos05.MainResults

/-- An MBQC flow possesses strict-order witnesses whose output-masked flow corrections are Pauli
wire operators and depend causally on measurement outcomes [DanosKashefi2006]. -/
theorem flowPattern_corrections_pauli_causal {n : ℕ} (G : MbqcGraph n)
    (I O : Finset (Fin n)) (h : MbqcHasFlow G I O) :
    ∃ (f : Fin n → Option (Fin n)) (prec : Fin n → Fin n → Prop),
      IsStrictOrder (Fin n) prec ∧
      (∀ v : Fin n, v ∉ O → ∃ w : Fin n,
        f v = some w ∧ mbqcAdj G v w ∧ w ∉ I ∧ prec v w ∧
          ∀ k : Fin n, mbqcAdj G w k → k ≠ v → prec v k) ∧
      (∀ s : Fin n → Bool, ∀ u : Fin n,
        MbqcPauliWire (flowCorrection G (clause6Aux_outMaskedFlow f O) s u)) ∧
      MbqcCausalCorrection prec (flowCorrection G (clause6Aux_outMaskedFlow f O)) := by
  obtain ⟨f, prec, _dp, hord, hF⟩ := h
  refine ⟨f, prec, hord, hF, ?_, flowCorrection_causal G (clause6Aux_outMaskedFlow f O) prec ?_ ?_⟩
  · intro s u
    exact flowCorrection_pauliWire G (clause6Aux_outMaskedFlow f O) s u
  · intro v u hfu
    by_cases hv : v ∈ O
    · simp [clause6Aux_outMaskedFlow, hv] at hfu
    · have hf' : f v = some u := by simpa [clause6Aux_outMaskedFlow, hv] using hfu
      obtain ⟨w, hw, _, _, hprec, _⟩ := hF v hv
      have hwu : w = u := by
        have hsame : some w = some u := hw.symm.trans hf'
        simpa using hsame
      rw [hwu] at hprec
      exact hprec
  · intro v w u hfw hne hadj
    by_cases hv : v ∈ O
    · simp [clause6Aux_outMaskedFlow, hv] at hfw
    · have hf' : f v = some w := by simpa [clause6Aux_outMaskedFlow, hv] using hfw
      obtain ⟨w', hw', _, _, _, hF3⟩ := hF v hv
      have hww : w' = w := by
        have hsame : some w' = some w := hw'.symm.trans hf'
        simpa using hsame
      rw [hww] at hF3
      exact hF3 u hadj hne

/-- The existence of a measurement order and Pauli wire corrections making every XY-plane
density branch equal to `U * ρ * Uᴴ`. -/
def PatternRealizesEmbedding {n : ℕ} (G : MbqcGraph n) (I O : Finset (Fin n))
    (a : Fin n → ℝ) (U : Matrix (Fin (2 ^ O.card)) (Fin (2 ^ I.card)) ℂ) : Prop :=
  ∃ (r : Fin n → Fin n) (corr : (Fin n → Bool) → Fin n → Operator 2),
    (∀ s : Fin n → Bool, ∀ v : Fin n, MbqcPauliWire (corr s v)) ∧
    ∀ ρ : Operator (2 ^ I.card), IsDensityOperator ρ →
      ∀ s : Fin n → Bool,
        mbqcPatternBranch G I O r (fun _ => MbqcPlane.XY) a corr s ρ
          = U * ρ * U.conjTranspose

end Qatlib.Papers.OneWayDanos05.MainResults
