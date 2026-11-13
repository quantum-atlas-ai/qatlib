/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.MbqcFlow.FlowDecision.MbqcFlowCoreDefs
import Qatlib.Concepts.UniformBqp.FiniteGateWord.FiniteGatePhaseBoundary

/-!
# Preentangled compilation preserves network histories

This module proves that preentangled compilation agrees with the network history instrument on
every branch and on the channel obtained by forgetting histories. It also records the Bell-word
resource counts and proves that zero-probability histories on positive semidefinite inputs have
zero output.

The statements are collected in `g2` and formalize concrete compilation properties in the
measurement-based setting of [RaussendorfBriegel2001].

## Main statements

* `clause2_clause1`: equality of individual history branches.
* `clause2_clause2`: equality after forgetting histories.
* `clause2_clause3`: Bell-word and general preentangling resource counts.
* `clause2_clause4`: zero-probability branches vanish.
* `g2`: the conjunction of these properties.

## References

* [Raussendorf and Briegel, 2001][RaussendorfBriegel2001]
-/

open Qatlib.Foundations.PureStateMath
set_option backward.isDefEq.respectTransparency false

open Qatlib
open Qatlib
open Matrix
open scoped Classical ComplexOrder

set_option autoImplicit false

open Qatlib.Concepts.AdaptiveCP.BranchTrace
open Qatlib.Concepts.MbqcFlow.FlowDecision Qatlib.Foundations.PureStateMath

namespace Qatlib.Concepts.MbqcFlow.FlowDecision.MbqcFlowPreentangled

/-- Preentangled compilation and the network history instrument have identical branches for
every legal gate word and outcome history. -/
theorem clause2_clause1 :
    ∀ (n : ℕ) (gs : List (ClusterNetworkGate n)) (hg : networkLegal gs)
      (hist : Fin gs.length → Bool × Bool) (ρ : Operator (2 ^ n)),
      (mbqcPreentangledInstrument gs hg).branch hist ρ
        = (networkHistoryInstrument gs hg).branch hist ρ :=
  fun _n gs hg hist ρ => mbqcPreentangledInstrument_branch gs hg hist ρ

/-- Forgetting outcomes gives the same channel for preentangled compilation and the network
history instrument. -/
theorem clause2_clause2 :
    ∀ (n : ℕ) (gs : List (ClusterNetworkGate n)) (hg : networkLegal gs),
      (mbqcPreentangledInstrument gs hg).forget.map
        = (networkHistoryInstrument gs hg).forget.map := by
  intro n gs hg
  apply LinearMap.ext
  intro ρ
  rw [Instrument.forget_apply, Instrument.forget_apply]
  exact Finset.sum_congr rfl fun hist _ =>
    mbqcPreentangledInstrument_branch gs hg hist ρ

/-- The legal Bell word has length three, gate counts `(2, 1)`, one preentangling step, three
measurements, and two feedback and communication bits. For every gate word, its
preentangling count equals the second network count. -/
theorem clause2_clause3 :
    networkLegal mbqcBellWord
      ∧ mbqcBellWord.length = 3
      ∧ networkCounts mbqcBellWord = (2, 1)
      ∧ mbqcPreentangleCount mbqcBellWord = 1
      ∧ mbqcMeasureCount mbqcBellWord = 3
      ∧ mbqcFeedbackBits mbqcBellWord = 2
      ∧ mbqcCommBits mbqcBellWord = 2
      ∧ ∀ (n : ℕ) (gs : List (ClusterNetworkGate n)),
          mbqcPreentangleCount gs = (networkCounts gs).2 := by
  refine ⟨mbqcBellWord_legal, by decide, by decide, by decide, by decide, by decide,
    by decide, fun _n gs => rfl⟩

/-- On positive semidefinite input, a history of zero probability under the network history
instrument has zero preentangled output branch. -/
theorem clause2_clause4 :
    ∀ (n : ℕ) (gs : List (ClusterNetworkGate n)) (hg : networkLegal gs)
      (ρ : Operator (2 ^ n)) (hist : Fin gs.length → Bool × Bool),
      ρ.PosSemidef →
        instrumentProb (networkHistoryInstrument gs hg) ρ hist = 0 →
          (mbqcPreentangledInstrument gs hg).branch hist ρ = 0 := by
  intro n gs hg ρ hist hρ hprob
  rw [mbqcPreentangledInstrument_branch gs hg hist ρ]
  exact (instrumentProb_eq_zero_iff (networkHistoryInstrument gs hg) hρ hist).mp hprob

/-- Preentangled compilation preserves every history branch and the channel obtained by
forgetting histories, with the stated Bell-word resource counts and zero-probability
behavior. This packages the compilation properties in the measurement-based setting of
[RaussendorfBriegel2001]. -/
theorem g2 :
    (∀ (n : ℕ) (gs : List (ClusterNetworkGate n)) (hg : networkLegal gs)
        (hist : Fin gs.length → Bool × Bool) (ρ : Operator (2 ^ n)),
        (mbqcPreentangledInstrument gs hg).branch hist ρ
          = (networkHistoryInstrument gs hg).branch hist ρ)
    ∧ (∀ (n : ℕ) (gs : List (ClusterNetworkGate n)) (hg : networkLegal gs),
        (mbqcPreentangledInstrument gs hg).forget.map
          = (networkHistoryInstrument gs hg).forget.map)
    ∧ (networkLegal mbqcBellWord
      ∧ mbqcBellWord.length = 3
      ∧ networkCounts mbqcBellWord = (2, 1)
      ∧ mbqcPreentangleCount mbqcBellWord = 1
      ∧ mbqcMeasureCount mbqcBellWord = 3
      ∧ mbqcFeedbackBits mbqcBellWord = 2
      ∧ mbqcCommBits mbqcBellWord = 2
      ∧ ∀ (n : ℕ) (gs : List (ClusterNetworkGate n)),
          mbqcPreentangleCount gs = (networkCounts gs).2)
    ∧ (∀ (n : ℕ) (gs : List (ClusterNetworkGate n)) (hg : networkLegal gs)
        (ρ : Operator (2 ^ n)) (hist : Fin gs.length → Bool × Bool),
        ρ.PosSemidef →
          instrumentProb (networkHistoryInstrument gs hg) ρ hist = 0 →
            (mbqcPreentangledInstrument gs hg).branch hist ρ = 0) :=
  ⟨clause2_clause1, clause2_clause2, clause2_clause3, clause2_clause4⟩
end Qatlib.Concepts.MbqcFlow.FlowDecision.MbqcFlowPreentangled
