/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.MbqcFlow.FlowDecision.MbqcFlowCoreDefs
import Qatlib.Concepts.UniformBqp.FiniteGateWord.FiniteGatePhaseBoundary
open Qatlib.Foundations.PureStateMath
set_option backward.isDefEq.respectTransparency false
set_option warningAsError false

open Qatlib
open Qatlib
open Matrix
open scoped Classical ComplexOrder

set_option autoImplicit false
set_option warningAsError false

open Qatlib.Concepts.AdaptiveCP.BranchTrace
open Qatlib.Concepts.MbqcFlow.FlowDecision Qatlib.Foundations.PureStateMath

namespace Qatlib.Concepts.MbqcFlow.FlowDecision.MbqcFlowPreentangled

theorem clause2_clause1 :
    ∀ (n : ℕ) (gs : List (ClusterNetworkGate n)) (hg : networkLegal gs)
      (hist : Fin gs.length → Bool × Bool) (ρ : Operator (2 ^ n)),
      (mbqcPreentangledInstrument gs hg).branch hist ρ
        = (networkHistoryInstrument gs hg).branch hist ρ :=
  fun _n gs hg hist ρ => mbqcPreentangledInstrument_branch gs hg hist ρ

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

theorem clause2_clause4 :
    ∀ (n : ℕ) (gs : List (ClusterNetworkGate n)) (hg : networkLegal gs)
      (ρ : Operator (2 ^ n)) (hist : Fin gs.length → Bool × Bool),
      ρ.PosSemidef →
        instrumentProb (networkHistoryInstrument gs hg) ρ hist = 0 →
          (mbqcPreentangledInstrument gs hg).branch hist ρ = 0 := by
  intro n gs hg ρ hist hρ hprob
  rw [mbqcPreentangledInstrument_branch gs hg hist ρ]
  exact (instrumentProb_eq_zero_iff (networkHistoryInstrument gs hg) hρ hist).mp hprob

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
