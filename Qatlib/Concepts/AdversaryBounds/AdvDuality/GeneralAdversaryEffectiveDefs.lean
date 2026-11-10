/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.AdversaryBounds.AdvDuality.GeneralAdversaryExt
import Qatlib.Concepts.AdversaryBounds.AdvDuality.ObservedTruncationEvent
import Qatlib.Concepts.GramQueryCore.GammaDuality.FilteredGamma2Optimization
import Qatlib.Concepts.AdversaryBounds.AdvDuality.GeneralAdversaryCompilation
import Qatlib.Concepts.AdversaryBounds.AdvDuality.GeneralAdversaryFourBitWitness
import Qatlib.Concepts.AdversaryBounds.AdvDuality.GeneralAdversaryInstrumentMinimax
import Qatlib.Concepts.AdversaryBounds.AdvDuality.GeneralAdversaryIteration
import Qatlib.Concepts.AdversaryBounds.AdvDuality.GeneralAdversaryNegativeWeightComp
import Qatlib.Concepts.AdversaryBounds.AdvDuality.GeneralAdversaryPhaseOracle
import Qatlib.Concepts.AdversaryBounds.AdvDuality.GeneralAdversarySdpDuality
import Qatlib.Concepts.AdversaryBounds.AdvDuality.GeneralAdversarySourceOptimizers
import Qatlib.Concepts.AdversaryBounds.AdvDuality.GeneralAdversaryStatementAnswers
import Qatlib.Concepts.AdversaryBounds.AdvDuality.GeneralAdversaryUnboundedBinaryBounds
set_option backward.isDefEq.respectTransparency false
set_option warningAsError false

set_option autoImplicit false

noncomputable section

open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.ShadowModels.ShadowChannel

open Qatlib.Concepts.Execution.CircuitCompile
open Qatlib.Concepts.GramQueryCore.GammaDuality

namespace Qatlib.Concepts.AdversaryBounds.AdvDuality

open Matrix
open scoped Classical BigOperators Matrix.Norms.L2Operator ComplexOrder ENNReal
open Qatlib
open Qatlib
open Qatlib
open Qatlib

inductive LossTag : Type where
  | lost : LossTag
deriving Fintype, DecidableEq

abbrev LossTagged (O : Type) := O ⊕ LossTag

def lossOutcome {O : Type} : LossTagged O := .inr .lost

def IsLoss {O : Type} : LossTagged O → Prop
  | .inl _ => False
  | .inr _ => True

@[simp] theorem isLoss_inl (O : Type) (o : O) : ¬ IsLoss (O := O) (.inl o) := by
  simp [IsLoss]

@[simp] theorem isLoss_inr (O : Type) (t : LossTag) : IsLoss (O := O) (.inr t) := by
  simp [IsLoss]

abbrev LossDecode (Y : Type) := Bool → List (ℕ × ℕ) → LossTagged Y

def lossTagAnswerEvent {I Y : Type} [DecidableEq Y] (decode : LossDecode Y) (y : Y) :
    BranchTrace I → Bool :=
  fun t => match decode t.accepted t.outcomes with
    | .inl o => decide (o = y)
    | .inr _ => false

def lossTagAnyAnswerEvent {I Y : Type} (decode : LossDecode Y) : BranchTrace I → Bool :=
  fun t => match decode t.accepted t.outcomes with
    | .inl _ => true
    | .inr _ => false

def lossTagLossEvent {I Y : Type} (decode : LossDecode Y) : BranchTrace I → Bool :=
  fun t => match decode t.accepted t.outcomes with
    | .inl _ => false
    | .inr _ => true

theorem lossTagLossEvent_eq_not_any {I Y : Type} (decode : LossDecode Y) (t : BranchTrace I) :
    lossTagLossEvent decode t = ! lossTagAnyAnswerEvent decode t := by
  cases h : decode t.accepted t.outcomes <;>
    simp [lossTagLossEvent, lossTagAnyAnswerEvent, h]

theorem lossTagAnswerEvent_le_any {I Y : Type} [DecidableEq Y] (decode : LossDecode Y) (y : Y)
    (t : BranchTrace I) (h : lossTagAnswerEvent decode y t = true) :
    lossTagAnyAnswerEvent decode t = true := by
  cases hdec : decode t.accepted t.outcomes with
  | inl o =>
    simp [lossTagAnyAnswerEvent, hdec]
  | inr t' =>
    simp [lossTagAnswerEvent, hdec] at h

noncomputable def lossTagSuccessMass {I Y : Type} [Fintype I] [DecidableEq I] [DecidableEq Y]
    (O : Matrix I I ℂ) (program : ObservedCircuit I) (ψ : QState I) (decode : LossDecode Y)
    (y : Y) : ℝ :=
  observedEventMass O program ψ (lossTagAnswerEvent decode y)

noncomputable def lossTagAnyAnswerMass {I Y : Type} [Fintype I] [DecidableEq I]
    (O : Matrix I I ℂ) (program : ObservedCircuit I) (ψ : QState I) (decode : LossDecode Y) : ℝ :=
  observedEventMass O program ψ (lossTagAnyAnswerEvent decode)

noncomputable def lossTagLossMass {I Y : Type} [Fintype I] [DecidableEq I]
    (O : Matrix I I ℂ) (program : ObservedCircuit I) (ψ : QState I) (decode : LossDecode Y) : ℝ :=
  observedEventMass O program ψ (lossTagLossEvent decode)

abbrev InstrumentLossDecode (Y : Type) := Bool → List (ℕ × ℕ) → LossTagged Y

def instrumentLossTagAnswerEvent {Y : Type} [DecidableEq Y] (decode : InstrumentLossDecode Y)
    (y : Y) : Bool → List (ℕ × ℕ) → Bool :=
  fun accepted outcomes => match decode accepted outcomes with
    | .inl o => decide (o = y)
    | .inr _ => false

def instrumentLossTagAnyAnswerEvent {Y : Type} (decode : InstrumentLossDecode Y) :
    Bool → List (ℕ × ℕ) → Bool :=
  fun accepted outcomes => match decode accepted outcomes with
    | .inl _ => true
    | .inr _ => false

def instrumentLossTagLossEvent {Y : Type} (decode : InstrumentLossDecode Y) :
    Bool → List (ℕ × ℕ) → Bool :=
  fun accepted outcomes => match decode accepted outcomes with
    | .inl _ => false
    | .inr _ => true

noncomputable def instrumentTotalMass {d : ℕ} (O : Operator d) (P : InstrumentCircuit d)
    (rho : Operator d) : ℝ :=
  instrumentCircuitEventMass O P rho (fun _ _ => true)

noncomputable def instrumentLossTagSuccessMass {d : ℕ} {Y : Type} (O : Operator d) (P : InstrumentCircuit d)
    (rho : Operator d) (decode : InstrumentLossDecode Y) (y : Y) : ℝ :=
  instrumentCircuitEventMass O P rho (instrumentLossTagAnswerEvent decode y)

noncomputable def instrumentLossTagAnyAnswerMass {d : ℕ} {Y : Type} (O : Operator d) (P : InstrumentCircuit d)
    (rho : Operator d) (decode : InstrumentLossDecode Y) : ℝ :=
  instrumentCircuitEventMass O P rho (instrumentLossTagAnyAnswerEvent decode)

noncomputable def instrumentLossTagLossMass {d : ℕ} {Y : Type} (O : Operator d) (P : InstrumentCircuit d)
    (rho : Operator d) (decode : InstrumentLossDecode Y) : ℝ :=
  instrumentCircuitEventMass O P rho (instrumentLossTagLossEvent decode)

noncomputable def instrumentLossTagLossQueryCost {d : ℕ} {Y : Type} (O : Operator d)
    (P : InstrumentCircuit d) (rho : Operator d) (decode : InstrumentLossDecode Y) : ℝ :=
  ((instrumentCircuitMixedTraces O P rho).map fun t =>
    if instrumentLossTagLossEvent decode t.accepted t.outcomes then mixedMass t * t.queries else 0).sum

noncomputable def genAdversaryValue {X E : Type} [Fintype X] [DecidableEq X]
    [Fintype E] [DecidableEq E] {n : ℕ} {A : Type} [Fintype A] [DecidableEq A]
    (input : X → Fin n → A) (f : X → E) : ℝ≥0∞ :=
  ⨆ Γ : {Γ : Matrix X X ℂ // Γ.IsHermitian ∧
      (∀ x y, f x = f y → Γ x y = 0) ∧
      ∀ j, ‖genFilterDelta input j ⊙ Γ‖ ≤ 1}, ENNReal.ofReal ‖Γ.1‖

def cutWitness {X : Type} [DecidableEq X] (x y : X) : Matrix X X ℂ :=
  Matrix.single x y 1 + Matrix.single y x 1

def separatingCoords {X : Type} [Fintype X] [DecidableEq X] {κ : Type} [Fintype κ]
    [DecidableEq κ] {A : Type} [DecidableEq A] (input : X → κ → A) (x y : X) : Finset κ :=
  Finset.univ.filter (fun j => input x j ≠ input y j)

noncomputable def certifiedCutCost {X : Type} [Fintype X] [DecidableEq X] {κ : Type}
    [Fintype κ] [DecidableEq κ] {A : Type} [DecidableEq A] (input : X → κ → A)
    (β : κ → ℝ≥0∞) (x y : X) : ℝ :=
  if h : (separatingCoords input x y).Nonempty then
    (separatingCoords input x y).inf' h (fun j => (β j).toReal)
  else 0

def crossOutputPairs {X : Type} [Fintype X] [DecidableEq X] {E : Type} [DecidableEq E]
    (g : X → E) : Finset (X × X) :=
  Finset.univ.filter (fun p => g p.1 ≠ g p.2)

noncomputable def effectiveCertifiedValue {X : Type} [Fintype X] [DecidableEq X] {κ : Type}
    [Fintype κ] [DecidableEq κ] {A : Type} [DecidableEq A] {E : Type} [DecidableEq E]
    (input : X → κ → A) (g : X → E) (β : κ → ℝ≥0∞) : ℝ :=
  if h : (crossOutputPairs g).Nonempty then
    (crossOutputPairs g).sup' h (fun p => certifiedCutCost input β p.1 p.2)
  else 0

end Qatlib.Concepts.AdversaryBounds.AdvDuality
