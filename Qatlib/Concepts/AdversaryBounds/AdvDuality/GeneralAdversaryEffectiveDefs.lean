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

/-!
# Loss tags and effective adversary certificates

Defines explicit loss outcomes and decoder events for observed and instrument circuits.
`lossTagSuccessMass`, `lossTagLossMass`, and their instrument counterparts keep answer and loss
contributions distinct while retaining all branch mass.

The module defines `genAdversaryValue` using normalized Hermitian witnesses, following the
filtered-norm viewpoint of [LeeEtAl2011], and introduces finite cut certificates through
`certifiedCutCost` and `effectiveCertifiedValue`.

## Main statements

* `LossTagged`: extend an output type with a distinguished loss outcome.
* `instrumentLossTagLossQueryCost`: query cost contributed by instrument traces decoded as loss.
* `genAdversaryValue`: supremum of norms of feasible Hermitian witnesses.
* `effectiveCertifiedValue`: maximum certified cut cost over pairs with different outputs.

## References

* [Lee et al., 2011][LeeEtAl2011]
-/

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

/-- The singleton type marking a lost output. -/
inductive LossTag : Type where
  | lost : LossTag
deriving Fintype, DecidableEq

/-- An output type extended by a distinguished loss tag using a disjoint sum. -/
abbrev LossTagged (O : Type) := O ⊕ LossTag

/-- The distinguished loss outcome in `LossTagged O`. -/
def lossOutcome {O : Type} : LossTagged O := .inr .lost

/-- The predicate asserting that an extended output lies in the loss summand. -/
def IsLoss {O : Type} : LossTagged O → Prop
  | .inl _ => False
  | .inr _ => True

/-- An ordinary output is not a loss outcome. -/
@[simp] theorem isLoss_inl (O : Type) (o : O) : ¬ IsLoss (O := O) (.inl o) := by
  simp [IsLoss]

/-- Every element of the loss summand satisfies `IsLoss`. -/
@[simp] theorem isLoss_inr (O : Type) (t : LossTag) : IsLoss (O := O) (.inr t) := by
  simp [IsLoss]

/-- A decoder assigning an ordinary output or loss to an acceptance flag and an outcome record. -/
abbrev LossDecode (Y : Type) := Bool → List (ℕ × ℕ) → LossTagged Y

/-- The Boolean event that an observed trace decodes to the specified ordinary answer. -/
def lossTagAnswerEvent {I Y : Type} [DecidableEq Y] (decode : LossDecode Y) (y : Y) :
    BranchTrace I → Bool :=
  fun t => match decode t.accepted t.outcomes with
    | .inl o => decide (o = y)
    | .inr _ => false

/-- The Boolean event that an observed trace decodes to some ordinary answer. -/
def lossTagAnyAnswerEvent {I Y : Type} (decode : LossDecode Y) : BranchTrace I → Bool :=
  fun t => match decode t.accepted t.outcomes with
    | .inl _ => true
    | .inr _ => false

/-- The Boolean event that an observed trace decodes to loss. -/
def lossTagLossEvent {I Y : Type} (decode : LossDecode Y) : BranchTrace I → Bool :=
  fun t => match decode t.accepted t.outcomes with
    | .inl _ => false
    | .inr _ => true

/-- For an observed trace, decoding to loss is the Boolean complement of decoding to any
ordinary answer. -/
theorem lossTagLossEvent_eq_not_any {I Y : Type} (decode : LossDecode Y) (t : BranchTrace I) :
    lossTagLossEvent decode t = ! lossTagAnyAnswerEvent decode t := by
  cases h : decode t.accepted t.outcomes <;>
    simp [lossTagLossEvent, lossTagAnyAnswerEvent, h]

/-- An observed trace decoded as the specified answer is also decoded as some answer. -/
theorem lossTagAnswerEvent_le_any {I Y : Type} [DecidableEq Y] (decode : LossDecode Y) (y : Y)
    (t : BranchTrace I) (h : lossTagAnswerEvent decode y t = true) :
    lossTagAnyAnswerEvent decode t = true := by
  cases hdec : decode t.accepted t.outcomes with
  | inl o =>
    simp [lossTagAnyAnswerEvent, hdec]
  | inr t' =>
    simp [lossTagAnswerEvent, hdec] at h

/-- The mass of observed traces decoded as the specified answer. -/
noncomputable def lossTagSuccessMass {I Y : Type} [Fintype I] [DecidableEq I] [DecidableEq Y]
    (O : Matrix I I ℂ) (program : ObservedCircuit I) (ψ : QState I) (decode : LossDecode Y)
    (y : Y) : ℝ :=
  observedEventMass O program ψ (lossTagAnswerEvent decode y)

/-- The mass of observed traces decoded as any ordinary answer. -/
noncomputable def lossTagAnyAnswerMass {I Y : Type} [Fintype I] [DecidableEq I]
    (O : Matrix I I ℂ) (program : ObservedCircuit I) (ψ : QState I) (decode : LossDecode Y) : ℝ :=
  observedEventMass O program ψ (lossTagAnyAnswerEvent decode)

/-- The mass of observed traces decoded as loss. -/
noncomputable def lossTagLossMass {I Y : Type} [Fintype I] [DecidableEq I]
    (O : Matrix I I ℂ) (program : ObservedCircuit I) (ψ : QState I) (decode : LossDecode Y) : ℝ :=
  observedEventMass O program ψ (lossTagLossEvent decode)

/-- A decoder from an instrument acceptance flag and outcome record to an ordinary answer or
loss. -/
abbrev InstrumentLossDecode (Y : Type) := Bool → List (ℕ × ℕ) → LossTagged Y

/-- The Boolean event that an instrument record decodes to the specified ordinary answer. -/
def instrumentLossTagAnswerEvent {Y : Type} [DecidableEq Y] (decode : InstrumentLossDecode Y)
    (y : Y) : Bool → List (ℕ × ℕ) → Bool :=
  fun accepted outcomes => match decode accepted outcomes with
    | .inl o => decide (o = y)
    | .inr _ => false

/-- The Boolean event that an instrument record decodes to any ordinary answer. -/
def instrumentLossTagAnyAnswerEvent {Y : Type} (decode : InstrumentLossDecode Y) :
    Bool → List (ℕ × ℕ) → Bool :=
  fun accepted outcomes => match decode accepted outcomes with
    | .inl _ => true
    | .inr _ => false

/-- The Boolean event that an instrument record decodes to loss. -/
def instrumentLossTagLossEvent {Y : Type} (decode : InstrumentLossDecode Y) :
    Bool → List (ℕ × ℕ) → Bool :=
  fun accepted outcomes => match decode accepted outcomes with
    | .inl _ => false
    | .inr _ => true

/-- The event mass of all mixed traces of an instrument circuit. -/
noncomputable def instrumentTotalMass {d : ℕ} (O : Operator d) (P : InstrumentCircuit d)
    (rho : Operator d) : ℝ :=
  instrumentCircuitEventMass O P rho (fun _ _ => true)

/-- The event mass of instrument traces decoded as the specified answer. -/
noncomputable def instrumentLossTagSuccessMass {d : ℕ} {Y : Type} (O : Operator d) (P : InstrumentCircuit d)
    (rho : Operator d) (decode : InstrumentLossDecode Y) (y : Y) : ℝ :=
  instrumentCircuitEventMass O P rho (instrumentLossTagAnswerEvent decode y)

/-- The event mass of instrument traces decoded as any ordinary answer. -/
noncomputable def instrumentLossTagAnyAnswerMass {d : ℕ} {Y : Type} (O : Operator d) (P : InstrumentCircuit d)
    (rho : Operator d) (decode : InstrumentLossDecode Y) : ℝ :=
  instrumentCircuitEventMass O P rho (instrumentLossTagAnyAnswerEvent decode)

/-- The event mass of instrument traces decoded as loss. -/
noncomputable def instrumentLossTagLossMass {d : ℕ} {Y : Type} (O : Operator d) (P : InstrumentCircuit d)
    (rho : Operator d) (decode : InstrumentLossDecode Y) : ℝ :=
  instrumentCircuitEventMass O P rho (instrumentLossTagLossEvent decode)

/-- The sum of mixed branch mass times query count over instrument traces decoded as loss. -/
noncomputable def instrumentLossTagLossQueryCost {d : ℕ} {Y : Type} (O : Operator d)
    (P : InstrumentCircuit d) (rho : Operator d) (decode : InstrumentLossDecode Y) : ℝ :=
  ((instrumentCircuitMixedTraces O P rho).map fun t =>
    if instrumentLossTagLossEvent decode t.accepted t.outcomes then mixedMass t * t.queries else 0).sum

/-- The extended nonnegative supremum of norms of Hermitian matrices vanishing on equal outputs
and having all input-difference filter norms at most one. -/
noncomputable def genAdversaryValue {X E : Type} [Fintype X] [DecidableEq X]
    [Fintype E] [DecidableEq E] {n : ℕ} {A : Type} [Fintype A] [DecidableEq A]
    (input : X → Fin n → A) (f : X → E) : ℝ≥0∞ :=
  ⨆ Γ : {Γ : Matrix X X ℂ // Γ.IsHermitian ∧
      (∀ x y, f x = f y → Γ x y = 0) ∧
      ∀ j, ‖genFilterDelta input j ⊙ Γ‖ ≤ 1}, ENNReal.ofReal ‖Γ.1‖

/-- The symmetric complex matrix with unit contributions at the two ordered pairs `(x, y)` and
`(y, x)`. -/
def cutWitness {X : Type} [DecidableEq X] (x y : X) : Matrix X X ℂ :=
  Matrix.single x y 1 + Matrix.single y x 1

/-- The finite set of coordinates at which two encoded inputs differ. -/
def separatingCoords {X : Type} [Fintype X] [DecidableEq X] {κ : Type} [Fintype κ]
    [DecidableEq κ] {A : Type} [DecidableEq A] (input : X → κ → A) (x y : X) : Finset κ :=
  Finset.univ.filter (fun j => input x j ≠ input y j)

/-- The minimum of `(β j).toReal` over separating coordinates, with value zero if no coordinate
separates the pair. -/
noncomputable def certifiedCutCost {X : Type} [Fintype X] [DecidableEq X] {κ : Type}
    [Fintype κ] [DecidableEq κ] {A : Type} [DecidableEq A] (input : X → κ → A)
    (β : κ → ℝ≥0∞) (x y : X) : ℝ :=
  if h : (separatingCoords input x y).Nonempty then
    (separatingCoords input x y).inf' h (fun j => (β j).toReal)
  else 0

/-- The finite set of ordered input pairs on which the output function takes different values. -/
def crossOutputPairs {X : Type} [Fintype X] [DecidableEq X] {E : Type} [DecidableEq E]
    (g : X → E) : Finset (X × X) :=
  Finset.univ.filter (fun p => g p.1 ≠ g p.2)

/-- The maximum certified cut cost over pairs with different outputs, with value zero if there
are no such pairs. -/
noncomputable def effectiveCertifiedValue {X : Type} [Fintype X] [DecidableEq X] {κ : Type}
    [Fintype κ] [DecidableEq κ] {A : Type} [DecidableEq A] {E : Type} [DecidableEq E]
    (input : X → κ → A) (g : X → E) (β : κ → ℝ≥0∞) : ℝ :=
  if h : (crossOutputPairs g).Nonempty then
    (crossOutputPairs g).sup' h (fun p => certifiedCutCost input β p.1 p.2)
  else 0

end Qatlib.Concepts.AdversaryBounds.AdvDuality
