/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.AdaptiveCP.BranchTrace.Instrument
import Qatlib.Foundations.PureStateMath.MixedState
import Qatlib.Concepts.AdaptiveCP.BranchTrace.QuantumChannel
import Qatlib.Concepts.AdversaryBounds.AdvDuality.StoppingReferenceTransport
import Qatlib.Concepts.FairRandomBits.FiniteCoinExecution
import Qatlib.Concepts.ZeroCostLimit.FirstHitMass.ZeroCostLimitDefs
set_option warningAsError false
set_option backward.isDefEq.respectTransparency false
open Qatlib.Concepts.AdaptiveCP.BranchTrace
open Qatlib.Concepts.StoppingCore.BranchCostCore
open Qatlib.Concepts.StoppingCore.InterruptBridge
open Qatlib.Concepts.ZeroCostLimit.FirstHitMass
open Qatlib.Concepts.AdversaryBounds.AdvDuality
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.FairRandomBits.FiniteCoinExecution
open Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw

set_option autoImplicit false
set_option linter.unusedSectionVars false
noncomputable section

namespace Qatlib.Concepts.AdaptiveCP.BranchTrace

open Qatlib
open scoped ENNReal
open scoped ComplexOrder

variable {S O X : Type} [Fintype S] [DecidableEq S] [Nonempty S] [Fintype O]
  [DecidableEq O] [Fintype X] [DecidableEq X]
variable {D E : ℕ}

structure JointProgram (S O X : Type) [Fintype X] (D E : ℕ) where

  next : S → PMF (O ⊕ S)

  cost : S → ℕ

  channel : S → QuantumChannel D D

  instrument : Instrument X D E

noncomputable def transitionProb (P : JointProgram S O X D E) (s : S) (d : O ⊕ S) : ℝ :=
  (P.next s d).toReal

noncomputable def maxCharge (P : JointProgram S O X D E) : ℕ :=
  Finset.univ.sup P.cost

noncomputable def jointChargeRange (P : JointProgram S O X D E) (fuel : ℕ) : Finset ℕ :=
  Finset.range (fuel * maxCharge P + 1)

noncomputable def jointStopMap (P : JointProgram S O X D E) :
    ℕ → (O ⊕ S) → O → X → ℕ → Operator D →ₗ[ℂ] Operator E :=
  fun fuel =>
    Nat.rec (motive := fun _ => (O ⊕ S) → O → X → ℕ → Operator D →ₗ[ℂ] Operator E)
      (fun cfg o x k => match cfg with
        | .inl o0 => if o0 = o ∧ k = 0 then P.instrument.branch x else 0
        | .inr _ => 0)
      (fun _ ih cfg o x k => match cfg with
        | .inl o0 => if o0 = o ∧ k = 0 then P.instrument.branch x else 0
        | .inr s => if P.cost s ≤ k then
            ∑ d : O ⊕ S, ((transitionProb P s d : ℝ) : ℂ) •
              (ih d o x (k - P.cost s)).comp (P.channel s).map
          else 0)
      fuel

@[simp] theorem jointStopMap_zero (P : JointProgram S O X D E) (cfg : O ⊕ S) (o : O)
    (x : X) (k : ℕ) :
    jointStopMap P 0 cfg o x k = match cfg with
      | .inl o0 => if o0 = o ∧ k = 0 then P.instrument.branch x else 0
      | .inr _ => 0 := rfl

@[simp] theorem jointStopMap_succ (P : JointProgram S O X D E) (fuel : ℕ) (cfg : O ⊕ S)
    (o : O) (x : X) (k : ℕ) :
    jointStopMap P (fuel + 1) cfg o x k = match cfg with
      | .inl o0 => if o0 = o ∧ k = 0 then P.instrument.branch x else 0
      | .inr s => if P.cost s ≤ k then
          ∑ d : O ⊕ S, ((transitionProb P s d : ℝ) : ℂ) •
            (jointStopMap P fuel d o x (k - P.cost s)).comp (P.channel s).map
        else 0 := rfl

noncomputable def jointProb (P : JointProgram S O X D E) :
    Operator D → ℕ → (O ⊕ S) → O → X → ℕ → ℝ :=
  fun ρ fuel =>
    (Nat.rec (motive := fun _ => Operator D → (O ⊕ S) → O → X → ℕ → ℝ)
      (fun ρ cfg o x k => match cfg with
        | .inl o0 => if o0 = o ∧ k = 0 then instrumentProb P.instrument ρ x else 0
        | .inr _ => 0)
      (fun _ ih ρ cfg o x k => match cfg with
        | .inl o0 => if o0 = o ∧ k = 0 then instrumentProb P.instrument ρ x else 0
        | .inr s => if P.cost s ≤ k then
            ∑ d : O ⊕ S, transitionProb P s d *
              ih ((P.channel s).map ρ) d o x (k - P.cost s)
          else 0)
      fuel) ρ

@[simp] theorem jointProb_zero (P : JointProgram S O X D E) (ρ : Operator D) (cfg : O ⊕ S)
    (o : O) (x : X) (k : ℕ) :
    jointProb P ρ 0 cfg o x k = match cfg with
      | .inl o0 => if o0 = o ∧ k = 0 then instrumentProb P.instrument ρ x else 0
      | .inr _ => 0 := rfl

@[simp] theorem jointProb_succ (P : JointProgram S O X D E) (ρ : Operator D) (fuel : ℕ)
    (cfg : O ⊕ S) (o : O) (x : X) (k : ℕ) :
    jointProb P ρ (fuel + 1) cfg o x k = match cfg with
      | .inl o0 => if o0 = o ∧ k = 0 then instrumentProb P.instrument ρ x else 0
      | .inr s => if P.cost s ≤ k then
          ∑ d : O ⊕ S, transitionProb P s d *
            jointProb P ((P.channel s).map ρ) fuel d o x (k - P.cost s)
        else 0 := rfl

noncomputable def jointClassicalMass (P : JointProgram S O X D E) :
    ℕ → (O ⊕ S) → O → ℕ → ℝ≥0∞ :=
  fun fuel =>
    Nat.rec (motive := fun _ => (O ⊕ S) → O → ℕ → ℝ≥0∞)
      (fun cfg o k => match cfg with
        | .inl o0 => if o0 = o ∧ k = 0 then 1 else 0
        | .inr _ => 0)
      (fun _ ih cfg o k => match cfg with
        | .inl o0 => if o0 = o ∧ k = 0 then 1 else 0
        | .inr s => if P.cost s ≤ k then
            ∑ d : O ⊕ S, P.next s d * ih d o (k - P.cost s)
          else 0)
      fuel

@[simp] theorem jointClassicalMass_zero (P : JointProgram S O X D E) (cfg : O ⊕ S)
    (o : O) (k : ℕ) :
    jointClassicalMass P 0 cfg o k = match cfg with
      | .inl o0 => if o0 = o ∧ k = 0 then 1 else 0
      | .inr _ => 0 := rfl

@[simp] theorem jointClassicalMass_succ (P : JointProgram S O X D E) (fuel : ℕ)
    (cfg : O ⊕ S) (o : O) (k : ℕ) :
    jointClassicalMass P (fuel + 1) cfg o k = match cfg with
      | .inl o0 => if o0 = o ∧ k = 0 then 1 else 0
      | .inr s => if P.cost s ≤ k then
          ∑ d : O ⊕ S, P.next s d * jointClassicalMass P fuel d o (k - P.cost s)
        else 0 := rfl

noncomputable def jointPendingMass (P : JointProgram S O X D E) (fuel : ℕ)
    (cfg : O ⊕ S) : ℝ≥0∞ :=
  pendingMass P.next cfg fuel

noncomputable def jointNeverMass (P : JointProgram S O X D E) (cfg : O ⊕ S) : ℝ≥0∞ :=
  ⨅ fuel : ℕ, jointPendingMass P fuel cfg

noncomputable def fairBitProgram (k m : ℕ) {X : Type} [Fintype X] (I : Instrument X D E) :
    JointProgram Unit (Fin m) X D E where
  next := fun _ => finiteCoinNext k m ()
  cost := fun _ => k
  channel := fun _ => QuantumChannel.id D
  instrument := I

noncomputable def jointEventMap (P : JointProgram S O X D E) (fuel : ℕ) (cfg : O ⊕ S)
    (Ev : O × X × ℕ → Prop) [DecidablePred Ev] :
    Operator D →ₗ[ℂ] Operator E :=
  ∑ o : O, ∑ x : X, ∑ k ∈ jointChargeRange P fuel,
    if Ev (o, x, k) then jointStopMap P fuel cfg o x k else 0

noncomputable def jointEventProb (P : JointProgram S O X D E) (ρ : Operator D)
    (fuel : ℕ) (cfg : O ⊕ S) (Ev : O × X × ℕ → Prop) [DecidablePred Ev] : ℝ :=
  ∑ o : O, ∑ x : X, ∑ k ∈ jointChargeRange P fuel,
    if Ev (o, x, k) then jointProb P ρ fuel cfg o x k else 0

noncomputable def jointNormalizedPost (P : JointProgram S O X D E) (ρ : Operator D)
    (fuel : ℕ) (cfg : O ⊕ S) (Ev : O × X × ℕ → Prop) [DecidablePred Ev] : Operator E :=
  if 0 < jointEventProb P ρ fuel cfg Ev then
    (((jointEventProb P ρ fuel cfg Ev : ℝ) : ℂ)⁻¹) • (jointEventMap P fuel cfg Ev ρ)
  else
    0

noncomputable def jointTotalMap (P : JointProgram S O X D E) (fuel : ℕ) (cfg : O ⊕ S) :
    Operator D →ₗ[ℂ] Operator E :=
  ∑ o : O, ∑ x : X, ∑ k ∈ jointChargeRange P fuel, jointStopMap P fuel cfg o x k

noncomputable def jointTotalProb (P : JointProgram S O X D E) (ρ : Operator D)
    (fuel : ℕ) (cfg : O ⊕ S) : ℝ :=
  ∑ o : O, ∑ x : X, ∑ k ∈ jointChargeRange P fuel, jointProb P ρ fuel cfg o x k

noncomputable def jointLabelPost (P : JointProgram S O X D E) (ρ : Operator D)
    (fuel : ℕ) (cfg : O ⊕ S) (o : O) (x : X) (k : ℕ) : Operator E :=
  if 0 < jointProb P ρ fuel cfg o x k then
    (((jointProb P ρ fuel cfg o x k : ℝ) : ℂ)⁻¹) • (jointStopMap P fuel cfg o x k ρ)
  else
    0

noncomputable def jointReferenceEventMap (P : JointProgram S O X D E) (fuel : ℕ)
    (cfg : O ⊕ S) (Ev : O × X × ℕ → Prop) [DecidablePred Ev] {R : ℕ} :
    Matrix (Fin D × Fin R) (Fin D × Fin R) ℂ →
      Matrix (Fin E × Fin R) (Fin E × Fin R) ℂ :=
  tensorLeft (jointEventMap P fuel cfg Ev)

noncomputable def jointReferenceTotalMap (P : JointProgram S O X D E) (fuel : ℕ)
    (cfg : O ⊕ S) {R : ℕ} :
    Matrix (Fin D × Fin R) (Fin D × Fin R) ℂ →
      Matrix (Fin E × Fin R) (Fin E × Fin R) ℂ :=
  tensorLeft (jointTotalMap P fuel cfg)

noncomputable def jointMemoryMarginal (D R : ℕ)
    (A : Matrix (Fin D × Fin R) (Fin D × Fin R) ℂ) : Operator D :=
  PartialTrace A

noncomputable def jointReferenceMarginal (D R : ℕ)
    (A : Matrix (Fin D × Fin R) (Fin D × Fin R) ℂ) : Operator R :=
  partialTraceFirst A

def Clause14JointFirstStop : Prop :=
  ∀ (S O X : Type) [Fintype S] [DecidableEq S] [Nonempty S] [Fintype O] [DecidableEq O]
    [Fintype X] [DecidableEq X] (D E : ℕ),
    (∀ (P : JointProgram S O X D E) (fuel : ℕ) (cfg : O ⊕ S) (o : O) (x : X) (k : ℕ),
        CompletelyPositive (jointStopMap P fuel cfg o x k)) ∧
    (∀ (P : JointProgram S O X D E) (fuel : ℕ) (cfg : O ⊕ S) (o : O) (x : X) (k : ℕ)
        (ρ : Operator D), IsDensityOperator ρ →
        Matrix.trace (jointStopMap P fuel cfg o x k ρ) =
          ((jointProb P ρ fuel cfg o x k : ℝ) : ℂ)) ∧
    (∀ (P : JointProgram S O X D E) (fuel : ℕ) (cfg : O ⊕ S) (o : O) (k : ℕ),
        jointClassicalMass P fuel cfg o k =
          weightedRunFor P.next P.cost fuel cfg (.inl o, k)) ∧
    (∀ (P : JointProgram S O X D E) (fuel : ℕ) (cfg : O ⊕ S) (o : O) (k : ℕ)
        (ρ : Operator D), IsDensityOperator ρ →
        (∑ x : X, jointProb P ρ fuel cfg o x k) =
          (jointClassicalMass P fuel cfg o k).toReal) ∧
    (∀ (P : JointProgram S O X D E) (fuel : ℕ) (cfg : O ⊕ S),
        (∑' o : O, ∑' k : ℕ, jointClassicalMass P fuel cfg o k) +
          jointPendingMass P fuel cfg = 1) ∧
    (∀ (P : JointProgram S O X D E) (cfg : O ⊕ S),
        jointNeverMass P cfg = nonterminationMass P.next cfg) ∧
    (∀ (P : JointProgram S O X D E),
        Qatlib.Concepts.StoppingCore.InterruptBridge.nonZenoCheck P.cost = true
          ↔ Qatlib.Concepts.StoppingCore.InterruptBridge.positiveCharge P.cost) ∧
    (∀ (P : JointProgram S O X D E) (hc : ∀ s, 0 < P.cost s) (fuel : ℕ) (cfg : O ⊕ S)
        (o : O) (k : ℕ) (hk : k ≤ fuel),
        jointClassicalMass P fuel cfg o k = weightedHaltJoint P.next P.cost cfg o k) ∧
    (∀ (P : JointProgram S O X D E) (cfg : O ⊕ S) (o : O) (k : ℕ),
        0 < Qatlib.Concepts.ZeroCostLimit.FirstHitMass.haltMass P.next P.cost cfg o k →
          Filter.Tendsto (fun fuel => jointClassicalMass P fuel cfg o k) Filter.atTop
            (nhds (Qatlib.Concepts.ZeroCostLimit.FirstHitMass.haltMass P.next P.cost cfg o k))) ∧
    (∀ (P : JointProgram S O X D E) (ρ : Operator D) (fuel : ℕ) (cfg : O ⊕ S),
        IsDensityOperator ρ →
        jointTotalProb P ρ fuel cfg + (jointPendingMass P fuel cfg).toReal = 1)

def PaidWalkReferenceEvents : Prop :=
  ∀ (S O X : Type) [Fintype S] [DecidableEq S] [Nonempty S] [Fintype O] [DecidableEq O]
    [Fintype X] [DecidableEq X] (D E : ℕ),
    (∀ (P : JointProgram S O X D E) (fuel : ℕ) (cfg : O ⊕ S)
        (Ev : O × X × ℕ → Prop) [DecidablePred Ev],
        CompletelyPositive (jointEventMap P fuel cfg Ev)) ∧
    (∀ (P : JointProgram S O X D E) (fuel : ℕ) (cfg : O ⊕ S)
        (Ev : O × X × ℕ → Prop) [DecidablePred Ev] (ρ : Operator D),
        IsDensityOperator ρ →
        Matrix.trace (jointEventMap P fuel cfg Ev ρ) =
          ((jointEventProb P ρ fuel cfg Ev : ℝ) : ℂ)) ∧
    (∀ (P : JointProgram S O X D E) (fuel : ℕ) (cfg : O ⊕ S)
        (Ev : O × X × ℕ → Prop) [DecidablePred Ev] (ρ : Operator D),
        IsDensityOperator ρ → 0 < jointEventProb P ρ fuel cfg Ev →
        IsDensityOperator (jointNormalizedPost P ρ fuel cfg Ev)) ∧
    (∀ (P : JointProgram S O X D E) (fuel : ℕ) (cfg : O ⊕ S)
        (Ev : O × X × ℕ → Prop) [DecidablePred Ev] (ρ : Operator D),
        IsDensityOperator ρ → jointEventProb P ρ fuel cfg Ev = 0 →
        jointEventMap P fuel cfg Ev ρ = 0) ∧
    (∀ (P : JointProgram S O X D E) (fuel : ℕ) (cfg : O ⊕ S)
        (Ev : O × X × ℕ → Prop) [DecidablePred Ev] {R : ℕ}
        (ρ : Matrix (Fin D × Fin R) (Fin D × Fin R) ℂ),
        IsDensityOperator (jointMemoryMarginal D R ρ) →
        Matrix.trace (jointReferenceEventMap P fuel cfg Ev ρ)
          = ((jointEventProb P (jointMemoryMarginal D R ρ) fuel cfg Ev : ℝ) : ℂ)) ∧
    (∀ (P : JointProgram S O X D E) (fuel : ℕ) (cfg : O ⊕ S) (o : O) (x : X) (k : ℕ)
        (R : ℕ) (ρ : Matrix (Fin D × Fin R) (Fin D × Fin R) ℂ),
        Matrix.trace (tensorLeft (jointStopMap P fuel cfg o x k) ρ)
          = Matrix.trace (jointStopMap P fuel cfg o x k (jointMemoryMarginal D R ρ))) ∧
    (∀ (P : JointProgram S O X D E) (fuel : ℕ) (cfg : O ⊕ S) (o : O) (x : X) (k : ℕ)
        (R : ℕ) (ρ : Matrix (Fin D × Fin R) (Fin D × Fin R) ℂ),
        IsDensityOperator (jointMemoryMarginal D R ρ) →
        Matrix.trace (tensorLeft (jointStopMap P fuel cfg o x k) ρ)
          = ((jointProb P (jointMemoryMarginal D R ρ) fuel cfg o x k : ℝ) : ℂ)) ∧
    (∀ (P : JointProgram S O X D E) (fuel : ℕ) (cfg : O ⊕ S) (o : O) (x : X) (k : ℕ)
        (ρ : Operator D), IsDensityOperator ρ → 0 < jointProb P ρ fuel cfg o x k →
        IsDensityOperator (jointLabelPost P ρ fuel cfg o x k)) ∧
    (∀ (P : JointProgram S O X D E) (fuel : ℕ) (cfg : O ⊕ S) (o : O) (x : X) (k : ℕ)
        (ρ : Operator D), IsDensityOperator ρ → jointProb P ρ fuel cfg o x k = 0 →
        jointStopMap P fuel cfg o x k ρ = 0)

set_option linter.unusedVariables false in

def Clause16EffectiveSampling : Prop :=
  ∀ (X : Type) [Fintype X] [DecidableEq X] (D E : ℕ),
    (∀ (k m : ℕ) (I : Instrument X D E),
        (fairBitProgram k m I).next () = finiteCoinNext k m () ∧
          (fairBitProgram k m I).cost () = k) ∧
    (∀ (k m : ℕ) (hm : m ≤ 2 ^ k) (fuel : ℕ) (I : Instrument X D E),
        jointPendingMass (fairBitProgram k m I) fuel (.inr ()) = coinRejectMass k m ^ fuel) ∧
    (∀ (k m : ℕ) (I : Instrument X D E) (fuel : ℕ) (cfg : Fin m ⊕ Unit) (o : Fin m) (c : ℕ),
        fuel * k < c → jointClassicalMass (fairBitProgram k m I) fuel cfg o c = 0) ∧
    (∀ (k m : ℕ) (I : Instrument X D E) (ρ : Operator D) (fuel : ℕ),
        IsDensityOperator ρ →
        1 - jointTotalProb (fairBitProgram k m I) ρ fuel (.inr ())
          = (jointPendingMass (fairBitProgram k m I) fuel (.inr ())).toReal)

end Qatlib.Concepts.AdaptiveCP.BranchTrace
