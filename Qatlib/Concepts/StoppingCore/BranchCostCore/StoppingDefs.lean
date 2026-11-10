/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.AdaptiveCP.BranchTrace.StoppingJointDefs
import Qatlib.Concepts.StoppingCore.BranchCostCore.BranchCostExecution
import Qatlib.Concepts.AdversaryBounds.AdvDuality.RandomBitsNativeDefs
set_option backward.isDefEq.respectTransparency false
set_option warningAsError false
open Qatlib.Concepts.AdaptiveCP.BranchTrace
open Qatlib.Concepts.StoppingCore.BranchCostCore
open Qatlib.Concepts.AdversaryBounds.AdvDuality
open Qatlib.Concepts.AdversaryBounds.AdvDuality.FairFeedback
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.AEMeanReadout.LocalAEBackend
open Qatlib.Concepts.AdaptiveCP.BranchTrace

set_option autoImplicit false

namespace Qatlib.Concepts.StoppingCore.BranchCostCore

open Matrix
open scoped BigOperators Classical
open Qatlib RandomizedExecution

variable {S O : Type} [Fintype S] [DecidableEq S] [Nonempty S]
  [Fintype O] [DecidableEq O] {X : Type} [Fintype X] {D E : ℕ}

def PositiveReceiptCost (next : S → PMF ((O ⊕ S) × ℕ)) : Prop :=
  ∀ s cfg k, next s (cfg, k) ≠ 0 → 1 ≤ k

noncomputable def zeroCostLoop (s : S) : S → PMF ((O ⊕ S) × ℕ) :=
  fun _ => PMF.pure (.inr s, 0)

def NeverSemantics (P : JointProgram S O X D E) (cfg : O ⊕ S) : Prop :=
  jointNeverMass P cfg = nonterminationMass P.next cfg

def ConditionalOutputInterface : Prop :=
  ∀ (S O X : Type) [Fintype S] [DecidableEq S] [Nonempty S] [Fintype O]
    [DecidableEq O] [Fintype X] [DecidableEq X] (D E : ℕ),
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
        IsDensityOperator ρ → jointEventProb P ρ fuel cfg Ev = 0 →
        jointEventMap P fuel cfg Ev ρ = 0)

def EffectiveSamplerLedger : Prop :=
  ∀ (X : Type) [Fintype X] [DecidableEq X] (D E : ℕ) (k m : ℕ) (I : Instrument X D E),
    (fairBitProgram k m I).cost () = k ∧
    (∀ (fuel : ℕ) (cfg : Fin m ⊕ Unit) (o : Fin m) (c : ℕ),
      fuel * k < c → jointClassicalMass (fairBitProgram k m I) fuel cfg o c = 0)

end Qatlib.Concepts.StoppingCore.BranchCostCore
