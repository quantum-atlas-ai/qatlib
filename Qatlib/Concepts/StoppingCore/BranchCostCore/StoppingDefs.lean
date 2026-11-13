/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.AdaptiveCP.BranchTrace.StoppingJointDefs
import Qatlib.Concepts.StoppingCore.BranchCostCore.BranchCostExecution
import Qatlib.Concepts.AdversaryBounds.AdvDuality.RandomBitsNativeDefs

/-!
# Stopping and conditional-output interface specifications

`PositiveReceiptCost` expresses the supported-cost condition for branch-clock compilation, while
`zeroCostLoop` supplies a zero-cost continuing transition. `NeverSemantics` identifies two
nontermination mass constructions.

`ConditionalOutputInterface` specifies complete positivity, trace probabilities, and vanishing
zero-probability outputs for event maps. `EffectiveSamplerLedger` specifies the per-step charge
and finite-fuel cost support of fair-bit instrument programs. For background, see
[DaviesLewis1970].

## Main statements

* `PositiveReceiptCost`: requires every supported branch receipt to cost at least one.
* `ConditionalOutputInterface`: packages the quantum event-map properties.
* `EffectiveSamplerLedger`: states the fair-bit program charge and cost-support bounds.

## References

* [Davies and Lewis, 1970][DaviesLewis1970]
-/

set_option backward.isDefEq.respectTransparency false
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

/-- Every successor-and-cost receipt with nonzero transition mass has natural cost at least one. -/
def PositiveReceiptCost (next : S → PMF ((O ⊕ S) × ℕ)) : Prop :=
  ∀ s cfg k, next s (cfg, k) ≠ 0 → 1 ≤ k

/-- The deterministic transition that always continues at the chosen state `s` with zero cost. -/
noncomputable def zeroCostLoop (s : S) : S → PMF ((O ⊕ S) × ℕ) :=
  fun _ => PMF.pure (.inr s, 0)

/-- The joint-program nontermination mass equals the nontermination mass of its underlying
classical transition from the same initial configuration. -/
def NeverSemantics (P : JointProgram S O X D E) (cfg : O ⊕ S) : Prop :=
  jointNeverMass P cfg = nonterminationMass P.next cfg

/-- The proposition that all finite joint-program event maps are completely positive, have trace
equal to event probability on density operators, and return zero when that probability is
zero. -/
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

/-- The proposition that a fair-bit instrument program has per-step cost `k` and zero classical
joint mass at every cost exceeding `fuel * k`. -/
def EffectiveSamplerLedger : Prop :=
  ∀ (X : Type) [Fintype X] [DecidableEq X] (D E : ℕ) (k m : ℕ) (I : Instrument X D E),
    (fairBitProgram k m I).cost () = k ∧
    (∀ (fuel : ℕ) (cfg : Fin m ⊕ Unit) (o : Fin m) (c : ℕ),
      fuel * k < c → jointClassicalMass (fairBitProgram k m I) fuel cfg o c = 0)

end Qatlib.Concepts.StoppingCore.BranchCostCore
