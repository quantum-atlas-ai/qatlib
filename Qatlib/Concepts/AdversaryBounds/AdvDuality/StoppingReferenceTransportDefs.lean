/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.StoppingCore.InterruptBridge.StoppingDefs
import Qatlib.Concepts.StoppingCore.InterruptBridge.StoppingExt
import Qatlib.Concepts.StoppingCore.InterruptBridge.QuerySpaceExtensions
set_option warningAsError false
set_option backward.isDefEq.respectTransparency false
open Qatlib.Concepts.ZeroCostLimit.FirstHitMass
open Qatlib.Concepts.AEMeanReadout.LocalAEBackend.CostedLaw
open Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw

set_option autoImplicit false
set_option linter.unusedVariables false

open Qatlib.Concepts.AdaptiveCP.BranchTrace
open Qatlib.Concepts.StoppingCore.BranchCostCore
open Qatlib.Foundations.PureStateMath

open Qatlib.Concepts.StoppingCore.InterruptBridge

namespace Qatlib.Concepts.AdversaryBounds.AdvDuality

open Qatlib.Concepts.AEMeanReadout.LocalAEBackend.RandomizedExecution
open Qatlib.Concepts.ZeroCostLimit.FirstHitMass
open scoped ENNReal BigOperators Classical Matrix

structure StopPolicy (S O : Type) where

  next : S → PMF (O ⊕ S)

  cost : S → ℕ

variable {S O : Type} [Fintype S] [DecidableEq S] [Fintype O] [DecidableEq O]

def StopPolicy.zenoCheck (P : StopPolicy S O) : Bool := nonZenoCheck P.cost

def StopPolicy.zenoFree (P : StopPolicy S O) : Prop := positiveCharge P.cost

structure FirstStopTransport (P : StopPolicy S O) (cfg : O ⊕ S) (o : O) (k : ℕ) where

  macroMass : ℝ≥0∞

  chargedMass : ℕ → ℝ≥0∞

  neverMass : ℝ≥0∞

noncomputable def policyFirstStop (P : StopPolicy S O) (cfg : O ⊕ S) (o : O) (k : ℕ) :
    FirstStopTransport P cfg o k where
  macroMass := haltMass P.next P.cost cfg o k
  chargedMass := fun fuel => weightedRunFor P.next P.cost fuel cfg (Sum.inl o, k)
  neverMass := nonterminationMass P.next cfg

noncomputable def chargedEventMap {X : Type} [Fintype X] [DecidableEq X]
    {D E : ℕ} (I : Instrument X D E) (price : X → ℕ) (Ev : X → Prop) [DecidablePred Ev] :
    Operator D →ₗ[ℂ] Operator E :=
  ∑ x ∈ Finset.univ.filter Ev, (price x : ℂ) • (I.branch x)

noncomputable def chargedEventMass {X : Type} [Fintype X] [DecidableEq X]
    {D E : ℕ} (I : Instrument X D E) (price : X → ℕ) (ρ : Operator D)
    (Ev : X → Prop) [DecidablePred Ev] : ℝ :=
  ∑ x ∈ Finset.univ.filter Ev, (price x : ℝ) * instrumentProb I ρ x

structure ChargedSampler (X : Type) where

  price : X → ℕ

  law : PMF X

  bits : ℕ

variable {X : Type}

noncomputable def ChargedSampler.chargedLaw (C : ChargedSampler X) : PMF (X × ℕ) :=
  C.law.map (fun x => (x, C.price x))

noncomputable def fairBitSampler {X R : Type} [Fintype X] [Fintype R]
    (decode : (R → Bool) → X) : ChargedSampler X where
  price := fun _ => 0
  law := bitDecodeSampler decode
  bits := Fintype.card R

end Qatlib.Concepts.AdversaryBounds.AdvDuality
