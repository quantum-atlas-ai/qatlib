/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.StoppingCore.InterruptBridge.StoppingDefs
import Qatlib.Concepts.StoppingCore.InterruptBridge.StoppingExt
import Qatlib.Concepts.StoppingCore.InterruptBridge.QuerySpaceExtensions

/-!
# Data for stopping and charged instrument transport

`StopPolicy` pairs probabilistic transitions with state costs, and `FirstStopTransport` stores a
stopping mass, finite-fuel charged masses, and a nontermination mass. `policyFirstStop` fills
these fields from the corresponding stopping constructions.

`chargedEventMap` and `chargedEventMass` weight instrument outcomes by prices, while
`ChargedSampler` records an output law, outcome prices, and a bit count. The instrument
constructions use the operational probability framework of [DaviesLewis1970].

## Main statements

* `policyFirstStop`: packages stopping masses for a policy and initial configuration.
* `chargedEventMap`: sums price-weighted instrument branches over an event.
* `fairBitSampler`: records a decoded fair-bit law with zero prices and its bit count.

## References

* [Davies and Lewis, 1970][DaviesLewis1970]
-/

set_option backward.isDefEq.respectTransparency false
open Qatlib.Concepts.ZeroCostLimit.FirstHitMass
open Qatlib.Concepts.AEMeanReadout.LocalAEBackend.CostedLaw
open Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw

set_option autoImplicit false

open Qatlib.Concepts.AdaptiveCP.BranchTrace
open Qatlib.Concepts.StoppingCore.BranchCostCore
open Qatlib.Foundations.PureStateMath

open Qatlib.Concepts.StoppingCore.InterruptBridge

namespace Qatlib.Concepts.AdversaryBounds.AdvDuality

open Qatlib.Concepts.AEMeanReadout.LocalAEBackend.RandomizedExecution
open Qatlib.Concepts.ZeroCostLimit.FirstHitMass
open scoped ENNReal BigOperators Classical Matrix

/-- A stopping policy consisting of a probabilistic transition to either an output or a new
state, together with a natural-number cost for each state. -/
structure StopPolicy (S O : Type) where

  next : S → PMF (O ⊕ S)

  cost : S → ℕ

variable {S O : Type} [Fintype S] [DecidableEq S] [Fintype O] [DecidableEq O]

/-- The Boolean non-Zeno check applied to the policy's state-cost function. -/
def StopPolicy.zenoCheck (P : StopPolicy S O) : Bool := nonZenoCheck P.cost

/-- The condition that every state of the policy has positive charge. -/
def StopPolicy.zenoFree (P : StopPolicy S O) : Prop := positiveCharge P.cost

/-- A record containing a macro stopping mass, a fuel-indexed family of charged masses, and a
nontermination mass. -/
structure FirstStopTransport (P : StopPolicy S O) (cfg : O ⊕ S) (o : O) (k : ℕ) where

  macroMass : ℝ≥0∞

  chargedMass : ℕ → ℝ≥0∞

  neverMass : ℝ≥0∞

/-- Package the policy's first-stop mass at outcome `o` and charge `k`, its finite-fuel charged
masses, and its nontermination mass. -/
noncomputable def policyFirstStop (P : StopPolicy S O) (cfg : O ⊕ S) (o : O) (k : ℕ) :
    FirstStopTransport P cfg o k where
  macroMass := haltMass P.next P.cost cfg o k
  chargedMass := fun fuel => weightedRunFor P.next P.cost fuel cfg (Sum.inl o, k)
  neverMass := nonterminationMass P.next cfg

/-- The complex-linear map obtained by summing instrument branches over the event, weighted by
their natural-number prices. -/
noncomputable def chargedEventMap {X : Type} [Fintype X] [DecidableEq X]
    {D E : ℕ} (I : Instrument X D E) (price : X → ℕ) (Ev : X → Prop) [DecidablePred Ev] :
    Operator D →ₗ[ℂ] Operator E :=
  ∑ x ∈ Finset.univ.filter Ev, (price x : ℂ) • (I.branch x)

/-- The sum of instrument outcome probabilities over the event, weighted by their natural-number
prices. -/
noncomputable def chargedEventMass {X : Type} [Fintype X] [DecidableEq X]
    {D E : ℕ} (I : Instrument X D E) (price : X → ℕ) (ρ : Operator D)
    (Ev : X → Prop) [DecidablePred Ev] : ℝ :=
  ∑ x ∈ Finset.univ.filter Ev, (price x : ℝ) * instrumentProb I ρ x

/-- A sampler record containing an output-dependent natural-number price, a probability mass
function, and a bit count. -/
structure ChargedSampler (X : Type) where

  price : X → ℕ

  law : PMF X

  bits : ℕ

variable {X : Type}

/-- The joint distribution obtained by pairing each sampled outcome with its price. -/
noncomputable def ChargedSampler.chargedLaw (C : ChargedSampler X) : PMF (X × ℕ) :=
  C.law.map (fun x => (x, C.price x))

/-- The charged-sampler record for a decoded fair-bit distribution, with zero outcome prices and
bit count `Fintype.card R`. -/
noncomputable def fairBitSampler {X R : Type} [Fintype X] [Fintype R]
    (decode : (R → Bool) → X) : ChargedSampler X where
  price := fun _ => 0
  law := bitDecodeSampler decode
  bits := Fintype.card R

end Qatlib.Concepts.AdversaryBounds.AdvDuality
