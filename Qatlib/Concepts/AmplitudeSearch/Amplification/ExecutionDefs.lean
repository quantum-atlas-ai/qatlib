/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.RiskEstimation.PopulationGap.GibbsMetropolisDefs
import Qatlib.Concepts.AdaptiveCP.BranchTrace.Instrument
import Qatlib.Foundations.PureStateMath.MixedState
import Qatlib.Concepts.ShadowModels.ShadowChannel.QubitConjugationDesign
import Qatlib.Foundations.PureStateMath.Qubit
import Qatlib.Concepts.MixedInstrument.ClockBridge.MixedInstrumentClock
import Qatlib.Concepts.LinearLearning.ConcisePipeline.RandomizedCost
import Qatlib.Concepts.AEMeanReadout.LocalAEBackend.RandomizedExecution
import Qatlib.Foundations.QueryWordCore.Circuit
import Qatlib.Concepts.GateVocabulary.FiniteGateDescription
import Qatlib.Concepts.QueryComplexity.AdaptiveQuery.InterruptedCall

/-!
# Execution and resource specifications

The module defines costed continuous strategies, finite-instrument step specifications, partial
circuit calls, overlap-design samplers, numerical precision records, and finite-gate backend
records. Each associated predicate states the particular finiteness, legality, moment, or
resource condition required by that record.

`MetropolisRecovery` and `EnergyRejectionPipeline` also package proposal and phase-estimation
ledger parameters. Finite-dimensional states, instruments, and circuit descriptions are treated
in [NielsenChuang2010] and [Watrous2018].

## Main statements

* `ContinuousStrategy`: defines initialized costed strategies on real coordinate states.
* `IsOverlapDesign`: specifies finite pure-state overlap moments through order three.
* `FiniteBitBackend`: records a finite gate word and bit-resource parameters.

## References

* [Nielsen and Chuang, 2010][NielsenChuang2010]
* [Watrous, 2018][Watrous2018]
-/

set_option backward.isDefEq.respectTransparency false

open Qatlib.Concepts.AEMeanReadout.LocalAEBackend.RandomizedExecution
open Qatlib.Concepts.AdversaryBounds.AdvDuality
open Qatlib.Concepts.MixedInstrument.ClockBridge
open Qatlib.Concepts.QueryComplexity.AdaptiveQuery
open Qatlib.Foundations.BornMetrics.EventProbability
open Qatlib.Concepts.GateVocabulary.FiniteGateDescription

open Qatlib.Concepts.AdaptiveCP.BranchTrace
open Qatlib.Foundations.QueryWordCore.Circuit
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.LinearLearning.ConcisePipeline
open Qatlib.Concepts.AEMeanReadout.LocalAEBackend.CostedLaw
open Qatlib.Concepts.RiskEstimation.PopulationGap

set_option autoImplicit false

noncomputable section

namespace Qatlib.Concepts.AmplitudeSearch.Amplification

open Qatlib.Concepts.AEMeanReadout.LocalAEBackend.RandomizedExecution
open Qatlib.Concepts.RiskEstimation.PopulationGap
open Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw
open Qatlib
open Qatlib.Concepts.AmplitudeSearch.Amplification
open Qatlib
open scoped Classical ENNReal

/-- A strategy with a costed initialization and costed transitions on `m` real coordinates, with
outputs of type `O`. -/
structure ContinuousStrategy (m : ℕ) (O : Type*) where

  init : CostedLaw (Fin m → ℝ)

  step : (Fin m → ℝ) → CostedLaw (Configuration (Fin m → ℝ) O)

/-- Advance an active strategy state by one step, leaving a completed output unchanged at zero
added cost. -/
noncomputable def ContinuousStrategy.tick {m : ℕ} {O : Type*}
    (σ : ContinuousStrategy m O) :
    Configuration (Fin m → ℝ) O → CostedLaw (Configuration (Fin m → ℝ) O)
  | .inl out => Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.ret (.inl out)
  | .inr s => σ.step s

/-- Iterate the strategy transition for a specified number of ticks. -/
noncomputable def ContinuousStrategy.runFor {m : ℕ} {O : Type*}
    (σ : ContinuousStrategy m O) :
    ℕ → Configuration (Fin m → ℝ) O → CostedLaw (Configuration (Fin m → ℝ) O)
  | 0, cfg => Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.ret cfg
  | n + 1, cfg => CostedLaw.bind (σ.tick cfg) (σ.runFor n)

/-- The requirement that initialization and every individual strategy step have finite expected
cost. -/
def ContinuousStrategy.Correct {m : ℕ} {O : Type*}
    (σ : ContinuousStrategy m O) : Prop :=
  expectedCost σ.init < ⊤ ∧ ∀ s : Fin m → ℝ, expectedCost (σ.step s) < ⊤

/-- The existence of a uniform natural cost bound on initialization and steps, together with the
stated linear bound on finite runs. -/
def ContinuousStrategy.PolyBounded {m : ℕ} {O : Type*}
    (σ : ContinuousStrategy m O) : Prop :=
  ∃ C : ℕ,
    expectedCost σ.init ≤ (C : ℝ≥0∞) ∧
      (∀ s : Fin m → ℝ, expectedCost (σ.step s) ≤ (C : ℝ≥0∞)) ∧
      (∀ (n : ℕ) (cfg : Configuration (Fin m → ℝ) O),
        expectedCost (σ.runFor n cfg) ≤ (C : ℝ≥0∞) * (n + 1))

/-- The existence of a finite-label quantum instrument, density, decoder, and label costs
matching step probabilities and covering every supported step outcome. -/
def ContinuousStrategy.EffectiveQuantumMachine {m : ℕ} {O : Type*}
    (σ : ContinuousStrategy m O) (D : ℕ) : Prop :=
  ∃ (L : Type) (_ : Fintype L) (I : Instrument L D D) (ρ : ClockDensity D)
      (decode : L → (Fin m → ℝ) → Configuration (Fin m → ℝ) O) (cost : L → ℕ),
    ∀ s : Fin m → ℝ,
      (∀ l : L,
        ENNReal.ofReal (instrumentProb I (ρ : Operator D) l) =
          (σ.step s) (decode l s, cost l)) ∧
        (∀ x ∈ (σ.step s).support, ∃ l : L, decode l s = x.1 ∧ cost l = x.2)

/-- The condition that every supported outcome satisfying a predicate has zero cost. -/
def ZeroPriceOn {α : Type*} (p : CostedLaw α) (P : α → Prop) : Prop :=
  ∀ x ∈ p.support, P x.1 → x.2 = 0

/-- A sequence of states whose step laws all have nonempty support and whose total expected step
cost is finite. -/
def ZenoPath {m : ℕ} {O : Type*} (σ : ContinuousStrategy m O)
    (s : ℕ → Fin m → ℝ) : Prop :=
  (∀ n : ℕ, (σ.step (s n)).support.Nonempty) ∧
    (∑' n : ℕ, expectedCost (σ.step (s n))) < ⊤

/-- Parameters for Metropolis recovery: an energy function, inverse temperature, proposal
ensemble, and repetition count. -/
structure MetropolisRecovery (D : ℕ) where

  E : Fin D → ℝ

  β : ℝ

  ens : ProposalEnsemble D

  k : ℕ

/-- The Metropolis recovery conditions of positive dimension and legal, symmetric, positive
proposals. -/
def MetropolisRecovery.Correct {D : ℕ} (R : MetropolisRecovery D) : Prop :=
  0 < D ∧ proposalEnsembleLegal R.ens ∧ proposalSymmetric R.ens ∧
    proposalPositive R.ens

/-- The condition that the proposal ensemble generates a dense subgroup. -/
def MetropolisRecovery.Ergodic {D : ℕ} (R : MetropolisRecovery D) : Prop :=
  denseGenerated R.ens

/-- The step count, phase-estimation sizes, and workspace parameter for an energy-rejection cost
pipeline. -/
structure EnergyRejectionPipeline (D : ℕ) where

  steps : ℕ

  M : ℕ

  n : ℕ

  k : ℕ

/-- The Metropolis resource ledger associated with the pipeline and rejection parameter `nStar`. -/
def EnergyRejectionPipeline.ledger {D : ℕ} (p : EnergyRejectionPipeline D)
    (nStar : ℕ) : MetropolisCostLedger :=
  metropolisRunLedger p.steps D p.M p.k p.n nStar

/-- The assertion that the pipeline ledger has the specified total phase-estimation query and
gate counts and workspace-qubit count. -/
def EnergyRejectionPipeline.Complete {D : ℕ} (p : EnergyRejectionPipeline D)
    (nStar : ℕ) : Prop :=
  (p.ledger nStar).stepQueries =
      p.steps * ((2 + nStar) * qpeWindowQueries p.M p.n) ∧
    (p.ledger nStar).stepGates = p.steps * ((2 + nStar) * qpeWindowGates p.M p.n) ∧
    (p.ledger nStar).spaceQubits = D + 2 * Nat.clog 2 p.M + 1 + p.k

/-- A circuit prefix request with a prefix length and an available native bit-time budget. -/
structure PartialCall (I : Type*) [Fintype I] [DecidableEq I] where

  C : Circuit I

  r : ℕ

  nativeBitTime : ℕ

/-- The requirement that the requested prefix length fit both the circuit length and the native
bit-time budget. -/
def PartialCall.Correct {I : Type*} [Fintype I] [DecidableEq I]
    (p : PartialCall I) : Prop :=
  p.r ≤ p.C.length ∧ p.r ≤ p.nativeBitTime

/-- The state obtained by running the requested circuit prefix with the supplied oracle and
input state. -/
noncomputable def PartialCall.state {I : Type*} [Fintype I] [DecidableEq I]
    (p : PartialCall I) (oracle : Matrix I I ℂ) (ψ : QState I) : QState I :=
  Run oracle (queryPrefix p.C p.r) ψ

/-- The overlap moment `k! / ∏ j < k, (d + j)`. -/
noncomputable def haarOverlapMoment (d k : ℕ) : ℝ :=
  (Nat.factorial k : ℝ) / (∏ j ∈ Finset.range k, ((d + j : ℕ) : ℝ))

/-- The finite pure-state overlap-moment condition of order `k ≤ 3`, with a nonempty family and
moment equal to `haarOverlapMoment d k`. -/
def IsOverlapDesign {n : ℕ} (d k : ℕ) (f : Fin n → Operator d) : Prop :=
  k ≤ 3 ∧ 0 < n ∧
    ∀ (ρ σ : Operator d), IsPureDensityOperator ρ → IsPureDensityOperator σ →
      (∑ i : Fin n,
        ((Matrix.trace (σ * f i * ρ * Matrix.conjTranspose (f i))).re) ^ k) / (n : ℝ) =
          haarOverlapMoment d k

/-- A finite family of operators on `w` qubits with a sampling-cost parameter. -/
structure DesignSampler (w : ℕ) where

  size : ℕ

  members : Fin size → Operator (2 ^ w)

  sampleCost : ℕ

/-- The condition that all sampled operators are unitary and the family satisfies the
order-three overlap-moment identity. -/
def DesignSampler.Correct (w : ℕ) (s : DesignSampler w) : Prop :=
  (∀ i : Fin s.size, s.members i ∈ Matrix.unitaryGroup (Fin (2 ^ w)) ℂ) ∧
    IsOverlapDesign (2 ^ w) 3 (fun i : Fin s.size =>
      (s.members i : Matrix (Fin (2 ^ w)) (Fin (2 ^ w)) ℂ))

/-- The existence of a polynomial bound in `w + 1` for the sampler's stated sampling cost. -/
def DesignSampler.PolyBounded (w : ℕ) (s : DesignSampler w) : Prop :=
  ∃ C e : ℕ, s.sampleCost ≤ C * (w + 1) ^ e

/-- The real and complex digit counts of a finite-precision input specification. -/
structure RealComplexInput where

  realDigits : ℕ

  complexDigits : ℕ

/-- The requirement that both real and complex digit counts be positive. -/
def RealComplexInput.Correct (x : RealComplexInput) : Prop :=
  0 < x.realDigits ∧ 0 < x.complexDigits

/-- Round a real input to a rational using the specified real dyadic precision. -/
noncomputable def RealComplexInput.roundReal (x : RealComplexInput) (t : ℝ) : ℚ :=
  dyadicRat x.realDigits t

/-- Confidence parameters consisting of a failure level, positive-scale candidate, and order. -/
structure ConfidenceLedger where

  δ : ℝ

  c : ℝ

  order : ℕ

/-- The conditions that the failure level lies strictly between zero and one and the scale
parameter is positive. -/
def ConfidenceLedger.Correct (L : ConfidenceLedger) : Prop :=
  0 < L.δ ∧ L.δ < 1 ∧ 0 < L.c

/-- A finite gate word on `w` wires with an error parameter and bit-time cost. -/
structure GateSynthesis (w : ℕ) where

  word : List FiniteGateCode

  ε : ℝ

  bitTime : ℕ

/-- The condition that the finite gate word is legal on `w` wires and its error parameter is
positive. -/
def GateSynthesis.Correct (w : ℕ) (g : GateSynthesis w) : Prop :=
  finiteWordLegal w g.word = true ∧ 0 < g.ε

/-- The existence of polynomial bounds in `w + 1` for the gate-word length and bit-time cost. -/
def GateSynthesis.PolyBounded (w : ℕ) (g : GateSynthesis w) : Prop :=
  ∃ C e : ℕ,
    g.word.length ≤ C * (w + 1) ^ e ∧ g.bitTime ≤ C * (w + 1) ^ e

/-- A finite gate word with bit-time and bit-space resource parameters. -/
structure FiniteBitBackend (w : ℕ) where

  word : List FiniteGateCode

  bitTime : ℕ

  bitSpace : ℕ

/-- The condition that the backend's finite gate word is legal on its wire count. -/
def FiniteBitBackend.Correct (w : ℕ) (b : FiniteBitBackend w) : Prop :=
  finiteWordLegal w b.word = true

/-- The proposition that every wire count possesses a backend with a legal finite gate word. -/
def instrumentPmfNotFiniteBitBackend : Prop :=
  ∀ w : ℕ, ∃ b : FiniteBitBackend w, FiniteBitBackend.Correct w b

end Qatlib.Concepts.AmplitudeSearch.Amplification
