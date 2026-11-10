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
set_option warningAsError false
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

structure ContinuousStrategy (m : ℕ) (O : Type*) where

  init : CostedLaw (Fin m → ℝ)

  step : (Fin m → ℝ) → CostedLaw (Configuration (Fin m → ℝ) O)

noncomputable def ContinuousStrategy.tick {m : ℕ} {O : Type*}
    (σ : ContinuousStrategy m O) :
    Configuration (Fin m → ℝ) O → CostedLaw (Configuration (Fin m → ℝ) O)
  | .inl out => Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.ret (.inl out)
  | .inr s => σ.step s

noncomputable def ContinuousStrategy.runFor {m : ℕ} {O : Type*}
    (σ : ContinuousStrategy m O) :
    ℕ → Configuration (Fin m → ℝ) O → CostedLaw (Configuration (Fin m → ℝ) O)
  | 0, cfg => Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.ret cfg
  | n + 1, cfg => CostedLaw.bind (σ.tick cfg) (σ.runFor n)

def ContinuousStrategy.Correct {m : ℕ} {O : Type*}
    (σ : ContinuousStrategy m O) : Prop :=
  expectedCost σ.init < ⊤ ∧ ∀ s : Fin m → ℝ, expectedCost (σ.step s) < ⊤

def ContinuousStrategy.PolyBounded {m : ℕ} {O : Type*}
    (σ : ContinuousStrategy m O) : Prop :=
  ∃ C : ℕ,
    expectedCost σ.init ≤ (C : ℝ≥0∞) ∧
      (∀ s : Fin m → ℝ, expectedCost (σ.step s) ≤ (C : ℝ≥0∞)) ∧
      (∀ (n : ℕ) (cfg : Configuration (Fin m → ℝ) O),
        expectedCost (σ.runFor n cfg) ≤ (C : ℝ≥0∞) * (n + 1))

def ContinuousStrategy.EffectiveQuantumMachine {m : ℕ} {O : Type*}
    (σ : ContinuousStrategy m O) (D : ℕ) : Prop :=
  ∃ (L : Type) (_ : Fintype L) (I : Instrument L D D) (ρ : ClockDensity D)
      (decode : L → (Fin m → ℝ) → Configuration (Fin m → ℝ) O) (cost : L → ℕ),
    ∀ s : Fin m → ℝ,
      (∀ l : L,
        ENNReal.ofReal (instrumentProb I (ρ : Operator D) l) =
          (σ.step s) (decode l s, cost l)) ∧
        (∀ x ∈ (σ.step s).support, ∃ l : L, decode l s = x.1 ∧ cost l = x.2)

def ZeroPriceOn {α : Type*} (p : CostedLaw α) (P : α → Prop) : Prop :=
  ∀ x ∈ p.support, P x.1 → x.2 = 0

def ZenoPath {m : ℕ} {O : Type*} (σ : ContinuousStrategy m O)
    (s : ℕ → Fin m → ℝ) : Prop :=
  (∀ n : ℕ, (σ.step (s n)).support.Nonempty) ∧
    (∑' n : ℕ, expectedCost (σ.step (s n))) < ⊤

structure MetropolisRecovery (D : ℕ) where

  E : Fin D → ℝ

  β : ℝ

  ens : ProposalEnsemble D

  k : ℕ

def MetropolisRecovery.Correct {D : ℕ} (R : MetropolisRecovery D) : Prop :=
  0 < D ∧ proposalEnsembleLegal R.ens ∧ proposalSymmetric R.ens ∧
    proposalPositive R.ens

def MetropolisRecovery.Ergodic {D : ℕ} (R : MetropolisRecovery D) : Prop :=
  denseGenerated R.ens

structure EnergyRejectionPipeline (D : ℕ) where

  steps : ℕ

  M : ℕ

  n : ℕ

  k : ℕ

def EnergyRejectionPipeline.ledger {D : ℕ} (p : EnergyRejectionPipeline D)
    (nStar : ℕ) : MetropolisCostLedger :=
  metropolisRunLedger p.steps D p.M p.k p.n nStar

def EnergyRejectionPipeline.Complete {D : ℕ} (p : EnergyRejectionPipeline D)
    (nStar : ℕ) : Prop :=
  (p.ledger nStar).stepQueries =
      p.steps * ((2 + nStar) * qpeWindowQueries p.M p.n) ∧
    (p.ledger nStar).stepGates = p.steps * ((2 + nStar) * qpeWindowGates p.M p.n) ∧
    (p.ledger nStar).spaceQubits = D + 2 * Nat.clog 2 p.M + 1 + p.k

structure PartialCall (I : Type*) [Fintype I] [DecidableEq I] where

  C : Circuit I

  r : ℕ

  nativeBitTime : ℕ

def PartialCall.Correct {I : Type*} [Fintype I] [DecidableEq I]
    (p : PartialCall I) : Prop :=
  p.r ≤ p.C.length ∧ p.r ≤ p.nativeBitTime

noncomputable def PartialCall.state {I : Type*} [Fintype I] [DecidableEq I]
    (p : PartialCall I) (oracle : Matrix I I ℂ) (ψ : QState I) : QState I :=
  Run oracle (queryPrefix p.C p.r) ψ

noncomputable def haarOverlapMoment (d k : ℕ) : ℝ :=
  (Nat.factorial k : ℝ) / (∏ j ∈ Finset.range k, ((d + j : ℕ) : ℝ))

def IsOverlapDesign {n : ℕ} (d k : ℕ) (f : Fin n → Operator d) : Prop :=
  k ≤ 3 ∧ 0 < n ∧
    ∀ (ρ σ : Operator d), IsPureDensityOperator ρ → IsPureDensityOperator σ →
      (∑ i : Fin n,
        ((Matrix.trace (σ * f i * ρ * Matrix.conjTranspose (f i))).re) ^ k) / (n : ℝ) =
          haarOverlapMoment d k

structure DesignSampler (w : ℕ) where

  size : ℕ

  members : Fin size → Operator (2 ^ w)

  sampleCost : ℕ

def DesignSampler.Correct (w : ℕ) (s : DesignSampler w) : Prop :=
  (∀ i : Fin s.size, s.members i ∈ Matrix.unitaryGroup (Fin (2 ^ w)) ℂ) ∧
    IsOverlapDesign (2 ^ w) 3 (fun i : Fin s.size =>
      (s.members i : Matrix (Fin (2 ^ w)) (Fin (2 ^ w)) ℂ))

def DesignSampler.PolyBounded (w : ℕ) (s : DesignSampler w) : Prop :=
  ∃ C e : ℕ, s.sampleCost ≤ C * (w + 1) ^ e

structure RealComplexInput where

  realDigits : ℕ

  complexDigits : ℕ

def RealComplexInput.Correct (x : RealComplexInput) : Prop :=
  0 < x.realDigits ∧ 0 < x.complexDigits

noncomputable def RealComplexInput.roundReal (x : RealComplexInput) (t : ℝ) : ℚ :=
  dyadicRat x.realDigits t

structure ConfidenceLedger where

  δ : ℝ

  c : ℝ

  order : ℕ

def ConfidenceLedger.Correct (L : ConfidenceLedger) : Prop :=
  0 < L.δ ∧ L.δ < 1 ∧ 0 < L.c

structure GateSynthesis (w : ℕ) where

  word : List FiniteGateCode

  ε : ℝ

  bitTime : ℕ

def GateSynthesis.Correct (w : ℕ) (g : GateSynthesis w) : Prop :=
  finiteWordLegal w g.word = true ∧ 0 < g.ε

def GateSynthesis.PolyBounded (w : ℕ) (g : GateSynthesis w) : Prop :=
  ∃ C e : ℕ,
    g.word.length ≤ C * (w + 1) ^ e ∧ g.bitTime ≤ C * (w + 1) ^ e

structure FiniteBitBackend (w : ℕ) where

  word : List FiniteGateCode

  bitTime : ℕ

  bitSpace : ℕ

def FiniteBitBackend.Correct (w : ℕ) (b : FiniteBitBackend w) : Prop :=
  finiteWordLegal w b.word = true

def instrumentPmfNotFiniteBitBackend : Prop :=
  ∀ w : ℕ, ∃ b : FiniteBitBackend w, FiniteBitBackend.Correct w b

end Qatlib.Concepts.AmplitudeSearch.Amplification
