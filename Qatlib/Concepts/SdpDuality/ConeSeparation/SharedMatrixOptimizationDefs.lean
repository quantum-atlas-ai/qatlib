/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.MatrixWeights.ApproxGibbs
import Qatlib.Concepts.RationalScan.Step2Scan.MatrixOptimizationAlgorithms
import Qatlib.Concepts.SdpMmwSolver.OracleError.SdpStep2SampledOracle
import Qatlib.Concepts.SdpDuality.ConeSeparation.MatrixOptimizationInterfaces
import Qatlib.Concepts.AmpTransform.LegendreWindow.LegendreCompleteWindow
set_option warningAsError false
set_option backward.isDefEq.respectTransparency false
open Qatlib.Concepts.ProbabilityCore.Concentration
open Qatlib.Concepts.ProbabilityCore.Concentration.FiniteDecisionTree
open Qatlib.Foundations.QueryWordCore.Circuit Qatlib.Concepts.ReferenceError.MixturePaths
open Qatlib.Concepts.QueryComplexity.DegreeMethod
open Qatlib.Concepts.AmpTransform.LegendreWindow
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.MonteCarloMean.FinDistBounds
open Qatlib.Concepts.SdpMmwSolver.OracleError

set_option autoImplicit false

namespace Qatlib.Concepts.SdpDuality.ConeSeparation

open Qatlib
open Qatlib.Concepts.SdpDuality.ConeSeparation
open Qatlib.Concepts.MatrixWeights.ApproxGibbs
open Qatlib.Concepts.RationalScan.Step2Scan
open Qatlib.Concepts.SdpDuality.ConeSeparation
open Qatlib
open scoped BigOperators Matrix.Norms.L2Operator ComplexOrder MatrixOrder

noncomputable section

open Classical

noncomputable def psdRegularizedInfimum {n : ℕ} (A B : HermitianMat (Fin n) ℂ) : ℝ :=
  ⨅ ε : Set.Ioi (0:ℝ), psdRegularizedGT A B ε

def gtEqualityBoundary {n : ℕ} (H K : Matrix (Fin n) (Fin n) ℂ) : Prop :=
  (Matrix.trace (NormedSpace.exp H * NormedSpace.exp K)).re
    = (Matrix.trace (NormedSpace.exp (H + K))).re

def gtLogInputBoundary {n : ℕ} (A B : HermitianMat (Fin n) ℂ) : Prop :=
  logInputGT A B ≤ (Matrix.trace (A.mat * B.mat)).re

structure MmwRound (O D : ℕ) where

  Λ : POVM (Fin O) (Fin D)

  ρ : Operator D

  hρ : IsDensityOperator ρ

  f : Fin O → ℝ

  hf : ∀ o, 0 ≤ f o ∧ f o ≤ 1

structure MmwRun (O D T : ℕ) where

  rounds : Fin T → MmwRound O D

abbrev MmwTranscript (T O : ℕ) : Type := Fin T → Fin O

noncomputable def MmwRound.law {O D : ℕ} (r : MmwRound O D) : FinDist (Fin O) :=
  Qatlib.Concepts.SdpDuality.ConeSeparation.povmLaw r.Λ r.ρ r.hρ

noncomputable def MmwRun.transcriptProb {O D T : ℕ} (R : MmwRun O D T)
    (ω : MmwTranscript T O) : ℝ :=
  ∏ t : Fin T, (R.rounds t).law.prob (ω t)

def MmwRound.record {O D : ℕ} (r : MmwRound O D) (o : Fin O) : ℝ := r.f o

noncomputable def MmwRound.observable {O D : ℕ} (r : MmwRound O D) : Operator D :=
  payoffObservable r.Λ r.f

noncomputable def MmwRound.actualPayoff {O D : ℕ} (r : MmwRound O D) : ℝ :=
  (Matrix.trace (r.observable * r.ρ)).re

noncomputable def MmwRun.recordAt {O D T : ℕ} (R : MmwRun O D T) (s : ℕ)
    (ω : MmwTranscript T O) : ℝ :=
  if h : s < T then (R.rounds ⟨s, h⟩ : MmwRound O D).record (ω ⟨s, h⟩) else 0

noncomputable def MmwRun.recordedPayoff {O D T : ℕ} (R : MmwRun O D T)
    (ω : MmwTranscript T O) : ℝ :=
  ∑ t : Fin T, (R.rounds t).record (ω t)

noncomputable def MmwRun.support {O D T : ℕ} (R : MmwRun O D T) :
    FiniteSupportSpace (MmwTranscript T O) where
  prob := R.transcriptProb
  prob_nonneg := by
    intro ω
    exact Finset.prod_nonneg fun t _ => (R.rounds t).law.nonneg (ω t)
  prob_sum := by
    show (∑ ω : Fin T → Fin O, ∏ t : Fin T, (R.rounds t).law.prob (ω t)) = 1
    have h := Fintype.prod_sum (κ := fun _ : Fin T => Fin O)
      (fun t o => (R.rounds t).law.prob o)
    rw [← h]
    exact Finset.prod_eq_one fun t _ => (R.rounds t).law.sum_one

def MmwRun.goodAt {O D T : ℕ} (R : MmwRun O D T) (ζ : Fin T → ℝ)
    (ω : MmwTranscript T O) : Prop :=
  ∀ t : Fin T, |(R.rounds t).record (ω t) - (R.rounds t).actualPayoff| ≤ ζ t

structure MmwRunLedger where

  rounds : ℕ

  errorMass : ℝ

  failMass : ℝ

  stopMass : ℝ

  timeoutMass : ℝ

def MmwRunLedger.discipline (L : MmwRunLedger) : Prop :=
  0 ≤ L.errorMass ∧ 0 ≤ L.failMass ∧ 0 ≤ L.stopMass ∧ 0 ≤ L.timeoutMass ∧
    L.stopMass + L.timeoutMass ≤ L.failMass

noncomputable def MmwRun.eventMass {O D T : ℕ} (R : MmwRun O D T)
    (E : Finset (MmwTranscript T O)) : ℝ :=
  ∑ ω ∈ E, R.transcriptProb ω

noncomputable def MmwRun.failureSet {O D T : ℕ} (R : MmwRun O D T) (ζ : Fin T → ℝ) :
    Finset (MmwTranscript T O) :=
  (Finset.univ : Finset (MmwTranscript T O)).filter (fun ω => ¬ R.goodAt ζ ω)

noncomputable def MmwRun.ledger {O D T : ℕ} (R : MmwRun O D T) (ζ : Fin T → ℝ)
    (stopped timedOut : Finset (MmwTranscript T O)) : MmwRunLedger where
  rounds := T
  errorMass := ∑ t : Fin T, ζ t
  failMass := R.eventMass (R.failureSet ζ)
  stopMass := R.eventMass stopped
  timeoutMass := R.eventMass timedOut

def step2CheapSeparator {D m : ℕ} (A : Fin m → Operator D) (Cv : Operator D)
    (b : Fin m → ℝ) (ρ : Operator D) (α R ε : ℝ) : Prop :=
  ∀ z : Fin m → ℝ, (∀ i, 0 ≤ z i) →
    (∑ i, z i * b i < Qatlib.Concepts.SdpDuality.ConeSeparation.noCheapWidth α R ε) →
    (∑ i, z i * (Matrix.trace (A i * ρ)).re < eq75Threshold Cv ρ α ε)

def step2NoOutputTransport {D m : ℕ} (A : Fin m → Operator D) (Cv : Operator D)
    (b : Fin m → ℝ) (ρ : Operator D) (α R ε : ℝ) : Prop :=
  step2CheapSeparator A Cv b ρ α R ε

def step2GoodEvent {m γ Nmax M L Q D : ℕ} (S : Step2Search m γ Nmax M L Q)
    (b : Fin m → ℝ) (A : Fin m → Operator D) (Cv ρ : Operator D)
    (α κ R ν : ℝ) : Prop :=
  S.goodEvent b A Cv ρ α κ R ν ∧ S.lawsOk

def step2Concentration {m γ Nmax M L Q D : ℕ} (S : Step2Search m γ Nmax M L Q)
    (A : Fin m → Operator D) (ρ : Operator D) (κ ν : ℝ)
    (k : Fin γ) (N : Fin Nmax) : Prop :=
  (∑ j : Fin M, (Matrix.trace (A (S.draws k N j) * ρ)).re) / M - (κ + ν)
      ≤ ∑ i : Fin m, S.law k i * (Matrix.trace (A i * ρ)).re

def step2IdealAcceptance {m γ Nmax M L Q D : ℕ} (S : Step2Search m γ Nmax M L Q)
    (A : Fin m → Operator D) (ρ : Operator D) (κ ν : ℝ)
    (k : Fin γ) (N : Fin Nmax) : Prop :=
  S.estC k N / Step2Search.gridMass κ N - (κ + ν)
    ≤ (∑ j : Fin M, (Matrix.trace (A (S.draws k N j) * ρ)).re) / M

structure widthTransportLedger where

  sampledWidth : ℝ

  exactWidth : ℝ

  bridgeSlack : ℝ

  rescale : ℝ

def widthTransport (α R ε : ℝ) : widthTransportLedger :=
  { sampledWidth := widthSampled α R ε
    exactWidth := widthExact α
    bridgeSlack := widthBridgeSlack α R ε
    rescale := 1 + 2 * R * ε }

structure DualMixtureReceipt (m T : ℕ) where

  j₀ : Fin m

  a : ℝ

  μ : Fin T → ℝ

  q : Fin T → Fin m → ℝ

  L : ℝ

  w : Fin (T + 1) → ℝ

noncomputable def DualMixtureReceipt.law {m T : ℕ} (S : DualMixtureReceipt m T) :
    Fin m → ℝ :=
  dualMixtureLaw S.j₀ S.a S.μ S.q

noncomputable def DualMixtureReceipt.vector {m T : ℕ} (S : DualMixtureReceipt m T) :
    Fin m → ℝ :=
  dualMixtureVector S.j₀ S.a S.μ S.q

structure rescaleLedger where

  α : ℝ

  R : ℝ

  δ : ℝ

  calls : ℕ

  failMass : ℝ

  errorMass : ℝ

def rescaleLedger.budget (L : rescaleLedger) : BisectionBudget :=
  { failMass := L.failMass, errorMass := L.errorMass, calls := L.calls }

structure backendCallCost where

  name : String

  bitTime : ℕ

  qubits : ℕ

structure backendCostLedger where

  calls : List backendCallCost

  fairBits : ℕ

  peakQubits : ℕ

def backendCostLedger.bitTime (L : backendCostLedger) : ℕ :=
  (L.calls.map (fun c => c.bitTime)).sum

def backendCostLedger.peak (L : backendCostLedger) : ℕ :=
  L.calls.foldl (fun acc c => max acc c.qubits) 0

inductive MmwCompiledStep where

  | matrixExp (accesses : List QueryDesc) (cost : IntCost)

  | comparison (accesses : List QueryDesc) (cost : IntCost)

  | rejection (accesses : List QueryDesc) (cost : IntCost)

  | adjointWord (accesses : List QueryDesc) (cost : IntCost)

  | stoppingTail (accesses : List QueryDesc) (cost : IntCost)

namespace MmwCompiledStep

def accesses : MmwCompiledStep → List QueryDesc
  | .matrixExp a _ => a
  | .comparison a _ => a
  | .rejection a _ => a
  | .adjointWord a _ => a
  | .stoppingTail a _ => a

def cost : MmwCompiledStep → IntCost
  | .matrixExp _ c => c
  | .comparison _ c => c
  | .rejection _ c => c
  | .adjointWord _ c => c
  | .stoppingTail _ c => c

def name : MmwCompiledStep → String
  | .matrixExp _ _ => "matrixExp"
  | .comparison _ _ => "comparison"
  | .rejection _ _ => "rejection"
  | .adjointWord _ _ => "adjointWord"
  | .stoppingTail _ _ => "stoppingTail"

end MmwCompiledStep

inductive MmwGateKind where

  | matrixExp

  | comparison

  | rejection

  | adjointWord

  | stoppingTail

def MmwGateSet.all : List MmwGateKind :=
  [.matrixExp, .comparison, .rejection, .adjointWord, .stoppingTail]

def MmwCompiledStep.gateKind : MmwCompiledStep → MmwGateKind
  | .matrixExp _ _ => .matrixExp
  | .comparison _ _ => .comparison
  | .rejection _ _ => .rejection
  | .adjointWord _ _ => .adjointWord
  | .stoppingTail _ _ => .stoppingTail

def MmwCompiledRun.usesFixedGates (steps : List MmwCompiledStep) : Prop :=
  ∀ s ∈ steps, s.gateKind ∈ MmwGateSet.all

def MmwCompiledRun.fairBits (steps : List MmwCompiledStep) : ℕ :=
  (steps.filter (fun s => match s with | .rejection _ _ => true | _ => false)).length

def MmwCompiledRun.cost (steps : List MmwCompiledStep) : IntCost where
  queries := (steps.map (fun s => s.cost.queries)).sum
  gates := (steps.map (fun s => s.cost.gates)).sum
  bitTime := (steps.map (fun s => s.cost.bitTime)).sum
  peakSpace := steps.foldl (fun acc s => max acc s.cost.peakSpace) 0

def MmwCompiledRun.accesses (steps : List MmwCompiledStep) : List QueryDesc :=
  steps.flatMap MmwCompiledStep.accesses

def MmwCompiledRun.ledger (steps : List MmwCompiledStep) (fairBits : ℕ) :
    backendCostLedger where
  calls := steps.map (fun s =>
    { name := MmwCompiledStep.name s
      bitTime := s.cost.bitTime
      qubits := s.cost.peakSpace })
  fairBits := fairBits
  peakQubits := steps.foldl (fun acc s => max acc s.cost.peakSpace) 0

def MmwCompiledRun.inputLength {D m : ℕ} (s : ℕ) (bits : ℕ)
    (wt : Fin m → ℚ) (β : ℚ) : ℕ :=
  totalInputLength D m s bits wt β

end
end Qatlib.Concepts.SdpDuality.ConeSeparation
