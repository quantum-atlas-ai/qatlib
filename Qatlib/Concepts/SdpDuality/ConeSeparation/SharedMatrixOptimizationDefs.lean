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

/-!
# Matrix optimization rounds and compilation ledgers

This module defines `MmwRound`, fixed sequences `MmwRun`, and their transcript probabilities,
payoff records, accuracy events, and accounting ledgers. It also records logarithmic trace
boundaries and predicates relating Step 2 sampling estimates to exact payoff expressions.

`DualMixtureReceipt`, `widthTransport`, and the compiled-step structures organize dual mixtures,
width corrections, and resource counts used in matrix multiplicative weights implementations of
quantum SDP algorithms; see [BrandaoSvore2017].

## Main definitions

* `MmwRun.support`: the finite transcript probability space.
* `step2GoodEvent`: search accuracy and valid candidate laws.
* `MmwCompiledRun.cost`: aggregate compiled resource costs.

## References

* [Brandao and Svore, 2017][BrandaoSvore2017]
-/

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

/-- The infimum of the regularized logarithmic trace expression over the subtype of positive
real parameters. -/
noncomputable def psdRegularizedInfimum {n : ℕ} (A B : HermitianMat (Fin n) ℂ) : ℝ :=
  ⨅ ε : Set.Ioi (0:ℝ), psdRegularizedGT A B ε

/-- States equality between the real traces of `exp H * exp K` and `exp (H + K)`. -/
def gtEqualityBoundary {n : ℕ} (H K : Matrix (Fin n) (Fin n) ℂ) : Prop :=
  (Matrix.trace (NormedSpace.exp H * NormedSpace.exp K)).re
    = (Matrix.trace (NormedSpace.exp (H + K))).re

/-- The Golden–Thompson trace inequality for the spectral logarithms of `A` and `B`. -/
def gtLogInputBoundary {n : ℕ} (A B : HermitianMat (Fin n) ℂ) : Prop :=
  logInputGT A B ≤ (Matrix.trace (A.mat * B.mat)).re

/-- A matrix multiplicative weights measurement round comprising a POVM, a density operator, and
an outcome payoff in `[0, 1]`. -/
structure MmwRound (O D : ℕ) where

  Λ : POVM (Fin O) (Fin D)

  ρ : Operator D

  hρ : IsDensityOperator ρ

  f : Fin O → ℝ

  hf : ∀ o, 0 ≤ f o ∧ f o ≤ 1

/-- A fixed sequence of `T` matrix multiplicative weights measurement rounds. -/
structure MmwRun (O D T : ℕ) where

  rounds : Fin T → MmwRound O D

/-- A length-`T` outcome record with entries in `Fin O`. -/
abbrev MmwTranscript (T O : ℕ) : Type := Fin T → Fin O

/-- The finite POVM outcome distribution of the round on its density operator. -/
noncomputable def MmwRound.law {O D : ℕ} (r : MmwRound O D) : FinDist (Fin O) :=
  Qatlib.Concepts.SdpDuality.ConeSeparation.povmLaw r.Λ r.ρ r.hρ

/-- The product of the round outcome probabilities along a transcript. -/
noncomputable def MmwRun.transcriptProb {O D T : ℕ} (R : MmwRun O D T)
    (ω : MmwTranscript T O) : ℝ :=
  ∏ t : Fin T, (R.rounds t).law.prob (ω t)

/-- The payoff recorded for the outcome `o`. -/
def MmwRound.record {O D : ℕ} (r : MmwRound O D) (o : Fin O) : ℝ := r.f o

/-- The POVM payoff observable associated with the round's outcome payoff function. -/
noncomputable def MmwRound.observable {O D : ℕ} (r : MmwRound O D) : Operator D :=
  payoffObservable r.Λ r.f

/-- The real trace of the round's payoff observable against its density operator. -/
noncomputable def MmwRound.actualPayoff {O D : ℕ} (r : MmwRound O D) : ℝ :=
  (Matrix.trace (r.observable * r.ρ)).re

/-- The recorded payoff at time `s`, with value zero for indices outside the run. -/
noncomputable def MmwRun.recordAt {O D T : ℕ} (R : MmwRun O D T) (s : ℕ)
    (ω : MmwTranscript T O) : ℝ :=
  if h : s < T then (R.rounds ⟨s, h⟩ : MmwRound O D).record (ω ⟨s, h⟩) else 0

/-- The sum of recorded round payoffs along the transcript. -/
noncomputable def MmwRun.recordedPayoff {O D T : ℕ} (R : MmwRun O D T)
    (ω : MmwTranscript T O) : ℝ :=
  ∑ t : Fin T, (R.rounds t).record (ω t)

/-- The normalized finite probability space whose masses are the independent-round transcript
probabilities. -/
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

/-- States that every recorded round payoff differs from its actual payoff by at most the
corresponding allowance `ζ t`. -/
def MmwRun.goodAt {O D T : ℕ} (R : MmwRun O D T) (ζ : Fin T → ℝ)
    (ω : MmwTranscript T O) : Prop :=
  ∀ t : Fin T, |(R.rounds t).record (ω t) - (R.rounds t).actualPayoff| ≤ ζ t

/-- A record of round count, accumulated error, failure mass, stop mass, and timeout mass. -/
structure MmwRunLedger where

  rounds : ℕ

  errorMass : ℝ

  failMass : ℝ

  stopMass : ℝ

  timeoutMass : ℝ

/-- Requires nonnegative error and probability masses, with combined stop and timeout masses
bounded by the failure mass. -/
def MmwRunLedger.discipline (L : MmwRunLedger) : Prop :=
  0 ≤ L.errorMass ∧ 0 ≤ L.failMass ∧ 0 ≤ L.stopMass ∧ 0 ≤ L.timeoutMass ∧
    L.stopMass + L.timeoutMass ≤ L.failMass

/-- The sum of transcript probabilities over the finite event `E`. -/
noncomputable def MmwRun.eventMass {O D T : ℕ} (R : MmwRun O D T)
    (E : Finset (MmwTranscript T O)) : ℝ :=
  ∑ ω ∈ E, R.transcriptProb ω

/-- The finite set of transcripts for which at least one recorded payoff violates its allowance. -/
noncomputable def MmwRun.failureSet {O D T : ℕ} (R : MmwRun O D T) (ζ : Fin T → ℝ) :
    Finset (MmwTranscript T O) :=
  (Finset.univ : Finset (MmwTranscript T O)).filter (fun ω => ¬ R.goodAt ζ ω)

/-- The run ledger containing the sum of round error allowances and the probability masses of
failure, stopping, and timeout events. -/
noncomputable def MmwRun.ledger {O D T : ℕ} (R : MmwRun O D T) (ζ : Fin T → ℝ)
    (stopped timedOut : Finset (MmwTranscript T O)) : MmwRunLedger where
  rounds := T
  errorMass := ∑ t : Fin T, ζ t
  failMass := R.eventMass (R.failureSet ζ)
  stopMass := R.eventMass stopped
  timeoutMass := R.eventMass timedOut

/-- States that any nonnegative vector costing less than `noCheapWidth` has payoff strictly
below `eq75Threshold`. -/
def step2CheapSeparator {D m : ℕ} (A : Fin m → Operator D) (Cv : Operator D)
    (b : Fin m → ℝ) (ρ : Operator D) (α R ε : ℝ) : Prop :=
  ∀ z : Fin m → ℝ, (∀ i, 0 ≤ z i) →
    (∑ i, z i * b i < Qatlib.Concepts.SdpDuality.ConeSeparation.noCheapWidth α R ε) →
    (∑ i, z i * (Matrix.trace (A i * ρ)).re < eq75Threshold Cv ρ α ε)

/-- The Step 2 cheap-vector separation predicate, expressed through `step2CheapSeparator`. -/
def step2NoOutputTransport {D m : ℕ} (A : Fin m → Operator D) (Cv : Operator D)
    (b : Fin m → ℝ) (ρ : Operator D) (α R ε : ℝ) : Prop :=
  step2CheapSeparator A Cv b ρ α R ε

/-- Combines the Step 2 accuracy event with normalization and nonnegativity of all candidate
laws. -/
def step2GoodEvent {m γ Nmax M L Q D : ℕ} (S : Step2Search m γ Nmax M L Q)
    (b : Fin m → ℝ) (A : Fin m → Operator D) (Cv ρ : Operator D)
    (α κ R ν : ℝ) : Prop :=
  S.goodEvent b A Cv ρ α κ R ν ∧ S.lawsOk

/-- Bounds the sampled average of exact constraint payoffs, minus `κ + ν`, by the candidate
law's mean payoff. -/
def step2Concentration {m γ Nmax M L Q D : ℕ} (S : Step2Search m γ Nmax M L Q)
    (A : Fin m → Operator D) (ρ : Operator D) (κ ν : ℝ)
    (k : Fin γ) (N : Fin Nmax) : Prop :=
  (∑ j : Fin M, (Matrix.trace (A (S.draws k N j) * ρ)).re) / M - (κ + ν)
      ≤ ∑ i : Fin m, S.law k i * (Matrix.trace (A i * ρ)).re

/-- Requires the sampled average of exact constraint payoffs to meet the scaled empirical
objective threshold. -/
def step2IdealAcceptance {m γ Nmax M L Q D : ℕ} (S : Step2Search m γ Nmax M L Q)
    (A : Fin m → Operator D) (ρ : Operator D) (κ ν : ℝ)
    (k : Fin γ) (N : Fin Nmax) : Prop :=
  S.estC k N / Step2Search.gridMass κ N - (κ + ν)
    ≤ (∑ j : Fin M, (Matrix.trace (A (S.draws k N j) * ρ)).re) / M

/-- A record of sampled width, exact width, bridge slack, and a rescaling factor. -/
structure widthTransportLedger where

  sampledWidth : ℝ

  exactWidth : ℝ

  bridgeSlack : ℝ

  rescale : ℝ

/-- The width transport record built from `widthSampled`, `widthExact`, and `widthBridgeSlack`,
with rescaling factor `1 + 2 * R * ε`. -/
def widthTransport (α R ε : ℝ) : widthTransportLedger :=
  { sampledWidth := widthSampled α R ε
    exactWidth := widthExact α
    bridgeSlack := widthBridgeSlack α R ε
    rescale := 1 + 2 * R * ε }

/-- Data describing a distinguished correction component and round mixture components, together
with proposed scale and mixture weights. -/
structure DualMixtureReceipt (m T : ℕ) where

  j₀ : Fin m

  a : ℝ

  μ : Fin T → ℝ

  q : Fin T → Fin m → ℝ

  L : ℝ

  w : Fin (T + 1) → ℝ

/-- The normalized dual mixture law determined by the receipt's correction and round components. -/
noncomputable def DualMixtureReceipt.law {m T : ℕ} (S : DualMixtureReceipt m T) :
    Fin m → ℝ :=
  dualMixtureLaw S.j₀ S.a S.μ S.q

/-- The unnormalized dual mixture vector determined by the receipt's correction and round
components. -/
noncomputable def DualMixtureReceipt.vector {m T : ℕ} (S : DualMixtureReceipt m T) :
    Fin m → ℝ :=
  dualMixtureVector S.j₀ S.a S.μ S.q

/-- A record of rescaling parameters, call count, and failure and error masses. -/
structure rescaleLedger where

  α : ℝ

  R : ℝ

  δ : ℝ

  calls : ℕ

  failMass : ℝ

  errorMass : ℝ

/-- The bisection budget obtained by retaining the ledger's call count and failure and error
masses. -/
def rescaleLedger.budget (L : rescaleLedger) : BisectionBudget :=
  { failMass := L.failMass, errorMass := L.errorMass, calls := L.calls }

/-- A named backend call with integer bit time and qubit usage. -/
structure backendCallCost where

  name : String

  bitTime : ℕ

  qubits : ℕ

/-- A sequence of backend call costs with fair-bit and peak-qubit counts. -/
structure backendCostLedger where

  calls : List backendCallCost

  fairBits : ℕ

  peakQubits : ℕ

/-- The sum of the bit times of all recorded backend calls. -/
def backendCostLedger.bitTime (L : backendCostLedger) : ℕ :=
  (L.calls.map (fun c => c.bitTime)).sum

/-- The maximum qubit usage among the recorded backend calls, defaulting to zero. -/
def backendCostLedger.peak (L : backendCostLedger) : ℕ :=
  L.calls.foldl (fun acc c => max acc c.qubits) 0

/-- A compiled matrix optimization step tagged as matrix exponential, comparison, rejection,
adjoint word, or stopping tail, with query accesses and resource costs. -/
inductive MmwCompiledStep where

  | matrixExp (accesses : List QueryDesc) (cost : IntCost)

  | comparison (accesses : List QueryDesc) (cost : IntCost)

  | rejection (accesses : List QueryDesc) (cost : IntCost)

  | adjointWord (accesses : List QueryDesc) (cost : IntCost)

  | stoppingTail (accesses : List QueryDesc) (cost : IntCost)

namespace MmwCompiledStep

/-- The list of query descriptors carried by a compiled step. -/
def accesses : MmwCompiledStep → List QueryDesc
  | .matrixExp a _ => a
  | .comparison a _ => a
  | .rejection a _ => a
  | .adjointWord a _ => a
  | .stoppingTail a _ => a

/-- The integer resource cost carried by a compiled step. -/
def cost : MmwCompiledStep → IntCost
  | .matrixExp _ c => c
  | .comparison _ c => c
  | .rejection _ c => c
  | .adjointWord _ c => c
  | .stoppingTail _ c => c

/-- The string naming the operation tag of a compiled step. -/
def name : MmwCompiledStep → String
  | .matrixExp _ _ => "matrixExp"
  | .comparison _ _ => "comparison"
  | .rejection _ _ => "rejection"
  | .adjointWord _ _ => "adjointWord"
  | .stoppingTail _ _ => "stoppingTail"

end MmwCompiledStep

/-- The five operation tags used by compiled matrix multiplicative weights steps. -/
inductive MmwGateKind where

  | matrixExp

  | comparison

  | rejection

  | adjointWord

  | stoppingTail

/-- The list containing all five compiled operation tags. -/
def MmwGateSet.all : List MmwGateKind :=
  [.matrixExp, .comparison, .rejection, .adjointWord, .stoppingTail]

/-- The operation tag corresponding to a compiled step's constructor. -/
def MmwCompiledStep.gateKind : MmwCompiledStep → MmwGateKind
  | .matrixExp _ _ => .matrixExp
  | .comparison _ _ => .comparison
  | .rejection _ _ => .rejection
  | .adjointWord _ _ => .adjointWord
  | .stoppingTail _ _ => .stoppingTail

/-- States that every compiled step's operation tag belongs to `MmwGateSet.all`. -/
def MmwCompiledRun.usesFixedGates (steps : List MmwCompiledStep) : Prop :=
  ∀ s ∈ steps, s.gateKind ∈ MmwGateSet.all

/-- The number of compiled steps tagged as rejection operations. -/
def MmwCompiledRun.fairBits (steps : List MmwCompiledStep) : ℕ :=
  (steps.filter (fun s => match s with | .rejection _ _ => true | _ => false)).length

/-- Sums query, gate, and bit time costs and takes the maximum peak space over all compiled
steps. -/
def MmwCompiledRun.cost (steps : List MmwCompiledStep) : IntCost where
  queries := (steps.map (fun s => s.cost.queries)).sum
  gates := (steps.map (fun s => s.cost.gates)).sum
  bitTime := (steps.map (fun s => s.cost.bitTime)).sum
  peakSpace := steps.foldl (fun acc s => max acc s.cost.peakSpace) 0

/-- The concatenation of all query descriptor lists in the compiled run. -/
def MmwCompiledRun.accesses (steps : List MmwCompiledStep) : List QueryDesc :=
  steps.flatMap MmwCompiledStep.accesses

/-- The backend ledger obtained from the compiled steps' names, bit times, and peak spaces, with
the supplied fair-bit count. -/
def MmwCompiledRun.ledger (steps : List MmwCompiledStep) (fairBits : ℕ) :
    backendCostLedger where
  calls := steps.map (fun s =>
    { name := MmwCompiledStep.name s
      bitTime := s.cost.bitTime
      qubits := s.cost.peakSpace })
  fairBits := fairBits
  peakQubits := steps.foldl (fun acc s => max acc s.cost.peakSpace) 0

/-- The total rational input encoding length for the specified matrix dimensions, sparsity,
precision, weights, and parameter `β`. -/
def MmwCompiledRun.inputLength {D m : ℕ} (s : ℕ) (bits : ℕ)
    (wt : Fin m → ℚ) (β : ℚ) : ℕ :=
  totalInputLength D m s bits wt β

end
end Qatlib.Concepts.SdpDuality.ConeSeparation
