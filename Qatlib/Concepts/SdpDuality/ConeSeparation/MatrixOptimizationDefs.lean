/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.SdpDuality.ConeSeparation.MatrixOptimizationSharedDefs
import Qatlib.Concepts.RationalScan.Step2Scan.MatrixOptimizationAlgorithmsDefs
import Qatlib.Concepts.SdpDuality.ConeSeparation.MatrixOptimizationAlgorithmsDefs
set_option warningAsError false
set_option backward.isDefEq.respectTransparency false
open Qatlib.Concepts.MixedFidelity.FidelityMetric
open Qatlib.Concepts.ProbabilityCore.Concentration
open Qatlib.Concepts.ProbabilityCore.Concentration.FiniteDecisionTree
open Qatlib.Foundations.QueryWordCore.Circuit Qatlib.Concepts.ReferenceError.MixturePaths
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.SdpMmwSolver.OracleError
open Qatlib.Foundations.BornMetrics.EventProbability
open Qatlib.Concepts.GateVocabulary.FiniteGateDescription

set_option autoImplicit false

namespace Qatlib.Concepts.SdpDuality.ConeSeparation

open scoped BigOperators Matrix.Norms.L2Operator

open Qatlib
open Qatlib.Concepts.SdpDuality.ConeSeparation
open Qatlib.Concepts.RationalScan.Step2Scan
open Qatlib.Concepts.SdpDuality.ConeSeparation
open Qatlib.Concepts.RationalScan.Step2Scan
noncomputable section

inductive Step2Scan (γ Nmax : ℕ) where

  | hit (k : Fin γ) (N : Fin Nmax)

  | noOutput

namespace Step2Scan

variable {γ Nmax : ℕ}

def roundVector (m : ℕ) (κ : ℝ) {M : ℕ} (loop : Step2Loop m γ Nmax M) :
    Step2Scan γ Nmax → Fin m → ℝ
  | hit k N => step2RoundVector m (step2Mass κ N) (loop.law k)
  | noOutput => fun _ => 0

def sound (m : ℕ) (b : Fin m → ℝ) {M : ℕ} (loop : Step2Loop m γ Nmax M)
    (α R κ ν : ℝ) : Step2Scan γ Nmax → Prop
  | hit k N =>
      step2Accepts m M b (loop.estA k N) (loop.estC k N) (loop.draws k N) α R κ ν
        (step2Mass κ N) ∧
      ∀ (k' : Fin γ) (N' : Fin Nmax),
        step2PairIndex k' N' < step2PairIndex k N →
          ¬ step2Accepts m M b (loop.estA k' N') (loop.estC k' N') (loop.draws k' N')
            α R κ ν (step2Mass κ N')
  | noOutput => Step2NoOutput m γ Nmax M b loop α R κ ν

end Step2Scan

structure Step2Run (m γ Nmax M L : ℕ) where

  loop : Step2Loop m γ Nmax M

  scan : Step2Scan γ Nmax

  pairs : ℕ

  gibbsCopies : ℕ

  qDraws : ℕ

  stateCopies : ℕ

  entryQueries : ℕ

def Step2Run.legal {m γ Nmax M L : ℕ} (b : Fin m → ℝ) (run : Step2Run m γ Nmax M L)
    (α R κ ν : ℝ) (s : ℕ) : Prop :=
  Step2Scan.sound m b run.loop α R κ ν run.scan ∧
    Step2SampleLedger γ Nmax M L run.pairs run.gibbsCopies run.qDraws run.stateCopies ∧
    run.entryQueries ≤ (run.gibbsCopies + run.stateCopies) * s + run.qDraws

def Step2Loop.sameProgram {m γ Nmax M : ℕ} (L₁ L₂ : Step2Loop m γ Nmax M) : Prop :=
  L₁.law = L₂.law ∧ L₁.estA = L₂.estA ∧ L₁.estC = L₂.estC

def step2TableConcentrates {m γ Nmax M : ℕ} (b : Fin m → ℝ)
    (law : Fin γ → Fin m → ℝ) (estA : Fin γ → Fin Nmax → Fin m → ℝ)
    (tab : Fin γ → Fin Nmax → Fin M → Fin m) (κ R ν : ℝ) : Prop :=
  ∀ (k : Fin γ) (N : Fin Nmax),
    |(∑ i : Fin m, law k i * b i) - (∑ j : Fin M, b (tab k N j)) / (M : ℝ)| ≤ R * (κ + ν) ∧
    |(∑ j : Fin M, estA k N (tab k N j)) / (M : ℝ) - (∑ i : Fin m, law k i * estA k N i)| ≤
      κ + ν

def step2GoodFailProb (m γ Nmax M : ℕ) (b : Fin m → ℝ)
    (law : Fin γ → Fin m → ℝ) (estA : Fin γ → Fin Nmax → Fin m → ℝ) (κ R ν : ℝ) : ℝ :=
  loopEventProb m γ Nmax M law
    (fun tab => ¬ step2TableConcentrates b law estA tab κ R ν)

def step2GoodFailBound (γ Nmax M : ℕ) (κ ν R : ℝ) : ℝ :=
  2 * (γ * Nmax : ℝ) *
    (matrixHoeffdingTail 1 M (κ + ν) R + matrixHoeffdingTail 1 M (κ + ν) 2)

def Step2UnifiedGoodEvent {D m γ Nmax M : ℕ} (A : Fin m → Operator D) (Cv : Operator D)
    (b : Fin m → ℝ) (ρ : Operator D) (loop : Step2Loop m γ Nmax M) (κ R ν : ℝ) : Prop :=
  Step2LoopLegal D m γ Nmax M A Cv b ρ loop κ R ν ∧
    Step2GoodEvent m γ Nmax M b loop κ R ν

structure TimeoutSupport where

  budget : ℕ

  truncMass : ℝ

  expectedCost : ℝ

  tail : ℕ → ℝ

def TimeoutSupport.legal (S : TimeoutSupport) : Prop :=
  0 ≤ S.truncMass ∧ 0 ≤ S.expectedCost ∧ (∀ k, 0 ≤ S.tail k) ∧
    (S.budget = 0 → S.truncMass = 0) ∧
    (0 < S.budget → S.tail S.budget ≤ S.truncMass)

def step2CeilGridPoint (α κ : ℝ) : ℕ := Nat.ceil (α / κ)

def step2CeilOverBound (α κ : ℝ) : Prop :=
  α < κ * (step2CeilGridPoint α κ : ℝ) ∧
    (Nat.floor (α / κ) : ℝ) < (step2CeilGridPoint α κ : ℝ)

def noCheapAt (D m : ℕ) (A : Fin m → Operator D) (Cv : Operator D) (b : Fin m → ℝ)
    (ρ : Operator D) (α R ε : ℝ) : Prop :=
  ∀ z : Fin m → ℝ, (∀ i, 0 ≤ z i) →
    ((Matrix.trace (Cv * ρ)).re - 3 * α * ε ≤
      ∑ i, z i * (Matrix.trace (A i * ρ)).re) →
    α * (1 - 3 * R * ε) ≤ ∑ i, z i * b i

def noOutputUnconditionalBoundary : Prop :=
  ∃ (D m γ Nmax M : ℕ) (A : Fin m → Operator D) (Cv : Operator D) (b : Fin m → ℝ)
      (ρ : Operator D) (loop : Step2Loop m γ Nmax M) (α R κ ν ε : ℝ),
    0 < D ∧ 0 < m ∧ 0 < α ∧ 0 < R ∧ 0 < ε ∧ 0 < κ ∧ 0 < ν ∧ 3 * R * ε < 1 ∧
    (∀ i, (A i).IsHermitian ∧ ‖A i‖ ≤ 1) ∧
    Cv.IsHermitian ∧ ‖Cv‖ ≤ 1 ∧
    (∀ i, 1 ≤ b i) ∧
    IsDensityOperator ρ ∧
    Step2LoopLegal D m γ Nmax M A Cv b ρ loop κ R ν ∧
    ¬ Step2GoodEvent m γ Nmax M b loop κ R ν ∧
    Step2NoOutput m γ Nmax M b loop α R κ ν ∧
    ¬ noCheapAt D m A Cv b ρ α R ε

def widthWrongStrongBoundary : Prop :=
  ∃ (D m : ℕ) (A : Fin m → Operator D) (Cv : Operator D) (b : Fin m → ℝ)
      (y : ℕ → Fin m → ℝ) (j₀ : Fin m) (α R ε : ℝ),
    0 < D ∧ 0 < m ∧ 2 ≤ α ∧ 0 < R ∧ 0 < ε ∧ 2 * R * ε ≤ 1 / 2 ∧
    (∀ i, (A i).IsHermitian ∧ ‖A i‖ ≤ 1) ∧
    Cv.IsHermitian ∧ ‖Cv‖ ≤ 1 ∧
    (∀ i, 1 ≤ b i) ∧ A j₀ = 1 ∧ b j₀ = R ∧
    (∀ t, (∀ i, 0 ≤ y t i) ∧ ∑ i, b i * y t i ≤ α * (1 + 4 * R * ε)) ∧
    α * (1 + 2 * R * ε) < ∑ i, b i * y 0 i ∧
    ¬ payoffUnitInterval D (dualPayoff D m A Cv α y 0)

structure SparsifySample (m Q : ℕ) where

  q : Fin m → ℝ

  idx : Fin Q → Fin m

def SparsifySample.independent {m Q : ℕ} (S : SparsifySample m Q) : Prop :=
  IsSamplingLaw m S.q

def SparsifySample.boundedSummands {D m Q : ℕ} (A : Fin m → Operator D)
    (S : SparsifySample m Q) (mass α : ℝ) : Prop :=
  ∀ j : Fin Q,
    ‖((mass / (4 * α) : ℝ)) • (A (S.idx j) - (∑ i, S.q i • A i))‖ ≤
      sparsifySummandBound mass α

def sparsifyOperatorError {D m Q : ℕ} (A : Fin m → Operator D) (Cv : Operator D)
    (y : Fin m → ℝ) (S : SparsifySample m Q) (α mass bound : ℝ) : Prop :=
  ‖sdpScaledSparsifiedPayoff D m Q A Cv α mass S.idx -
    Qatlib.Concepts.SdpDuality.ConeSeparation.sourceScaledPayoff A Cv α y‖ ≤ bound

structure RunEventLedger where

  unionFail : ℝ

  stopTail : ℕ → ℝ

  timeoutMass : ℝ

def RunEventLedger.legal (L : RunEventLedger) (budget : ℝ) : Prop :=
  0 ≤ L.unionFail ∧ 0 ≤ L.timeoutMass ∧ (∀ k, 0 ≤ L.stopTail k) ∧
    L.unionFail + L.timeoutMass ≤ budget

def lawTV {m : ℕ} (p q : Fin m → ℝ) : ℝ := l1Dist p q / 2

structure HistoryCopyLedger where

  gibbsCalls : ℕ

  measCopies : ℕ

  sampleDraws : ℕ

def HistoryCopyLedger.legal (T Q L : ℕ) (H : HistoryCopyLedger) : Prop :=
  H.gibbsCalls = T * (Q + 1) ∧ H.measCopies = T * 2 * L ∧ H.sampleDraws = T * Q

inductive Alg3RunPath where

  | controlledEntry

  | controlledSparseRow

  | hOracle

  | gibbsPrepare

  | estimation

  | sampleReject

  | binaryShell

  | inverseWord

  | classicalArith

  | timeoutTrunc
  deriving DecidableEq, Repr

structure SdpResourceParams where

  dim : ℕ

  constraints : ℕ

  sparsity : ℕ

  inputWord : ℕ

  truncBits : ℕ

  eps : ℝ

  delta : ℝ

  xi : ℝ

  sizeR : ℝ

def SdpResourceParams.legal (P : SdpResourceParams) : Prop :=
  0 < P.dim ∧ 0 < P.constraints ∧ 0 < P.sparsity ∧ 0 < P.inputWord ∧
    0 < P.eps ∧ P.eps ≤ 1 / 2 ∧ 0 < P.delta ∧ P.delta ≤ 1 ∧ 1 < P.xi ∧ 1 ≤ P.sizeR

structure PathCost where

  queries : ℕ

  twoQubitGates : ℕ

  fairBits : ℕ

  bitTime : ℕ

  peakSpace : ℕ

  intBits : ℕ

structure PathBound where

  queries : ℝ

  twoQubitGates : ℝ

  fairBits : ℝ

  bitTime : ℝ

  peakSpace : ℝ

  intBits : ℕ

structure RunPathCompile where

  width : ℕ

  word : List FiniteGateCode

  cost : PathCost

  bound : PathBound

def RunPathCompile.legal (C : RunPathCompile) : Prop :=
  finiteWordLegal C.width C.word = true ∧
    (C.cost.queries : ℝ) ≤ C.bound.queries ∧
    (C.cost.twoQubitGates : ℝ) ≤ C.bound.twoQubitGates ∧
    (C.cost.fairBits : ℝ) ≤ C.bound.fairBits ∧
    (C.cost.bitTime : ℝ) ≤ C.bound.bitTime ∧
    (C.cost.peakSpace : ℝ) ≤ C.bound.peakSpace ∧
    C.cost.intBits ≤ C.bound.intBits

def runGateBound (D : ℕ) (prec calls : ℝ) : ℝ :=
  calls * (64 * D + 128) * (((Nat.ceil ((1 / prec) ^ 2) : ℕ) : ℝ) + 1)

def runIntegerBitBound (P : SdpResourceParams) : ℕ :=
  sdpIntegerBits (2 * P.inputWord + P.truncBits + 8) (sdpPrecisionBits P.eps)

def SoftOBounded (actual budget C N : ℝ) (k : ℕ) : Prop :=
  1 ≤ C ∧ 1 ≤ N ∧ actual ≤ C * budget * (max 1 (Real.log N)) ^ k

def safeLog (x : ℝ) : ℝ := max 1 (Real.log x)

def safeFailureBudget (n m : ℕ) (R δ ξ cO : ℝ) : ℝ :=
  cO * ((R / δ) ^ 18 * (safeLog ((n : ℝ) * (m : ℝ))) ^ 10 *
    Real.exp (-(safeLog ((n : ℝ) * (m : ℝ))) ^ ξ))

structure Alg3DegenerateBranch (n m : ℕ) where

  rounds : ℕ

  samplesM : ℕ

  samplesL : ℕ

  failCharge : ℝ

def Alg3DegenerateBranch.legal {n m : ℕ} (B : Alg3DegenerateBranch n m)
    (R δ ξ cO : ℝ) : Prop :=
  0 < B.rounds ∧ 0 < B.samplesM ∧ 0 < B.samplesL ∧ 0 ≤ B.failCharge ∧
    B.failCharge ≤ safeFailureBudget n m R δ ξ cO

end

end Qatlib.Concepts.SdpDuality.ConeSeparation
