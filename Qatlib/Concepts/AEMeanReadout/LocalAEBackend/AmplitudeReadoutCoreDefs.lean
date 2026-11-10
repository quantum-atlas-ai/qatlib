/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.AEMeanReadout.LocalAEBackend.SearchDefs
import Qatlib.Concepts.MonteCarloMean.PayoffRotation.RationalPayoffRotation
import Qatlib.Concepts.AEMeanReadout.LocalAEBackend.Corollary14Stat
import Qatlib.Concepts.AEMeanReadout.LocalAEBackend.Theorem15ApproxCountStat
import Qatlib.Concepts.AEMeanReadout.LocalAEBackend.Theorem17Stat
set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 800000

open Qatlib.Foundations.QueryWordCore.Circuit Qatlib.Concepts.ReferenceError.MixturePaths
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.SpectralFilter.PhaseReadout
open Qatlib.Concepts.BlockEncoding.LCU Qatlib.Foundations.PureStateMath.BornBridge
open Qatlib.Concepts.CopyEvolution.Discriminate

open Qatlib.Concepts.ProbabilityCore.Concentration.FiniteDecisionTree
open Qatlib.Concepts.AmplitudeCore.PayoffMedian
open Qatlib.Concepts.AmplitudeCore.PayoffMedian.SignedMean
open Qatlib.Concepts.AmplitudeCore.PreparedReadout
open Qatlib.Foundations.BornMetrics.EventProbability
open Qatlib.Concepts.GateVocabulary.FiniteGateDescription
open Qatlib.Concepts.PhaseGeometry.RationalCayleyPhase Qatlib.Concepts.MonteCarloMean.PayoffRotation

namespace Qatlib.Concepts.AEMeanReadout.LocalAEBackend

open Matrix
open scoped Classical BigOperators Matrix.Norms.L2Operator

structure RealApprox where

  value : ℚ

  err : ℝ

def RealApprox.Wellformed (a : RealApprox) : Prop := 0 ≤ a.err

structure LayerTable where

  layers : ℕ

  results : ℕ

  cells : Fin layers → Fin results → ℚ

def LayerTable.Wellformed (t : LayerTable) : Prop :=
  0 < t.layers ∧ 0 < t.results ∧ (∀ l z, 0 ≤ t.cells l z ∧ t.cells l z ≤ 1)

structure JointErrorRecord where

  inputApprox : ℝ

  forwardAccess : ℝ

  inverseAccess : ℝ

  decoderErr : ℝ

def JointErrorRecord.programErr (e : JointErrorRecord) : ℝ :=
  e.forwardAccess + e.inverseAccess + e.decoderErr

def JointErrorRecord.total (e : JointErrorRecord) : ℝ :=
  e.inputApprox + e.programErr

structure ReadoutRequest where

  basisSize : ℕ

  frame : Fin basisSize → Fin basisSize → ℚ × ℚ

  payoff : Fin basisSize → ℚ

  payoffErr : ℝ

  normErr : ℝ

  phaseErr : ℝ

  frameErr : ℝ

  tol : ℝ

  prec : ℕ

def ReadoutRequest.inputBudget (r : ReadoutRequest) : ℝ :=
  r.payoffErr + r.normErr + r.phaseErr + r.frameErr

noncomputable def ReadoutRequest.target (r : ReadoutRequest) : ℝ :=
  if r.basisSize = 0 then 0 else (∑ i, (r.payoff i : ℝ)) / r.basisSize

def ReadoutRequest.Legal (r : ReadoutRequest) : Prop :=
  0 < r.basisSize ∧
    (∀ i, 0 ≤ r.payoff i ∧ r.payoff i ≤ 1) ∧
    0 ≤ r.payoffErr ∧ 0 ≤ r.normErr ∧ 0 ≤ r.phaseErr ∧ 0 ≤ r.frameErr ∧
    r.inputBudget < r.tol ∧ r.tol ≤ 1

structure ReadoutProgram where

  wires : ℕ

  prec : ℕ

  prepareWord : List FiniteGateCode

  prepareInvWord : List FiniteGateCode

  table : LayerTable

  tableSelectWord : List FiniteGateCode

  phaseInversion : List FiniteGateCode

  decoder : Reg wires → ℚ

  gcdSteps : ℕ

def ReadoutProgram.synthWord (P : ReadoutProgram) : List FiniteGateCode :=
  P.prepareWord ++ P.tableSelectWord ++ P.phaseInversion

def ReadoutProgram.Legal (P : ReadoutProgram) : Prop :=
  finiteWordLegal P.wires P.synthWord = true ∧
    P.prepareInvWord = finiteWordAdjoint P.prepareWord

noncomputable def ReadoutProgram.runState (P : ReadoutProgram) : QState (Reg P.wires) :=
  Run (1 : Matrix (Reg P.wires) (Reg P.wires) ℂ) (finiteCodeCircuit P.wires P.synthWord)
    (Qatlib.Foundations.PureStateMath.Ket (fun _ => false))

noncomputable def ReadoutProgram.successEvent (P : ReadoutProgram) (r : ReadoutRequest)
    (w : ℝ) : Finset (Reg P.wires) :=
  Finset.univ.filter (fun z => |(P.decoder z : ℝ) - r.target| ≤ w)

noncomputable def ReadoutProgram.successProb (P : ReadoutProgram) (r : ReadoutRequest)
    (w : ℝ) : ℝ :=
  MeasureProb P.runState (P.successEvent r w)

def ReadoutProgram.TableFaithful (P : ReadoutProgram) (r : ReadoutRequest) : Prop :=
  P.table.results = r.basisSize ∧ P.table.Wellformed ∧
    (∀ (l : Fin P.table.layers) (z : Fin P.table.results) (i : Fin r.basisSize),
      z.val = i.val →
      |(P.table.cells l z : ℝ) - (r.payoff i : ℝ)| ≤ r.payoffErr + r.phaseErr)

def ReadoutProgram.SolvesAt (P : ReadoutProgram) (r : ReadoutRequest) : Prop :=
  ∃ e : JointErrorRecord,
    e.inputApprox = r.inputBudget ∧
      e.total ≤ r.tol ∧
      (2 : ℝ) / 3 ≤ P.successProb r e.programErr ∧
      P.TableFaithful r

structure ReadoutLedger where

  bitLength : ℕ

  gcdSteps : ℕ

  persistentSpace : ℕ

  peakSpace : ℕ

  gateCount : ℕ

  forwardAccesses : ℕ

  inverseAccesses : ℕ

def readoutBitShape (basisSize prec : ℕ) : ℕ := (basisSize + 1) * (prec + 1)

def readoutGcdShape (basisSize prec : ℕ) : ℕ := basisSize + prec + 1

def readoutPersistentShape (basisSize prec : ℕ) : ℕ := 2 * readoutBitShape basisSize prec

def readoutPeakShape (basisSize prec : ℕ) : ℕ := 3 * readoutBitShape basisSize prec

def readoutGateShape (basisSize layers prec : ℕ) : ℕ :=
  (basisSize + 1) * (layers + 1) * (prec + 1)

def ReadoutLedger.Covers (led : ReadoutLedger) (P : ReadoutProgram) (r : ReadoutRequest) : Prop :=
  led.gateCount = P.synthWord.length + P.prepareInvWord.length ∧
    led.gcdSteps = P.gcdSteps ∧
    led.forwardAccesses = 1 ∧ led.inverseAccesses = 1 ∧
    ∃ C : ℕ, 1 ≤ C ∧
      led.bitLength ≤ C * readoutBitShape r.basisSize P.prec ∧
      led.gcdSteps ≤ C * readoutGcdShape r.basisSize P.prec ∧
      led.persistentSpace ≤ C * readoutPersistentShape r.basisSize P.prec ∧
      led.peakSpace ≤ C * readoutPeakShape r.basisSize P.prec ∧
      led.gateCount ≤ C * readoutGateShape r.basisSize P.table.layers P.prec

def RationalPayoffTablePrecise : Prop :=
  ∀ (I : Type) [Fintype I] [DecidableEq I] (f : I → ℚ) (k : ℕ),
    (∀ i, 0 ≤ f i ∧ f i ≤ 1) →
    rationalPayoffRotation f k ∈ Matrix.unitaryGroup (I × Bool) ℂ ∧
      (∀ i, 0 ≤ rationalPayoffValue (f i) k ∧ rationalPayoffValue (f i) k ≤ 1 ∧
        |(rationalPayoffValue (f i) k : ℝ) - (f i : ℝ)| ≤ 64 / 2 ^ k) ∧
      ‖rationalPayoffRotation f k - payoffRotation (fun i => (f i : ℝ))‖ ≤ 32 / 2 ^ k

def NativeScalarPrecision : Prop :=
  ∀ (M k : ℕ) (z : Fin M), 0 ≤ nativeAEDecode M k z ∧ nativeAEDecode M k z ≤ 1 ∧
    |(nativeAEDecode M k z : ℝ) - aeEstimate M z| ≤ ((2 : ℝ)⁻¹) ^ k

def ratFloor (x : ℚ) : ℤ := Int.fdiv x.num (x.den : ℤ)

def aeEffRound (x : ℚ) : ℤ := ratFloor (x + 1 / 2)

def aeEffEstimate (M k : ℕ) (z : Fin M) : ℚ := nativeAEDecode M k z

def aeEffCount (N M k : ℕ) (z : Fin M) : ℤ := aeEffRound (N * aeEffEstimate M k z)

noncomputable def effRoundSlack (N k : ℕ) : ℝ := 1 + (N : ℝ) * ((2 : ℝ)⁻¹) ^ k

noncomputable def cor14Width (N : ℕ) (t : ℝ) : ℝ :=
  2 * Real.pi * Real.sqrt (t * ((N : ℝ) - t) / (N : ℝ)) + 11

noncomputable def cor14EffWidth (N k : ℕ) (t : ℝ) : ℝ := cor14Width N t + effRoundSlack N k

def cor14N1Output (S : Finset (Fin 1)) : ℤ := if (0 : Fin 1) ∈ S then 1 else 0

noncomputable def basicApproxCountEffOutput (N : ℕ) (ε : ℝ)
    (ω : (l : Fin (basicApproxCountLoopCap N)) → Fin (2 * 2 ^ l.val))
    (y : Fin (basicApproxCountFinalM ε (basicApproxCountStop N ω))) (k : ℕ) : ℤ :=
  aeEffCount N (basicApproxCountFinalM ε (basicApproxCountStop N ω)) k y

noncomputable def basicApproxCountEffZero {N : ℕ} (hN : 0 < N) (S : Finset (Fin N))
    (ε : ℝ) (ω : (l : Fin (basicApproxCountLoopCap N)) → Fin (2 * 2 ^ l.val))
    (hω : 2 ≤ basicApproxCountFinalM ε (basicApproxCountStop N ω)) (k : ℕ) : ℝ :=
  ∑ y ∈ Finset.univ.filter (fun y : Fin (basicApproxCountFinalM ε (basicApproxCountStop N ω)) =>
      |(basicApproxCountEffOutput N ε ω y k : ℝ)| ≤ effRoundSlack N k),
    (basicApproxCountFinalLaw hN S ε ω hω).prob y

noncomputable def basicApproxCountEffGood {N : ℕ} (hN : 0 < N) (S : Finset (Fin N))
    (ε : ℝ) (ω : (l : Fin (basicApproxCountLoopCap N)) → Fin (2 * 2 ^ l.val))
    (hω : 2 ≤ basicApproxCountFinalM ε (basicApproxCountStop N ω)) (k : ℕ) : ℝ :=
  ∑ y ∈ Finset.univ.filter (fun y : Fin (basicApproxCountFinalM ε (basicApproxCountStop N ω)) =>
      |(basicApproxCountEffOutput N ε ω y k : ℝ) - (S.card : ℝ)| ≤
        ε * (S.card : ℝ) + effRoundSlack N k),
    (basicApproxCountFinalLaw hN S ε ω hω).prob y

noncomputable def exactCountEffFinalMass {N M : ℕ} (hN : 0 < N) (S : Finset (Fin N))
    (hM : 2 ≤ M) (k : ℕ) : ℝ :=
  ∑ y ∈ Finset.univ.filter (fun y : Fin M =>
      |(aeEffCount N M k y : ℝ) - (S.card : ℝ)| ≤ effRoundSlack N k),
    (aeLaw M (QFTMatrix N) (⟨0, hN⟩ : Fin N) S (qftMatrix_unitary hN) hM).prob y

noncomputable def exactCountEffSuccessMass {N : ℕ} (hN : 0 < N) (S : Finset (Fin N))
    (hM₀ : 2 ≤ BHMTTh17.exactCountM₀ N)
    (hM : ∀ z₁ z₂ : Fin (BHMTTh17.exactCountM₀ N),
      2 ≤ BHMTTh17.exactCountGrid N
        ((N : ℝ) * aeEstimate (BHMTTh17.exactCountM₀ N) z₁)
        ((N : ℝ) * aeEstimate (BHMTTh17.exactCountM₀ N) z₂)) (k : ℕ) : ℝ :=
  ∑ z₁ : Fin (BHMTTh17.exactCountM₀ N), ∑ z₂ : Fin (BHMTTh17.exactCountM₀ N),
    ((aeLaw (BHMTTh17.exactCountM₀ N) (QFTMatrix N) (⟨0, hN⟩ : Fin N) S
        (qftMatrix_unitary hN) hM₀).prob z₁) *
      ((aeLaw (BHMTTh17.exactCountM₀ N) (QFTMatrix N) (⟨0, hN⟩ : Fin N) S
        (qftMatrix_unitary hN) hM₀).prob z₂) *
      exactCountEffFinalMass hN S (hM z₁ z₂) k

def effCountBitBudget (N k : ℕ) : ℕ := Nat.clog 2 (N + 1) + k + 8

def effCountSpaceBudget (N k : ℕ) : ℕ := 2 * effCountBitBudget N k + 4

end Qatlib.Concepts.AEMeanReadout.LocalAEBackend
