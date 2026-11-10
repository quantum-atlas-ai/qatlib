/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.QspSimulation.JacobiAnger.ComputedSignalSimulation
import Qatlib.Concepts.GateVocabulary.FiniteGateDescription
import Qatlib.Foundations.PureStateMath.BornBridge.RepresentationBridge
import Qatlib.Concepts.BlockEncoding.EncodingCore.SparseOverlapEncoding
import Qatlib.Concepts.QsvtCore.PhaseExistence.Lc17Support
set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

open Qatlib.Foundations.QueryWordCore.Circuit

open Qatlib.Foundations.BornMetrics.EventProbability
open Qatlib.Concepts.GateVocabulary.FiniteGateDescription
open Qatlib.Concepts.QsvtCore.PhaseExistence

open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.TrotterFormula.SuzukiFourth
open Qatlib.Concepts.PhaseGeometry.RationalCayleyPhase
open Qatlib.Concepts.BlockEncoding.LCU Qatlib.Foundations.PureStateMath.BornBridge
open Qatlib.Concepts.CopyEvolution.Discriminate
open Qatlib.Concepts.QueryWordCore.AdjointCircuits
open Qatlib.Concepts.CoherentSim.CoherentOAA.SignalProcessing
open Qatlib.Concepts.NativeNumerics.PhaseSynthesis
open Qatlib.Concepts.SignalPrimitive.PhaseFrontend
open Qatlib.Concepts.PhaseGeometry.Phase Qatlib.Concepts.QspSimulation.WordModel
open Qatlib.Concepts.BlockEncoding
open Qatlib.Concepts.BlockEncoding.Encoding
open Qatlib.Concepts.BlockEncoding.Postselection.Encoding
open Qatlib.Concepts.OperatorErrors.Robustness.SignalProcessing
open Qatlib.Concepts.NonNormalSpec.ResolventWord

set_option autoImplicit false

namespace Qatlib.Concepts.QspSimulation.Achievability

open Qatlib.Concepts.BlockEncoding Qatlib.Concepts.BlockEncoding.Encoding
open Qatlib.Concepts.BlockEncoding.Postselection.Encoding
open Qatlib.Concepts.QueryWordCore.AdjointCircuits
open Qatlib.Concepts.CoherentSim.CoherentOAA.SignalProcessing
open Qatlib.Concepts.SignalPrimitive.PhaseFrontend Qatlib.Concepts.PhaseGeometry.Phase
open Qatlib.Concepts.QspSimulation.WordModel
open Qatlib.Concepts.OperatorErrors.Robustness.SignalProcessing
open Qatlib.Concepts.NonNormalSpec.ResolventWord
open Qatlib.Concepts.NativeNumerics.PhaseSynthesis
open Matrix
open scoped Classical BigOperators Matrix.Norms.L2Operator

def RepresentsEffectiveReal (t : ℝ) (a : ℕ → ℚ) : Prop :=
  ∀ k : ℕ, |t - (a k : ℝ)| ≤ (1 / 2 : ℝ) ^ k

structure SparseEntry where
  row : ℕ
  col : ℕ
  value : GaussianRat

structure SparseHamiltonianData where
  dim : ℕ
  entries : List SparseEntry
  sparsity : ℕ
  entryNorm : ℕ

noncomputable def sparseDataMatrix (S : SparseHamiltonianData) :
    Matrix (Fin S.dim) (Fin S.dim) ℂ :=
  Matrix.of fun i j =>
    ((S.entries.filter fun e => decide (e.row = i.1 ∧ e.col = j.1)).map
      fun e => gaussianRatComplex e.value).sum

def SparseHamiltonianData.Legal (S : SparseHamiltonianData) : Prop :=
  0 < S.sparsity ∧ 0 < S.entryNorm ∧
    (∀ e ∈ S.entries, e.row < S.dim ∧ e.col < S.dim ∧
      ‖gaussianRatComplex e.value‖ ≤ (S.entryNorm : ℝ)) ∧
    (∀ i : ℕ, i < S.dim →
      (S.entries.filter fun e => decide (e.row = i)).length ≤ S.sparsity) ∧
    (∀ j : ℕ, j < S.dim →
      (S.entries.filter fun e => decide (e.col = j)).length ≤ S.sparsity) ∧
    (sparseDataMatrix S).IsHermitian

structure EffectiveSparseEntry where
  row : ℕ
  col : ℕ
  value : ℕ → ℚ

structure EffectiveSparseHamiltonianData where
  dim : ℕ
  entries : List EffectiveSparseEntry
  sparsity : ℕ
  entryNorm : ℕ

noncomputable def effectiveSparseMatrix (S : EffectiveSparseHamiltonianData)
    (V : EffectiveSparseEntry → ℝ) : Matrix (Fin S.dim) (Fin S.dim) ℂ :=
  Matrix.of fun i j =>
    ((S.entries.filter fun e => decide (e.row = i.1 ∧ e.col = j.1)).map
      fun e => (V e : ℂ)).sum

def quantizedSparseData (S : EffectiveSparseHamiltonianData) (K : ℕ) :
    SparseHamiltonianData where
  dim := S.dim
  entries := S.entries.map fun e => ⟨e.row, e.col, (e.value K, 0)⟩
  sparsity := S.sparsity
  entryNorm := S.entryNorm + 1

noncomputable def fixedWordMatrix (n : ℕ) (W : List FiniteGateCode) :
    Matrix (Reg n) (Reg n) ℂ := (W.map (finiteCodeMatrix n)).reverse.prod

noncomputable def ImplementsWithin (n : ℕ) (W : List FiniteGateCode)
    (V : Matrix (Reg n) (Reg n) ℂ) (η : ℝ) : Prop :=
  finiteWordLegal n W = true ∧ ‖fixedWordMatrix n W - V‖ ≤ η

def cleanEmbed {m h : ℕ} (_hmh : m ≤ h) (x : Reg m) : Reg h :=
  fun i => if hi : i.1 < m then x ⟨i.1, hi⟩ else false

def LoadsFrame {m h : ℕ} (hmh : m ≤ h) (F : Matrix (Reg h) (Reg m) ℂ)
    (VL : Matrix (Reg h) (Reg h) ℂ) : Prop :=
  VL ∈ Matrix.unitaryGroup (Reg h) ℂ ∧
    ∀ x : Reg m, VL *ᵥ Ket (cleanEmbed hmh x) = F *ᵥ Ket x

structure GateLevelSimulation where
  qubitCount : ℕ
  gateWord : List FiniteGateCode
  successWire : ℕ
  bitTime : ℕ

def SimulationLegal (P : GateLevelSimulation) : Prop :=
  finiteWordLegal P.qubitCount P.gateWord = true ∧
    P.successWire < P.qubitCount ∧ P.gateWord.length ≤ P.bitTime

def baseGateCost (P : GateLevelSimulation) : ℕ := P.gateWord.length

def systemRestrict {m n : ℕ} (hmn : m ≤ n) (z : Reg n) : Reg m :=
  fun i => z (Fin.castLE hmn i)

def workZero (m : ℕ) {n : ℕ} (z : Reg n) : Prop :=
  ∀ i : Fin n, m ≤ i.1 → z i = false

def residualZero (m flag : ℕ) {n : ℕ} (z : Reg n) : Prop :=
  ∀ i : Fin n, m ≤ i.1 → i.1 ≠ flag → z i = false

noncomputable def systemInputState {m n : ℕ} (hmn : m ≤ n)
    (ψ : QState (Reg m)) : QState (Reg n) :=
  fun z => if workZero m z then ψ (systemRestrict hmn z) else 0

def simulationSuccessEvent (P : GateLevelSimulation) :
    Finset (Reg P.qubitCount) :=
  if h : P.successWire < P.qubitCount then
    Finset.univ.filter fun z => z ⟨P.successWire, h⟩ = true
  else ∅

noncomputable def simulationRunState (P : GateLevelSimulation)
    (ψ : QState (Reg P.qubitCount)) : QState (Reg P.qubitCount) :=
  Run (1 : Matrix (Reg P.qubitCount) (Reg P.qubitCount) ℂ)
    (finiteCodeCircuit P.qubitCount P.gateWord) ψ

noncomputable def simulationFailureProb (P : GateLevelSimulation)
    (ψ : QState (Reg P.qubitCount)) : ℝ :=
  MeasureProb (simulationRunState P ψ)
    (Finset.univ \ simulationSuccessEvent P)

noncomputable def successSystemVector (P : GateLevelSimulation) (m : ℕ)
    (hmn : m ≤ P.qubitCount) (ψ : QState (Reg m)) : QState (Reg m) :=
  fun x => ∑ z ∈ simulationSuccessEvent P,
    if residualZero m P.successWire z ∧ systemRestrict hmn z = x then
      simulationRunState P (systemInputState hmn ψ) z
    else 0

noncomputable def conditionalSystemState (P : GateLevelSimulation) (m : ℕ)
    (hmn : m ≤ P.qubitCount) (ψ : QState (Reg m)) : QState (Reg m) :=
  (‖toEuclidean_fromVec (successSystemVector P m hmn ψ)‖)⁻¹ •
    successSystemVector P m hmn ψ

def perturbationBudget (P : GateLevelSimulation) (η : ℝ) : ℝ :=
  ((P.gateWord.length : ℝ) + 1) * η

def identityFlagProgram (m : ℕ) : GateLevelSimulation where
  qubitCount := m + 1
  gateWord := [FiniteGateCode.x m]
  successWire := m
  bitTime := 1

structure PhaseInversionCost where
  refinementSteps : ℕ
  coefficientVisits : ℕ
  ringOperations : ℕ
  responseRounds : ℕ

structure PhaseInversionOutput where
  value : Option PhaseData
  cost : PhaseInversionCost

abbrev PhaseInversionProgram := List ℚ → ℕ → ℚ → PhaseInversionOutput

def phaseInversionCostBound (d k : ℕ) : ℕ := 64 * (d + 1) ^ 6 * (k + 2) ^ 4

def PhaseInversionLegal (p : List ℚ) (d : ℕ) (eps : ℚ) : Prop :=
  0 < eps ∧ (realTarget p).degree ≤ (d : WithBot ℕ) ∧
    Qatlib.Concepts.QspSimulation.Achievability.HasRealParity d (realTarget p) ∧
    ∀ x ∈ Set.Icc (-1 : ℝ) 1, |(realTarget p).eval x| ≤ 1

def PhaseInversionCertified (prog : PhaseInversionProgram)
    (p : List ℚ) (d : ℕ) (eps : ℚ) : Prop :=
  ∃ data : PhaseData,
    (prog p d eps).value = some data ∧
      data.phases.length = d ∧
      ‖gaussianRatComplex data.base‖ = 1 ∧
      (∀ z ∈ data.phases, ‖gaussianRatComplex z‖ = 1) ∧
      (scoreData p d data).1.1 ≤ (1 / 2 : ℚ) ^ phaseToleranceBits eps ∧
      (∀ x ∈ Set.Icc (-1 : ℝ) 1,
        |((responseP (gaussianRatComplex data.base)
            (data.phases.map gaussianRatComplex)).eval (x : ℂ)).re -
          (realTarget p).eval x| ≤ (eps : ℝ)) ∧
      d + 1 ≤ (prog p d eps).cost.coefficientVisits ∧
      d ≤ (prog p d eps).cost.responseRounds ∧
      (prog p d eps).cost.refinementSteps ≤
        phaseInversionCostBound d (phaseToleranceBits eps) ∧
      (prog p d eps).cost.coefficientVisits ≤
        phaseInversionCostBound d (phaseToleranceBits eps) ∧
      (prog p d eps).cost.ringOperations ≤
        phaseInversionCostBound d (phaseToleranceBits eps) ∧
      (prog p d eps).cost.responseRounds ≤
        phaseInversionCostBound d (phaseToleranceBits eps)

def inputCoefficientGap (p q : List ℚ) (d : ℕ) : ℚ :=
  ∑ i ∈ Finset.range (d + 1), |p.getD i 0 - q.getD i 0|

end Qatlib.Concepts.QspSimulation.Achievability
