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

/-!
# Data and specifications for gate-level QSP simulation

This module defines the data and semantic interfaces used to state concrete
Hamiltonian-simulation guarantees. `SparseHamiltonianData` and `EffectiveSparseHamiltonianData`
represent finite sparse inputs, while `RepresentsEffectiveReal` gives a dyadic rational
approximation contract. `GateLevelSimulation` records a finite gate word, a success flag, and a
time budget; its behavior is expressed through `simulationFailureProb`, `successSystemVector`,
and `conditionalSystemState`. These interfaces support the QSP simulation framework of
[LowChuang2017] and the projected-encoding viewpoint of [GilyenSuLowWiebe2019].

`PhaseInversionLegal` specifies bounded real target polynomials with the required degree and
parity. `PhaseInversionCertified` combines returned rational phase data, uniform approximation,
coefficient-score control, and bounds on the program's recorded operation counts.

## Main statements

* `SparseHamiltonianData.Legal` requires valid coordinates, entry bounds, row and column
  sparsity, and Hermiticity.
* `ImplementsWithin` combines gate-word legality with an operator-norm approximation bound.
* `LoadsFrame` specifies a unitary loader on cleanly embedded basis states.
* `SimulationLegal` checks the finite gate word, flag index, and declared time budget.
* `PhaseInversionCertified` states phase validity, approximation accuracy, and the cost-record
  bounds.

## References

* [Low and Chuang, 2017][LowChuang2017]
* [Gilyén, Su, Low, and Wiebe, 2019][GilyenSuLowWiebe2019]
-/

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

/-- A rational sequence represents a real number when its `k`th value has absolute error at most
`2⁻ᵏ` for every natural precision index. -/
def RepresentsEffectiveReal (t : ℝ) (a : ℕ → ℚ) : Prop :=
  ∀ k : ℕ, |t - (a k : ℝ)| ≤ (1 / 2 : ℝ) ^ k

/-- A sparse matrix entry described by natural row and column indices and a Gaussian-rational
value. -/
structure SparseEntry where
  row : ℕ
  col : ℕ
  value : GaussianRat

/-- Finite sparse Hamiltonian input data consisting of a dimension, an entry list, and declared
sparsity and entry-norm bounds. -/
structure SparseHamiltonianData where
  dim : ℕ
  entries : List SparseEntry
  sparsity : ℕ
  entryNorm : ℕ

/-- Interprets sparse data as a complex matrix by summing the values of all listed entries at
each coordinate. -/
noncomputable def sparseDataMatrix (S : SparseHamiltonianData) :
    Matrix (Fin S.dim) (Fin S.dim) ℂ :=
  Matrix.of fun i j =>
    ((S.entries.filter fun e => decide (e.row = i.1 ∧ e.col = j.1)).map
      fun e => gaussianRatComplex e.value).sum

/-- Requires positive declared bounds, valid entry coordinates, bounded entry values, bounded
row and column list lengths, and a Hermitian interpreted matrix. -/
def SparseHamiltonianData.Legal (S : SparseHamiltonianData) : Prop :=
  0 < S.sparsity ∧ 0 < S.entryNorm ∧
    (∀ e ∈ S.entries, e.row < S.dim ∧ e.col < S.dim ∧
      ‖gaussianRatComplex e.value‖ ≤ (S.entryNorm : ℝ)) ∧
    (∀ i : ℕ, i < S.dim →
      (S.entries.filter fun e => decide (e.row = i)).length ≤ S.sparsity) ∧
    (∀ j : ℕ, j < S.dim →
      (S.entries.filter fun e => decide (e.col = j)).length ≤ S.sparsity) ∧
    (sparseDataMatrix S).IsHermitian

/-- A sparse entry with natural row and column indices and a rational value available at each
natural precision index. -/
structure EffectiveSparseEntry where
  row : ℕ
  col : ℕ
  value : ℕ → ℚ

/-- Sparse input data whose entry values are rational approximation sequences, together with a
dimension and declared sparsity and norm bounds. -/
structure EffectiveSparseHamiltonianData where
  dim : ℕ
  entries : List EffectiveSparseEntry
  sparsity : ℕ
  entryNorm : ℕ

/-- Builds a complex matrix by summing the supplied real interpretation of every listed entry at
each coordinate. -/
noncomputable def effectiveSparseMatrix (S : EffectiveSparseHamiltonianData)
    (V : EffectiveSparseEntry → ℝ) : Matrix (Fin S.dim) (Fin S.dim) ℂ :=
  Matrix.of fun i j =>
    ((S.entries.filter fun e => decide (e.row = i.1 ∧ e.col = j.1)).map
      fun e => (V e : ℂ)).sum

/-- Samples each effective entry at precision `K`, uses zero imaginary part, and increases the
declared entry-norm bound by one. -/
def quantizedSparseData (S : EffectiveSparseHamiltonianData) (K : ℕ) :
    SparseHamiltonianData where
  dim := S.dim
  entries := S.entries.map fun e => ⟨e.row, e.col, (e.value K, 0)⟩
  sparsity := S.sparsity
  entryNorm := S.entryNorm + 1

/-- The matrix of a finite gate word, obtained by multiplying its gate matrices in reverse list
order. -/
noncomputable def fixedWordMatrix (n : ℕ) (W : List FiniteGateCode) :
    Matrix (Reg n) (Reg n) ℂ := (W.map (finiteCodeMatrix n)).reverse.prod

/-- A finite gate word implements `V` within `η` when the word is legal and its matrix differs
from `V` by at most `η` in operator norm. -/
noncomputable def ImplementsWithin (n : ℕ) (W : List FiniteGateCode)
    (V : Matrix (Reg n) (Reg n) ℂ) (η : ℝ) : Prop :=
  finiteWordLegal n W = true ∧ ‖fixedWordMatrix n W - V‖ ≤ η

/-- Embeds a system basis register into a larger register by copying its initial bits and
setting all remaining bits to false. -/
def cleanEmbed {m h : ℕ} (_hmh : m ≤ h) (x : Reg m) : Reg h :=
  fun i => if hi : i.1 < m then x ⟨i.1, hi⟩ else false

/-- A frame loader is unitary and maps each cleanly embedded system basis vector to the
corresponding column of the frame `F`. -/
def LoadsFrame {m h : ℕ} (hmh : m ≤ h) (F : Matrix (Reg h) (Reg m) ℂ)
    (VL : Matrix (Reg h) (Reg h) ℂ) : Prop :=
  VL ∈ Matrix.unitaryGroup (Reg h) ℂ ∧
    ∀ x : Reg m, VL *ᵥ Ket (cleanEmbed hmh x) = F *ᵥ Ket x

/-- A finite simulation description recording the qubit count, gate word, designated success
wire, and bit-time budget. -/
structure GateLevelSimulation where
  qubitCount : ℕ
  gateWord : List FiniteGateCode
  successWire : ℕ
  bitTime : ℕ

/-- Requires a legal finite gate word, an in-range success wire, and gate-word length no larger
than the declared bit-time budget. -/
def SimulationLegal (P : GateLevelSimulation) : Prop :=
  finiteWordLegal P.qubitCount P.gateWord = true ∧
    P.successWire < P.qubitCount ∧ P.gateWord.length ≤ P.bitTime

/-- The base gate cost of a simulation is the length of its finite gate word. -/
def baseGateCost (P : GateLevelSimulation) : ℕ := P.gateWord.length

/-- Restricts a larger register to its first `m` bits using the given dimension inequality. -/
def systemRestrict {m n : ℕ} (hmn : m ≤ n) (z : Reg n) : Reg m :=
  fun i => z (Fin.castLE hmn i)

/-- All register bits at positions at least `m` are false. -/
def workZero (m : ℕ) {n : ℕ} (z : Reg n) : Prop :=
  ∀ i : Fin n, m ≤ i.1 → z i = false

/-- All register bits at positions at least `m`, except the designated flag, are false. -/
def residualZero (m flag : ℕ) {n : ℕ} (z : Reg n) : Prop :=
  ∀ i : Fin n, m ≤ i.1 → i.1 ≠ flag → z i = false

/-- Extends a system state to a larger register with zero work bits, assigning zero amplitude to
every other basis register. -/
noncomputable def systemInputState {m n : ℕ} (hmn : m ≤ n)
    (ψ : QState (Reg m)) : QState (Reg n) :=
  fun z => if workZero m z then ψ (systemRestrict hmn z) else 0

/-- The success event consists of basis registers whose designated flag is true; an out-of-range
flag gives the empty event. -/
def simulationSuccessEvent (P : GateLevelSimulation) :
    Finset (Reg P.qubitCount) :=
  if h : P.successWire < P.qubitCount then
    Finset.univ.filter fun z => z ⟨P.successWire, h⟩ = true
  else ∅

/-- Executes the simulation's finite gate circuit on the supplied full-register state. -/
noncomputable def simulationRunState (P : GateLevelSimulation)
    (ψ : QState (Reg P.qubitCount)) : QState (Reg P.qubitCount) :=
  Run (1 : Matrix (Reg P.qubitCount) (Reg P.qubitCount) ℂ)
    (finiteCodeCircuit P.qubitCount P.gateWord) ψ

/-- The Born probability of the complement of the success event after execution of the
simulation. -/
noncomputable def simulationFailureProb (P : GateLevelSimulation)
    (ψ : QState (Reg P.qubitCount)) : ℝ :=
  MeasureProb (simulationRunState P ψ)
    (Finset.univ \ simulationSuccessEvent P)

/-- Extracts system amplitudes from successful output registers with all residual work bits
zero, starting from a cleanly embedded input. -/
noncomputable def successSystemVector (P : GateLevelSimulation) (m : ℕ)
    (hmn : m ≤ P.qubitCount) (ψ : QState (Reg m)) : QState (Reg m) :=
  fun x => ∑ z ∈ simulationSuccessEvent P,
    if residualZero m P.successWire z ∧ systemRestrict hmn z = x then
      simulationRunState P (systemInputState hmn ψ) z
    else 0

/-- Scales the extracted successful system vector by the reciprocal of its Euclidean norm. -/
noncomputable def conditionalSystemState (P : GateLevelSimulation) (m : ℕ)
    (hmn : m ≤ P.qubitCount) (ψ : QState (Reg m)) : QState (Reg m) :=
  (‖toEuclidean_fromVec (successSystemVector P m hmn ψ)‖)⁻¹ •
    successSystemVector P m hmn ψ

/-- Assigns the perturbation budget `(gateWord.length + 1) * η` to a simulation and per-step
error scale. -/
def perturbationBudget (P : GateLevelSimulation) (η : ℝ) : ℝ :=
  ((P.gateWord.length : ℝ) + 1) * η

/-- A simulation with one extra qubit and one X gate that sets its designated success flag, with
bit-time budget one. -/
def identityFlagProgram (m : ℕ) : GateLevelSimulation where
  qubitCount := m + 1
  gateWord := [FiniteGateCode.x m]
  successWire := m
  bitTime := 1

/-- Recorded counts of refinement steps, coefficient visits, ring operations, and response
rounds for phase inversion. -/
structure PhaseInversionCost where
  refinementSteps : ℕ
  coefficientVisits : ℕ
  ringOperations : ℕ
  responseRounds : ℕ

/-- An optional rational phase packet paired with its recorded phase-inversion cost. -/
structure PhaseInversionOutput where
  value : Option PhaseData
  cost : PhaseInversionCost

/-- A phase-inversion program maps rational target coefficients, a degree, and a rational
tolerance to an output packet and cost record. -/
abbrev PhaseInversionProgram := List ℚ → ℕ → ℚ → PhaseInversionOutput

/-- The explicit recorded-cost bound `64 * (d + 1)^6 * (k + 2)^4` for degree `d` and precision
index `k`. -/
def phaseInversionCostBound (d k : ℕ) : ℕ := 64 * (d + 1) ^ 6 * (k + 2) ^ 4

/-- A legal input has positive tolerance and a real target polynomial of degree at most `d`,
parity prescribed by `d`, and absolute value at most one on `[-1, 1]`. -/
def PhaseInversionLegal (p : List ℚ) (d : ℕ) (eps : ℚ) : Prop :=
  0 < eps ∧ (realTarget p).degree ≤ (d : WithBot ℕ) ∧
    Qatlib.Concepts.QspSimulation.Achievability.HasRealParity d (realTarget p) ∧
    ∀ x ∈ Set.Icc (-1 : ℝ) 1, |(realTarget p).eval x| ≤ 1

/-- Certifies returned unit-modulus rational phase data of length `d`, coefficient-score and
uniform-error bounds, and lower and upper bounds on the recorded costs. -/
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

/-- The sum of absolute coefficient differences through degree `d`, interpreting missing
coefficients as zero. -/
def inputCoefficientGap (p q : List ℚ) (d : ℕ) : ℚ :=
  ∑ i ∈ Finset.range (d + 1), |p.getD i 0 - q.getD i 0|

end Qatlib.Concepts.QspSimulation.Achievability
