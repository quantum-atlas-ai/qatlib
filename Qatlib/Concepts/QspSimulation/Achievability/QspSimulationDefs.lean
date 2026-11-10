/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.QspSimulation.Achievability.SimQsp
import Qatlib.Concepts.NativeNumerics.PhaseSynthesis.FinitePhaseSynthesis
import Qatlib.Concepts.BlockEncoding.EncodingCore.SparseOverlapEncoding
import Qatlib.Concepts.BlockEncoding.Basic
import Qatlib.Concepts.QspSimulation.Achievability.CountedHamiltonian
set_option warningAsError false
set_option backward.isDefEq.respectTransparency false
open Qatlib.Concepts.CoherentSim.CoherentOAA
open Qatlib.Foundations.InstrumentCore.ProjectiveMeasurementLaws
open Qatlib.Foundations.OperatorErrors.OperatorError
open Qatlib.Concepts.NativeNumerics.PhaseSynthesis
open Qatlib.Concepts.TrotterFormula.SuzukiFourth
open Qatlib.Concepts.QspSimulation.Achievability
open Qatlib.Concepts.PhaseGeometry.RationalCayleyPhase
open Qatlib.Concepts.BlockEncoding
open Qatlib.Concepts.QsvtCore.PhaseExistence

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000
set_option maxRecDepth 4096

noncomputable section

namespace Qatlib.Concepts.QspSimulation.Achievability

open Matrix
open Polynomial
open Qatlib
open scoped Classical BigOperators Matrix.Norms.L2Operator

def JaDomain (τ ε : ℝ) : Prop := 0 ≤ τ ∧ 0 < ε

noncomputable def jaAccuracy (ε : ℝ) : ℝ := min ε 1

noncomputable def jaCount (τ ε : ℝ) : ℕ := lcCorrectedQ τ (jaAccuracy ε)

noncomputable def jaIdealShape (τ ε : ℝ) : ℝ :=
  τ + 1 + Real.log (32 / min ε 1) /
    Real.log (1 + Real.log (32 / min ε 1) / max τ 1)

noncomputable def jaError (A Qt : Polynomial ℝ) (τ θ : ℝ) : ℝ :=
  ‖((realEval A (Complex.ofReal (Real.cos (θ / 2))))
      + Complex.I * ((Real.sin (θ / 2) : ℝ) : ℂ) *
        (realEval Qt (Complex.ofReal (Real.cos (θ / 2))))
      - Complex.exp (Complex.I * (-(τ : ℂ) * (Real.sin θ : ℂ))))‖

noncomputable def jaLogBudget (ε : ℝ) : ℝ := Real.log (32 / jaAccuracy ε)

structure PhaseRunLedger where
  testedWords : ℕ
  coefficientVisits : ℕ
  responseRounds : ℕ
  backendCalls : ℕ
  tableMultiplications : ℕ

structure PhaseRunOutput where
  value : Option PhaseData
  ledger : PhaseRunLedger

def honestPhaseRun (p : List ℚ) (d : ℕ) (eps : ℚ) : PhaseRunOutput :=
  let r := finitePhaseSynthesis p d eps
  { value := r.value
    ledger :=
      { testedWords := r.tested
        coefficientVisits := r.coefficientVisits
        responseRounds := r.responseRounds
        backendCalls := r.backendCalls
        tableMultiplications := r.tableMultiplications } }

noncomputable def phaseSearchWords (d k : ℕ) : ℕ := (2 ^ phaseGridBits d k) ^ (d + 1)

def EffectiveValueBound (V : ℝ) (a : ℕ → ℚ) : Prop :=
  ∀ k : ℕ, |V - (a k : ℝ)| ≤ (1 / 2 : ℝ) ^ k

def EffectiveSparseLegal (S : EffectiveSparseHamiltonianData)
    (V : EffectiveSparseEntry → ℝ) : Prop :=
  0 < S.sparsity ∧ 0 < S.entryNorm ∧
    (∀ e ∈ S.entries, EffectiveValueBound (V e) e.value) ∧
    (∀ e ∈ S.entries, |V e| ≤ (S.entryNorm : ℝ)) ∧
    (∀ o : Fin S.dim, (S.entries.filter fun e => e.row = o.1).length ≤ S.sparsity) ∧
    (∀ i : Fin S.dim, (S.entries.filter fun e => e.col = i.1).length ≤ S.sparsity)

noncomputable def quantizationErrorBound (S : EffectiveSparseHamiltonianData)
    (K : ℕ) : ℝ :=
  2 * (S.sparsity : ℝ) ^ 2 * (1 / 2 : ℝ) ^ K

noncomputable def entryQuantizationError (K : ℕ) : ℝ := (1 / 2 : ℝ) ^ K

noncomputable def hostingQubits (dim : ℕ) : ℕ := 2 + Nat.log2 dim + 1

noncomputable def sparseSimulationWord {H I : Type} [Fintype H] [DecidableEq H]
    [Fintype I] [DecidableEq I] (F : Matrix H I ℂ) (p : List ℚ) (d : ℕ) (eps : ℚ) :
    List (AdjointStep (Bool × (Bool × H))) :=
  match (honestPhaseRun p d eps).value with
  | some data =>
      compileHamiltonian F (gaussianRatComplex data.base)
        (data.phases.map gaussianRatComplex)
        (gaussianRatComplex data.base)
        (data.phases.map gaussianRatComplex)
  | none => []

structure SparseSimulationLedger where
  qubits : ℕ
  oracleQueries : ℕ
  macroGates : ℕ
  targetError : ℝ
  phaseSearchWords : ℕ
  phaseCoefficientVisits : ℕ

noncomputable def sparseSimulationLedger {H I : Type} [Fintype H] [DecidableEq H]
    [Fintype I] [DecidableEq I] (F : Matrix H I ℂ) (p : List ℚ) (d : ℕ) (eps : ℚ)
    (targetError : ℝ) : SparseSimulationLedger :=
  let w := sparseSimulationWord F p d eps
  { qubits := hostingQubits (Fintype.card H)
    oracleQueries := adjointQueryCount w
    macroGates := adjointGateCount w
    targetError := targetError
    phaseSearchWords := phaseSearchWords d (phaseToleranceBits eps)
    phaseCoefficientVisits := (honestPhaseRun p d eps).ledger.coefficientVisits }

end Qatlib.Concepts.QspSimulation.Achievability
