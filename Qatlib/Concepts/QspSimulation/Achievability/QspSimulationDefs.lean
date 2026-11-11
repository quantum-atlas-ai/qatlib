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

/-!
# QSP simulation parameters and resource ledgers

This module defines Jacobi–Anger approximation parameters and records the work performed by
finite phase synthesis. `honestPhaseRun` retains the backend counters, while
`sparseSimulationWord` and `sparseSimulationLedger` package the resulting circuit and its
resource counts. The approximation parameters follow the QSP simulation setting of
[LowChuang2017].

`EffectiveValueBound` and `EffectiveSparseLegal` express dyadic approximation accuracy, entry
bounds, and row and column sparsity for effective Hamiltonian data. The module also defines the
corresponding quantization error budgets.

## Main statements

* `JaDomain`: The parameter domain τ ≥ 0 and ε > 0.
* `honestPhaseRun`: A finite phase synthesis result together with its measured counters.
* `sparseSimulationLedger`: Circuit counts and phase search information for the compiled word.

## References

* [Low and Chuang, 2017][LowChuang2017]
-/

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

/-- The parameter condition τ ≥ 0 and ε > 0 for Jacobi–Anger approximation. -/
def JaDomain (τ ε : ℝ) : Prop := 0 ≤ τ ∧ 0 < ε

/-- The requested accuracy capped at one, min(ε, 1). -/
noncomputable def jaAccuracy (ε : ℝ) : ℝ := min ε 1

/-- The corrected Jacobi–Anger truncation count for τ and the capped accuracy `jaAccuracy ε`. -/
noncomputable def jaCount (τ ε : ℝ) : ℕ := lcCorrectedQ τ (jaAccuracy ε)

/-- The real-valued degree scale τ + 1 + L/log(1 + L/max(τ, 1)), where L = log(32/min(ε, 1)). -/
noncomputable def jaIdealShape (τ ε : ℝ) : ℝ :=
  τ + 1 + Real.log (32 / min ε 1) /
    Real.log (1 + Real.log (32 / min ε 1) / max τ 1)

/-- The complex norm error of the response built from A and Qt at angle θ relative to exp(−iτ
sin θ). -/
noncomputable def jaError (A Qt : Polynomial ℝ) (τ θ : ℝ) : ℝ :=
  ‖((realEval A (Complex.ofReal (Real.cos (θ / 2))))
      + Complex.I * ((Real.sin (θ / 2) : ℝ) : ℂ) *
        (realEval Qt (Complex.ofReal (Real.cos (θ / 2))))
      - Complex.exp (Complex.I * (-(τ : ℂ) * (Real.sin θ : ℂ))))‖

/-- The logarithmic accuracy budget log(32/`jaAccuracy ε`). -/
noncomputable def jaLogBudget (ε : ℝ) : ℝ := Real.log (32 / jaAccuracy ε)

/-- Counters for tested phase words, coefficient visits, response rounds, backend calls, and
table multiplications in a phase synthesis run. -/
structure PhaseRunLedger where
  testedWords : ℕ
  coefficientVisits : ℕ
  responseRounds : ℕ
  backendCalls : ℕ
  tableMultiplications : ℕ

/-- An optional phase synthesis result together with the work counters stored in a
`PhaseRunLedger`. -/
structure PhaseRunOutput where
  value : Option PhaseData
  ledger : PhaseRunLedger

/-- Run `finitePhaseSynthesis` on the rational coefficient list and retain its optional phase
data and all recorded work counters. -/
def honestPhaseRun (p : List ℚ) (d : ℕ) (eps : ℚ) : PhaseRunOutput :=
  let r := finitePhaseSynthesis p d eps
  { value := r.value
    ledger :=
      { testedWords := r.tested
        coefficientVisits := r.coefficientVisits
        responseRounds := r.responseRounds
        backendCalls := r.backendCalls
        tableMultiplications := r.tableMultiplications } }

/-- The number of words of length d + 1 over a phase grid of size 2 raised to `phaseGridBits d
k`. -/
noncomputable def phaseSearchWords (d k : ℕ) : ℕ := (2 ^ phaseGridBits d k) ^ (d + 1)

/-- The condition that the rational approximation a(k) lies within 2^(−k) of the real value V
for every natural k. -/
def EffectiveValueBound (V : ℝ) (a : ℕ → ℚ) : Prop :=
  ∀ k : ℕ, |V - (a k : ℝ)| ≤ (1 / 2 : ℝ) ^ k

/-- The condition that effective sparse data have positive sparsity and entry norm, dyadically
accurate entry values bounded by the entry norm, and at most the prescribed number of
entries in each row and column. -/
def EffectiveSparseLegal (S : EffectiveSparseHamiltonianData)
    (V : EffectiveSparseEntry → ℝ) : Prop :=
  0 < S.sparsity ∧ 0 < S.entryNorm ∧
    (∀ e ∈ S.entries, EffectiveValueBound (V e) e.value) ∧
    (∀ e ∈ S.entries, |V e| ≤ (S.entryNorm : ℝ)) ∧
    (∀ o : Fin S.dim, (S.entries.filter fun e => e.row = o.1).length ≤ S.sparsity) ∧
    (∀ i : Fin S.dim, (S.entries.filter fun e => e.col = i.1).length ≤ S.sparsity)

/-- The error budget 2s² · 2^(−K), where s is the sparsity recorded in S. -/
noncomputable def quantizationErrorBound (S : EffectiveSparseHamiltonianData)
    (K : ℕ) : ℝ :=
  2 * (S.sparsity : ℝ) ^ 2 * (1 / 2 : ℝ) ^ K

/-- The dyadic entry error budget 2^(−K). -/
noncomputable def entryQuantizationError (K : ℕ) : ℝ := (1 / 2 : ℝ) ^ K

/-- The qubit count 2 + `Nat.log2 dim` + 1 used for the hosting space. -/
noncomputable def hostingQubits (dim : ℕ) : ℕ := 2 + Nat.log2 dim + 1

/-- Compile a Hamiltonian word using the phase data returned by `honestPhaseRun` for both
response branches, or return the empty word if synthesis returns no data. -/
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

/-- A record of hosting qubits, oracle queries, macro gates, target error, phase search word
count, and phase coefficient visits. -/
structure SparseSimulationLedger where
  qubits : ℕ
  oracleQueries : ℕ
  macroGates : ℕ
  targetError : ℝ
  phaseSearchWords : ℕ
  phaseCoefficientVisits : ℕ

/-- Build a resource ledger from `sparseSimulationWord`, the hosting dimension, the requested
target error, and the phase synthesis counters. -/
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
