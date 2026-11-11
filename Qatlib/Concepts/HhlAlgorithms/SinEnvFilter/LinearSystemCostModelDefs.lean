/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.HhlAlgorithms.SinEnvProgram.QlsHhlDefs
import Qatlib.Concepts.HhlAlgorithms.UniformHHL.UniformHHLFilter

/-!
# HHL cost models and backend specifications

This module defines phase-estimation budget expressions, backend resource ledgers, finite-gate
access records, and fresh-retry schedules for the HHL setting of [HarrowHassidimLloyd2009]. The
associated predicates state circuit legality, sparse-synthesis certificates, budget consistency,
and componentwise matrix quantization requirements.

`quantizeReal` uses a natural-number floor, while `FreshRetrySchedule` records the product
failure expression and linear total cost of repeated fresh trials.

## Main statements

* `NumericBackendLedger.Complete`: consistency and resource conditions for a numeric ledger.
* `HamiltonianBackend.Complete`: sparse-access and synthesis certification.
* `freshRetryIsNotAmplification`: the stated independent-trial cost and failure formulas.
* `SystemDecomputation.Complete`: strict componentwise matrix quantization bounds.

## References

* [Harrow et al., 2009][HarrowHassidimLloyd2009]
-/

set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

open Qatlib.Concepts.HhlAlgorithms.SinEnvProgram.SinEnvelopeHHLConsumers
open Qatlib.Concepts.LinearLearning.ConcisePipeline

open Qatlib.Concepts.CoherentSim.CoherentOAA
open Qatlib.Foundations.InstrumentCore.ProjectiveMeasurementLaws
open Qatlib.Foundations.OperatorErrors.OperatorError
open Qatlib.Foundations.BornMetrics.EventProbability
open Qatlib.Concepts.GateVocabulary.FiniteGateDescription
open Qatlib.Concepts.QspSimulation.Achievability
open Qatlib.Concepts.HhlAlgorithms.Postselection
open Qatlib.Concepts.HhlAlgorithms.SinEnvProgram
open Qatlib.Concepts.HhlAlgorithms.UniformHHL
open Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw

open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.QueryWordCore.AdjointCircuits
open Qatlib.Concepts.CoherentSim.CoherentOAA.SignalProcessing
open Qatlib.Concepts.SignalPrimitive.PhaseFrontend
open Qatlib.Concepts.PhaseGeometry.Phase Qatlib.Concepts.QspSimulation.WordModel
open Qatlib.Concepts.HhlAlgorithms.Postselection.SignalProcessing
open Qatlib.Concepts.HhlAlgorithms.SinEnvFilter
open Qatlib.Concepts.OperatorErrors.Robustness.SignalProcessing
open Qatlib.Concepts.NonNormalSpec.ResolventWord

set_option autoImplicit false
set_option linter.unusedVariables false

namespace Qatlib.Concepts.HhlAlgorithms.SinEnvFilter

open Matrix Qatlib.Concepts.HhlAlgorithms.SinEnvFilter
open Qatlib.Concepts.QueryWordCore.AdjointCircuits
open Qatlib.Concepts.CoherentSim.CoherentOAA.SignalProcessing
open Qatlib.Concepts.SignalPrimitive.PhaseFrontend Qatlib.Concepts.PhaseGeometry.Phase
open Qatlib.Concepts.QspSimulation.WordModel
open Qatlib.Concepts.HhlAlgorithms.Postselection.SignalProcessing
open Qatlib.Concepts.OperatorErrors.Robustness.SignalProcessing
open Qatlib.Concepts.NonNormalSpec.ResolventWord
open scoped Classical BigOperators

/-- The sine-envelope phase-estimation budget `21 / (d * η)`. -/
noncomputable def sinEnvelopeFirstPowerBudget (d η : ℝ) : ℝ := 21 / (d * η)

/-- The uniform phase-estimation grid budget `4096 / (d^2 * η^4)`. -/
noncomputable def uniformQPEGridBudget (d η : ℝ) : ℝ := 4096 / (d ^ 2 * η ^ 4)

/-- The condition-number and precision budget `21 * κ / ε`. -/
noncomputable def nearOptimalKappaEpsBudget (κ ε : ℝ) : ℝ := 21 * κ / ε

/-- A record of a three-state filter's gap, target error, and phase-grid size. -/
structure SinThreeStateFilter where

  d : ℝ

  eta : ℝ

  grid : ℕ

/-- The positive gap and error ranges together with the requirement that the grid covers
`sinEnvelopeFirstPowerBudget`. -/
def SinThreeStateFilter.Budgeted (f : SinThreeStateFilter) : Prop :=
  0 < f.d ∧ f.d ≤ 1 / 4 ∧ 0 < f.eta ∧ f.eta ≤ 1 ∧
    sinEnvelopeFirstPowerBudget f.d f.eta ≤ f.grid

/-- The rational dyadic value obtained by applying the natural-number floor to `2^k * t` and
dividing by `2^k`. -/
noncomputable def quantizeReal (k : ℕ) (t : ℝ) : ℚ :=
  ((Nat.floor ((2 : ℝ) ^ k * t) : ℤ) : ℚ) / ((2 ^ k : ℕ) : ℚ)

/-- The complex value formed by applying `quantizeReal` separately to the real and imaginary
parts. -/
noncomputable def quantizeComplex (k : ℕ) (z : ℂ) : ℂ :=
  ((quantizeReal k z.re : ℚ) : ℂ) + ((quantizeReal k z.im : ℚ) : ℂ) * Complex.I

/-- The scaled block dilation `qlsScaledDilation A` of a possibly rectangular matrix. -/
noncomputable def nonHermitianDilation {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℂ) :
    Matrix (Fin m ⊕ Fin n) (Fin m ⊕ Fin n) ℂ :=
  qlsScaledDilation A

/-- A ledger of phase-grid, rotation, synthesis, dilation, quantization, gate, bit-time, and
peak-space counts. -/
structure NumericBackendLedger where

  phaseGrid : ℕ

  filterRotations : ℕ

  synthCalls : ℕ

  synthGates : ℕ

  dilationWires : ℕ

  quantDigits : ℕ

  gateCount : ℕ

  bitTime : ℕ

  peakSpace : ℕ

/-- The filter-budget condition and the stated consistency and resource inequalities for a
numeric backend ledger. -/
def NumericBackendLedger.Complete (L : NumericBackendLedger)
    (f : SinThreeStateFilter) : Prop :=
  f.Budgeted ∧
    L.phaseGrid = f.grid ∧
    L.filterRotations ≤ L.gateCount ∧
    L.synthCalls * L.synthGates ≤ L.gateCount ∧
    L.gateCount ≤ L.bitTime ∧
    1 + L.dilationWires ≤ L.peakSpace ∧
    0 < L.quantDigits

/-- A finite-gate backend record containing register size, word, bit-time budget, and peak-space
budget. -/
structure IntegerBitBackend where

  wires : ℕ

  word : List FiniteGateCode

  bitTime : ℕ

  peakSpace : ℕ

/-- Legality of the finite-gate word together with word-length and register-size bounds by bit
time and peak space. -/
def IntegerBitBackend.Legal (B : IntegerBitBackend) : Prop :=
  finiteWordLegal B.wires B.word = true ∧
    B.word.length ≤ B.bitTime ∧
    B.wires ≤ B.peakSpace

/-- The existence of a common polynomial bound in `wires + 1` for the recorded bit time and peak
space. -/
def IntegerBitBackend.PolyBounded (B : IntegerBitBackend) : Prop :=
  ∃ (c e : ℕ), B.bitTime ≤ c * (B.wires + 1) ^ e ∧ B.peakSpace ≤ c * (B.wires + 1) ^ e

/-- A sparse Hamiltonian backend with access data, sparsity, synthesis, spectral certificate,
and precision. -/
structure HamiltonianBackend where

  access : SparseAccessSystem

  sparsity : ℕ

  synthesis : SparseHamiltonianSynthesis access

  certEig : Fin access.dim → ℝ

  certV : Operator access.dim

  precision : ℕ

/-- The sparse-access legality, unitary spectral certificate, synthesis-implementation, and
synthesis-budget conditions for a Hamiltonian backend. -/
def HamiltonianBackend.Complete (B : HamiltonianBackend) : Prop :=
  B.access.Legal B.sparsity ∧
    B.certV ∈ Matrix.unitaryGroup (Fin B.access.dim) ℂ ∧
    continuousHHLMatrix B.certEig B.certV = B.access.data.matrix ∧
    SparseHamiltonianSynthesis.ImplementsAt B.access B.synthesis
      B.certEig B.certV B.precision ∧
    SparseHamiltonianSynthesis.BudgetBounded B.access B.synthesis
      B.sparsity B.precision

/-- A record of a forward gate word and budgets for inverse, controlled, preparation, and
inverse-preparation access. -/
structure PaidAccess where

  wires : ℕ

  forward : List FiniteGateCode

  inverseGates : ℕ

  controlledGates : ℕ

  prepGates : ℕ

  prepInverseGates : ℕ

/-- Legality of the forward word, preservation of its length by adjoint, and the stated inverse,
controlled, and preparation budget inequalities. -/
def PaidAccess.Explicit (a : PaidAccess) : Prop :=
  finiteWordLegal a.wires a.forward = true ∧
    (finiteWordAdjoint a.forward).length = a.forward.length ∧
    a.forward.length ≤ a.inverseGates ∧
    a.forward.length ≤ a.controlledGates ∧
    a.prepGates ≤ a.prepInverseGates

/-- Twice the length of the forward gate word. -/
def PaidAccess.RoundTrip (a : PaidAccess) : ℕ :=
  2 * a.forward.length

/-- A record of the number of fresh trials, success probability per trial, and cost per trial. -/
structure FreshRetrySchedule where

  trials : ℕ

  perTrialSuccess : ℝ

  perTrialCost : ℕ

/-- The independent-trial failure expression `(1 - perTrialSuccess)^trials`. -/
noncomputable def FreshRetrySchedule.jointFailure (s : FreshRetrySchedule) : ℝ :=
  (1 - s.perTrialSuccess) ^ s.trials

/-- The number of trials multiplied by their common cost. -/
def FreshRetrySchedule.totalCost (s : FreshRetrySchedule) : ℕ :=
  s.trials * s.perTrialCost

/-- The proposition that a nonempty fresh-retry schedule has the stated linear total cost,
product failure expression, and cost at least that of one trial. -/
def freshRetryIsNotAmplification : Prop :=
  ∀ (s : FreshRetrySchedule), 0 < s.trials → 0 ≤ s.perTrialSuccess →
    s.perTrialSuccess < 1 →
    s.totalCost = s.trials * s.perTrialCost ∧
      s.jointFailure = (1 - s.perTrialSuccess) ^ s.trials ∧
      s.perTrialCost ≤ s.totalCost

/-- The uniform HHL word's query-count expression `2 * (M - 1)`. -/
def uniformWordQueries (M : ℕ) : ℕ := 2 * (M - 1)

/-- The uniform HHL word's fixed-gate expression `4 * (M - 1) + 6`. -/
def uniformWordGates (M : ℕ) : ℕ := 4 * (M - 1) + 6

/-- The proposition recording the full uniform HHL query and gate formulas and the query-count
upper bound by the gate count for `M ≥ 2`. -/
def uniformGridChargedAtFullScale : Prop :=
  ∀ (M : ℕ), 2 ≤ M →
    uniformWordQueries M = 2 * (M - 1) ∧
      uniformWordGates M = 4 * (M - 1) + 6 ∧
      uniformWordQueries M ≤ uniformWordGates M

/-- A record of dimension, preparation and inverse-preparation words, sparse access, and
Hamiltonian synthesis. -/
structure EffectivePreparationBackend where

  dim : ℕ

  prep : List FiniteGateCode

  prepInverse : List FiniteGateCode

  access : SparseAccessSystem

  synthesis : SparseHamiltonianSynthesis access

/-- Legality of both preparation words, the adjoint-length identity, and existence of a complete
Hamiltonian backend with the specified access, sparsity, and precision. -/
def EffectivePreparationBackend.Complete (B : EffectivePreparationBackend)
    (s k : ℕ) : Prop :=
  finiteWordLegal (qlsBitWidth B.dim) B.prep = true ∧
    finiteWordLegal (qlsBitWidth B.dim) B.prepInverse = true ∧
    (finiteWordAdjoint B.prep).length = B.prep.length ∧
    ∃ hb : HamiltonianBackend, hb.access = B.access ∧ hb.sparsity = s ∧
      hb.precision = k ∧ hb.Complete

/-- A system-quantization specification given by its digit count. -/
structure SystemDecomputation where

  digits : ℕ

/-- A positive digit count and strict componentwise dyadic error bounds for every real and
imaginary matrix entry. -/
def SystemDecomputation.Complete {m n : ℕ} (D : SystemDecomputation)
    (A : Matrix (Fin m) (Fin n) ℂ) : Prop :=
  0 < D.digits ∧
    ∀ i j,
      |(A i j).re - ((quantizeReal D.digits (A i j).re : ℚ) : ℝ)| <
        (1 / 2 : ℝ) ^ D.digits ∧
      |(A i j).im - ((quantizeReal D.digits (A i j).im : ℚ) : ℝ)| <
        (1 / 2 : ℝ) ^ D.digits

end Qatlib.Concepts.HhlAlgorithms.SinEnvFilter
