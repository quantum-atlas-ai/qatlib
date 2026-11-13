/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.MbqcFlow.FlowDecision.PureToMixedConditionalDefs
import Qatlib.Concepts.HhlErrorBridge.FilterStability
import Qatlib.Concepts.HhlAlgorithms.SinEnvProgram.SinEnvelopeHHLConsumers
import Qatlib.Concepts.HhlAlgorithms.UniformHHL.OffGridSignedHHL
import Qatlib.Concepts.HhlAlgorithms.Postselection.RationalHHLNoiseRetry
import Qatlib.Concepts.CoherentSim.CoherentOAA.Pseudoinverse
import Qatlib.Concepts.LocalMachine.LocalTransport.LeastSquaresOutputSpec
import Qatlib.Concepts.AdaptiveCP.BranchTrace.Instrument
import Qatlib.Concepts.RandCompile.FairBitSampling.DiamondStabilizationConsumers
import Qatlib.Concepts.GateVocabulary.FiniteGateDescription
import Qatlib.Concepts.BlockEncoding.Basic

/-!
# HHL input models and resource records

This module defines filter masses, direction-error expressions, kernel records, Hamiltonian
synthesis specifications, and signed dyadic input quantization. `HhlBackendLedger`,
`InstrumentAccessCost`, and `SuccessorProgramBudget` record the explicit resources used by the
HHL consumers motivated by [HarrowHassidimLloyd2009].

Predicates such as `HamiltonianSynthesis.SynthesizesAt` and `ThreeStateFilterRun.Realizes` state
the approximation, legality, and budget conditions separately from the underlying data records.

## Main statements

* `ThreeStateFilterRun.Realizes`: filter parameter, mass, direction, and resource conditions.
* `HamiltonianSynthesis.SynthesizesAt`: a legal finite-gate approximation to Hamiltonian
  evolution with bounded error.
* `RealInputQuantizer.QuantizesAt`: positive-precision signed dyadic rounding.

## References

* [Harrow et al., 2009][HarrowHassidimLloyd2009]
-/

set_option backward.isDefEq.respectTransparency false

open Qatlib.Concepts.HhlAlgorithms.SinEnvFilter.SinEnvelopeHHL
open Qatlib.Concepts.HhlErrorBridge.FilterStability
open Qatlib.Concepts.LinearLearning.ConcisePipeline

open Qatlib.Concepts.AdversaryBounds.AdvDuality
open Qatlib.Concepts.CoherentSim.CoherentOAA
open Qatlib.Foundations.InstrumentCore.ProjectiveMeasurementLaws
open Qatlib.Foundations.OperatorErrors.OperatorError
open Qatlib.Concepts.LocalMachine.LocalTransport
open Qatlib.Foundations.BornMetrics.EventProbability
open Qatlib.Concepts.GateVocabulary.FiniteGateDescription
open Qatlib.Concepts.HhlAlgorithms.Postselection
open Qatlib.Concepts.HhlAlgorithms.UniformHHL
open Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw
open Qatlib.Concepts.BlockEncoding

open Qatlib.Concepts.AdaptiveCP.BranchTrace
open Qatlib.Concepts.MbqcFlow.FlowDecision Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.QueryWordCore.AdjointCircuits
open Qatlib.Concepts.CoherentSim.CoherentOAA.SignalProcessing
open Qatlib.Concepts.PhaseGeometry.Phase
open Qatlib.Concepts.OperatorErrors.Robustness.SignalProcessing

set_option autoImplicit false

namespace Qatlib.Concepts.HhlAlgorithms.SinEnvFilter

open Matrix Qatlib.Concepts.QueryWordCore.AdjointCircuits
open Qatlib.Concepts.CoherentSim.CoherentOAA.SignalProcessing Qatlib.Concepts.PhaseGeometry.Phase
open Qatlib.Concepts.OperatorErrors.Robustness.SignalProcessing
open scoped Classical Matrix.Norms.L2Operator

/-- The squared well-conditioned filter amplitude `sinEnvelopeFilterF d θ`. -/
noncomputable def threeStateWellMass (d θ : ℝ) : ℝ := sinEnvelopeFilterF d θ ^ 2

/-- The squared ill-conditioned filter amplitude `sinEnvelopeFilterG d θ`. -/
noncomputable def threeStateIllMass (d θ : ℝ) : ℝ := sinEnvelopeFilterG d θ ^ 2

/-- The combined selected mass `sinEnvelopeFlagMass d θ` of the three-state filter. -/
noncomputable def threeStateSelectedMass (d θ : ℝ) : ℝ := sinEnvelopeFlagMass d θ

/-- The normalization error expression `2 * e / x` for error `e` and target norm `x`. -/
noncomputable def threeStateDirectionBound (e x : ℝ) : ℝ := 2 * e / x

/-- A record of gap, phase, filter error, target norm, direction error, and gate and bit budgets
for a three-state filter. -/
structure ThreeStateFilterRun where

  gap : ℝ

  phase : ℝ

  filterError : ℝ

  targetNorm : ℝ

  directionError : ℝ

  gateBudget : ℕ

  bitBudget : ℕ

/-- The gate budget `256 * 16 * (bits + k + 2)^8` for a three-state filter record. -/
def threeStateGateBudget (bits k : ℕ) : ℕ := 256 * 16 * (bits + k + 2) ^ 8

/-- The bit budget `4 * (bits + k + 4)` for a three-state filter record. -/
def threeStateBitBudget (bits k : ℕ) : ℕ := 4 * (bits + k + 4)

/-- The parameter, mass-decomposition, direction-error, and resource inequalities required of a
three-state filter record. -/
noncomputable def ThreeStateFilterRun.Realizes (run : ThreeStateFilterRun)
    (bits k : ℕ) : Prop :=
  0 < run.gap ∧ 0 ≤ run.filterError ∧ 0 < run.targetNorm ∧
    run.filterError < run.targetNorm ∧
    threeStateSelectedMass run.gap run.phase
      = threeStateWellMass run.gap run.phase + threeStateIllMass run.gap run.phase ∧
    run.directionError = threeStateDirectionBound run.filterError run.targetNorm ∧
    run.gateBudget ≤ threeStateGateBudget bits k ∧
    run.bitBudget ≤ threeStateBitBudget bits k

/-- The kernel query budget `⌈1 / d⌉₊ * (8 * k + 16)`. -/
noncomputable def nearOptimalKernelQueries (d : ℝ) (k : ℕ) : ℕ :=
  (Nat.ceil (1 / d)) * (8 * k + 16)

/-- A record of a phase-estimation grid, query budget, and accuracy. -/
structure QpeKernelProgram where

  grid : ℕ

  queryBudget : ℕ

  accuracy : ℝ

/-- The conditions that a kernel record has grid size at least two, positive accuracy within
`uniformHHLAccuracy d k`, and query budget within `nearOptimalKernelQueries d k`. -/
def QpeKernelProgram.SolvesAt (K : QpeKernelProgram) (d : ℝ) (k : ℕ) : Prop :=
  2 ≤ K.grid ∧ 0 < K.accuracy ∧
    K.accuracy ≤ uniformHHLAccuracy d k ∧
    K.queryBudget ≤ nearOptimalKernelQueries d k

/-- The map sending a finite index to its low `w` binary bits. -/
def finEmbed (N w : ℕ) : Fin N → Reg w := fun i t => i.val.testBit t.1

/-- The matrix of a finite-gate word, formed by multiplying its gate matrices in reverse list
order. -/
noncomputable def wordMatrix (w : ℕ) (gs : List FiniteGateCode) :
    Matrix (Reg w) (Reg w) ℂ :=
  (gs.map (finiteCodeMatrix w)).reverse.prod

/-- The matrix obtained by restricting both indices of `G` along the map `e`. -/
noncomputable def compressEmbed {I : Type} [Fintype I] {w : ℕ}
    (e : I → Reg w) (G : Matrix (Reg w) (Reg w) ℂ) : Matrix I I ℂ :=
  Matrix.of fun i j => G (e i) (e j)

/-- A record of a Hamiltonian, evolution time, register size, finite-gate word, error, and
resource budgets. -/
structure HamiltonianSynthesis (N : ℕ) where

  ham : Matrix (Fin N) (Fin N) ℂ

  time : ℝ

  wires : ℕ

  word : List FiniteGateCode

  error : ℝ

  gateBudget : ℕ

  bitBudget : ℕ

/-- The synthesis gate budget `256 * (N + 1)^2 * 4^N * (bits + k + 2)^8`. -/
def hamiltonianGateBudget (N bits k : ℕ) : ℕ :=
  256 * (N + 1) ^ 2 * 4 ^ N * (bits + k + 2) ^ 8

/-- The synthesis bit budget `(N + 2) * (bits + k + 4)`. -/
def hamiltonianBitBudget (N bits k : ℕ) : ℕ := (N + 2) * (bits + k + 4)

/-- The Hermitian norm bound, register capacity, word legality, evolution-approximation error,
and budget conditions required of a Hamiltonian synthesis record. -/
noncomputable def HamiltonianSynthesis.SynthesizesAt {N : ℕ}
    (S : HamiltonianSynthesis N) (bits k : ℕ) : Prop :=
  S.ham.IsHermitian ∧ ‖S.ham‖ ≤ 1 ∧ N ≤ 2 ^ S.wires ∧
    finiteWordLegal S.wires S.word = true ∧
    S.error ≤ (1 / 2 : ℝ) ^ k ∧
    ‖compressEmbed (finEmbed N S.wires) (wordMatrix S.wires S.word)
      - HamiltonianEvolution S.ham S.time‖ ≤ S.error ∧
    S.gateBudget ≤ hamiltonianGateBudget N bits k ∧
    S.bitBudget ≤ hamiltonianBitBudget N bits k

/-- The signed dyadic rounding `⌊2^k * x⌋ / 2^k`, using the integer floor. -/
noncomputable def dyadicRound (x : ℝ) (k : ℕ) : ℝ :=
  (Int.floor ((2 : ℝ) ^ k * x) : ℝ) / (2 : ℝ) ^ k

/-- A real-input quantizer specified by its number of binary digits. -/
structure RealInputQuantizer where

  digits : ℕ

/-- The assertion that the digit count is positive and `y` is the corresponding signed dyadic
rounding of `x`. -/
def RealInputQuantizer.QuantizesAt (Q : RealInputQuantizer)
    (x y : ℝ) : Prop :=
  y = dyadicRound x Q.digits ∧ 0 < Q.digits

/-- A ledger of elementary gates, integer bits, and peak space bits. -/
structure HhlBackendLedger where

  elementaryGates : ℕ

  integerBits : ℕ

  peakSpaceBits : ℕ

/-- The explicit HHL backend ledger with gate count `256 * (wires + 1)^2 * 4^wires * (bits + k +
2)^8` and equal integer-bit and space budgets. -/
def hhlBackendBudget (wires bits k : ℕ) : HhlBackendLedger :=
  ⟨256 * (wires + 1) ^ 2 * 4 ^ wires * (bits + k + 2) ^ 8,
    (wires + 2) * (bits + k + 4),
    (wires + 2) * (bits + k + 4)⟩

/-- A record of measurement, preparation, and inverse access counts. -/
structure InstrumentAccessCost where

  measurementAccesses : ℕ

  preparationAccesses : ℕ

  inverseAccesses : ℕ

/-- The access budget with `calls` measurements, `calls + 1` preparations, and `calls` inverse
accesses. -/
def instrumentAccessBudget (calls : ℕ) : InstrumentAccessCost :=
  ⟨calls, calls + 1, calls⟩

/-- The successor success-probability lower-bound expression `(d * θ / 2)^2`. -/
noncomputable def successorSuccessGap (d θ : ℝ) : ℝ := ((d * θ) / 2) ^ 2

/-- The rational successor accuracy parameter `numericHHLAccuracy d θ k`. -/
def successorTightParam (d θ : ℚ) (k : ℕ) : ℚ := numericHHLAccuracy d θ k

/-- The successor gate budget `256 * (calls + 1)^2 * (bits + k + 2)^8`. -/
def successorGateBudget (calls bits k : ℕ) : ℕ :=
  256 * (calls + 1) ^ 2 * (bits + k + 2) ^ 8

/-- The successor bit budget `(calls + 2) * (bits + k + 4)`. -/
def successorBitBudget (calls bits k : ℕ) : ℕ := (calls + 2) * (bits + k + 4)

/-- A record of successor success gap, accuracy parameter, instrument accesses, and gate and bit
budgets. -/
structure SuccessorProgramBudget where

  successGap : ℝ

  tightParam : ℝ

  access : InstrumentAccessCost

  gateBudget : ℕ

  bitBudget : ℕ

/-- The positivity, success-gap upper bound, and access, gate, and bit inequalities required of
a successor budget record. -/
def SuccessorProgramBudget.Realizes (B : SuccessorProgramBudget)
    (calls bits k : ℕ) : Prop :=
  0 < B.successGap ∧ B.successGap ≤ 1 ∧ 0 < B.tightParam ∧
    B.access.measurementAccesses ≤ (instrumentAccessBudget calls).measurementAccesses ∧
    B.access.preparationAccesses ≤ (instrumentAccessBudget calls).preparationAccesses ∧
    B.access.inverseAccesses ≤ (instrumentAccessBudget calls).inverseAccesses ∧
    B.gateBudget ≤ successorGateBudget calls bits k ∧
    B.bitBudget ≤ successorBitBudget calls bits k

end Qatlib.Concepts.HhlAlgorithms.SinEnvFilter
