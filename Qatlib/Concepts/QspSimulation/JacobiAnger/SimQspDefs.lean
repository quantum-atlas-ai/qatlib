/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.QspSimulation.Achievability.QspSimulationDefs
import Qatlib.Concepts.QspSimulation.JacobiAnger.ComputedSignalSimulation
import Qatlib.Concepts.CopyEvolution.Discriminate.UnitaryExponentialRemainder
import Qatlib.Concepts.RandCompile.ChannelBudget.FiniteDiamondQdriftRefinedDefs

/-!
# Resource ledgers for Jacobi–Anger simulation

This module re-exports the achievability interfaces used by Jacobi–Anger simulation and defines
analytic phase packets, classical cost estimates, and a simulation resource ledger.
`simQspLedger` records the qubit, gate, query, failure, and truncation budgets of
`computedSignalWord`, while `simQspTimeRead` specifies dyadic rational approximations to a real
time. Background and related constructions are discussed in [LowChuang2017].

## Main statements

* `analyticPhasePacket`: selects a synthesized cosine or sine phase packet.
* `simQspLedger`: collects resources and errors for a computed signal word.
* `simQspReadProgram`: packages numerical simulation parameters as a rational program.

## References

* [Low and Chuang, 2017][LowChuang2017]
-/

set_option backward.isDefEq.respectTransparency false
open Qatlib.Concepts.CoherentSim.CoherentOAA
open Qatlib.Foundations.InstrumentCore.ProjectiveMeasurementLaws
open Qatlib.Foundations.OperatorErrors.OperatorError
open Qatlib.Concepts.NativeNumerics.PhaseSynthesis
open Qatlib.Concepts.QspSimulation.JacobiAnger
open Qatlib.Concepts.QspSimulation.Achievability

set_option autoImplicit false
set_option maxHeartbeats 2000000

namespace Qatlib.Concepts.QspSimulation.JacobiAnger

open Matrix Qatlib
open scoped BigOperators Classical ENNReal Matrix.Norms.L2Operator

/-- The Jacobi–Anger namespace alias for `Qatlib.Concepts.QspSimulation.Achievability.JaDomain`. -/
abbrev JaDomain := Qatlib.Concepts.QspSimulation.Achievability.JaDomain

/-- The Jacobi–Anger namespace alias for the achievability accuracy parameter
`Qatlib.Concepts.QspSimulation.Achievability.jaAccuracy`. -/
noncomputable abbrev jaAccuracy := Qatlib.Concepts.QspSimulation.Achievability.jaAccuracy

/-- The Jacobi–Anger namespace alias for `Qatlib.Concepts.QspSimulation.Achievability.jaCount`. -/
noncomputable abbrev jaCount := Qatlib.Concepts.QspSimulation.Achievability.jaCount

/-- The Jacobi–Anger namespace alias for the ideal-shape function
`Qatlib.Concepts.QspSimulation.Achievability.jaIdealShape`. -/
noncomputable abbrev jaIdealShape := Qatlib.Concepts.QspSimulation.Achievability.jaIdealShape

/-- The Jacobi–Anger namespace alias for
`Qatlib.Concepts.QspSimulation.Achievability.jaLogBudget`. -/
noncomputable abbrev jaLogBudget := Qatlib.Concepts.QspSimulation.Achievability.jaLogBudget

/-- The Jacobi–Anger namespace alias for
`Qatlib.Concepts.QspSimulation.Achievability.honestPhaseRun`. -/
abbrev honestPhaseRun := Qatlib.Concepts.QspSimulation.Achievability.honestPhaseRun

/-- The Jacobi–Anger namespace alias for the phase-search word budget
`Qatlib.Concepts.QspSimulation.Achievability.phaseSearchWords`. -/
noncomputable abbrev phaseSearchWords :=
  Qatlib.Concepts.QspSimulation.Achievability.phaseSearchWords

/-- The Jacobi–Anger namespace alias for the phase-run ledger
`Qatlib.Concepts.QspSimulation.Achievability.PhaseRunLedger`. -/
abbrev PhaseRunLedger := Qatlib.Concepts.QspSimulation.Achievability.PhaseRunLedger

/-- The Jacobi–Anger namespace alias for the phase-run output type
`Qatlib.Concepts.QspSimulation.Achievability.PhaseRunOutput`. -/
abbrev PhaseRunOutput := Qatlib.Concepts.QspSimulation.Achievability.PhaseRunOutput

/-- The Jacobi–Anger namespace alias for
`Qatlib.Concepts.QspSimulation.Achievability.EffectiveValueBound`. -/
abbrev EffectiveValueBound := Qatlib.Concepts.QspSimulation.Achievability.EffectiveValueBound

/-- The Jacobi–Anger namespace alias for
`Qatlib.Concepts.QspSimulation.Achievability.EffectiveSparseLegal`. -/
abbrev EffectiveSparseLegal := Qatlib.Concepts.QspSimulation.Achievability.EffectiveSparseLegal

/-- The Jacobi–Anger namespace alias for the quantization error bound
`Qatlib.Concepts.QspSimulation.Achievability.quantizationErrorBound`. -/
noncomputable abbrev quantizationErrorBound :=
  Qatlib.Concepts.QspSimulation.Achievability.quantizationErrorBound

/-- The Jacobi–Anger namespace alias for
`Qatlib.Concepts.QspSimulation.Achievability.entryQuantizationError`. -/
noncomputable abbrev entryQuantizationError :=
  Qatlib.Concepts.QspSimulation.Achievability.entryQuantizationError

/-- The Jacobi–Anger namespace alias for the register-size function
`Qatlib.Concepts.QspSimulation.Achievability.hostingQubits`. -/
noncomputable abbrev hostingQubits := Qatlib.Concepts.QspSimulation.Achievability.hostingQubits

/-- The achievability sparse-simulation word for the matrix `F`, rational coefficient list `p`,
degree parameter `d`, and tolerance `eps`, viewed in the Jacobi–Anger namespace. -/
noncomputable abbrev sparseSimulationWord {H I : Type} [Fintype H] [DecidableEq H]
    [Fintype I] [DecidableEq I] (F : Matrix H I ℂ) (p : List ℚ) (d : ℕ) (eps : ℚ) :
    List (AdjointStep (Bool × (Bool × H))) :=
  Qatlib.Concepts.QspSimulation.Achievability.sparseSimulationWord F p d eps

/-- The achievability sparse-simulation resource ledger for the given matrix, coefficients,
degree, tolerance, and target error. -/
noncomputable abbrev sparseSimulationLedger {H I : Type} [Fintype H] [DecidableEq H]
    [Fintype I] [DecidableEq I] (F : Matrix H I ℂ) (p : List ℚ) (d : ℕ) (eps : ℚ)
    (targetError : ℝ) : Qatlib.Concepts.QspSimulation.Achievability.SparseSimulationLedger :=
  Qatlib.Concepts.QspSimulation.Achievability.sparseSimulationLedger F p d eps targetError

/-- The rational arithmetic program type used to package classical simulation parameters. -/
abbrev RatProgram :=
    Qatlib.Concepts.RandCompile.ChannelBudget.FiniteDiamondQdriftRefinedDefs.RatProgram

/-- Constructs a rational arithmetic program consisting of a single rational literal. -/
abbrev ratLit : ℚ → RatProgram :=
  @Qatlib.Concepts.RandCompile.ChannelBudget.FiniteDiamondQdriftRefinedDefs.RatProgram.lit

/-- Constructs the sum of two rational arithmetic programs. -/
abbrev ratAdd : RatProgram → RatProgram → RatProgram :=
  @Qatlib.Concepts.RandCompile.ChannelBudget.FiniteDiamondQdriftRefinedDefs.RatProgram.add

/-- Evaluates a rational arithmetic program to a rational number. -/
abbrev ratEval : RatProgram → ℚ :=
  Qatlib.Concepts.RandCompile.ChannelBudget.FiniteDiamondQdriftRefinedDefs.RatProgram.eval

/-- The phase-synthesis precision parameter associated with a rational tolerance. -/
abbrev phaseToleranceBits : ℚ → ℕ :=
  Qatlib.Concepts.NativeNumerics.PhaseSynthesis.phaseToleranceBits

/-- The phase-synthesis grid bit count as a function of the two natural-number parameters. -/
abbrev phaseGridBits : ℕ → ℕ → ℕ :=
  Qatlib.Concepts.NativeNumerics.PhaseSynthesis.phaseGridBits

/-- Selects the synthesized cosine packet when `cosine` is true and the synthesized sine packet
otherwise, using `computed_signal_synthesized_packets`. -/
noncomputable def analyticPhasePacket (t : ℚ) (k : ℕ) (cosine : Bool) : PhaseData :=
  let h := computed_signal_synthesized_packets t k
  let c := Classical.choose h
  let s := Classical.choose (Classical.choose_spec h)
  if cosine then c else s

/-- The analytic phase cost estimate `computedSignalCutoff t k + 1`. -/
noncomputable def analyticPhaseCost (t : ℚ) (k : ℕ) : ℕ := computedSignalCutoff t k + 1

/-- The exhaustive phase-search word budget at degree `2 * computedSignalCutoff t k + 1` and the
precision prescribed by `computedSignalTolerance`. -/
noncomputable def exhaustivePhaseCost (t : ℚ) (k : ℕ) : ℕ :=
  phaseSearchWords (2 * computedSignalCutoff t k + 1)
    (phaseToleranceBits (computedSignalTolerance t k))

/-- States that `q k` approximates the real time `x` with absolute error at most 2⁻ᵏ for every
natural number `k`. -/
def simQspTimeRead (x : ℝ) (q : ℕ → ℚ) : Prop :=
  ∀ k : ℕ, |x - (q k : ℝ)| ≤ (1 / 2 : ℝ) ^ k

/-- Records the qubit count, fixed-gate count, oracle-query count, failure rate, and truncation
error of a QSP simulation. -/
structure QspSimulationLedger where

  qubits : ℕ

  fixedGates : ℕ

  oracleQueries : ℕ

  failureRate : ℝ

  truncationError : ℝ

/-- Builds the ledger of `computedSignalWord F t k`, assigning failure rate equal to the query
count times `δ` and truncation error 2⁻ᵏ. -/
noncomputable def simQspLedger {H I : Type} [Fintype H] [DecidableEq H]
    [Fintype I] [DecidableEq I] (F : Matrix H I ℂ) (t : ℚ) (k : ℕ) (δ : ℝ) :
    QspSimulationLedger :=
  let cs := computedSignalWord F t k
  { qubits := hostingQubits (Fintype.card H)
    fixedGates := adjointGateCount cs
    oracleQueries := adjointQueryCount cs
    failureRate := (adjointQueryCount cs : ℝ) * δ
    truncationError := (1 / 2 : ℝ) ^ k }

/-- Forms a rational program summing the segment count, cutoff, dyadic error 2⁻ᵏ, and signal
tolerance used by the computed simulation. -/
noncomputable def simQspReadProgram (t : ℚ) (k : ℕ) : RatProgram :=
  ratAdd (ratLit (computedSignalSegments t : ℚ))
    (ratAdd (ratLit (computedSignalCutoff t k : ℚ))
      (ratAdd (ratLit ((1 / 2 : ℚ) ^ k)) (ratLit (computedSignalTolerance t k))))

end Qatlib.Concepts.QspSimulation.JacobiAnger
