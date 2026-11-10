/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.QspSimulation.Achievability.QspSimulationDefs
import Qatlib.Concepts.QspSimulation.JacobiAnger.ComputedSignalSimulation
import Qatlib.Concepts.CopyEvolution.Discriminate.UnitaryExponentialRemainder
import Qatlib.Concepts.RandCompile.ChannelBudget.FiniteDiamondQdriftRefinedDefs
set_option backward.isDefEq.respectTransparency false
set_option warningAsError false
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

abbrev JaDomain := Qatlib.Concepts.QspSimulation.Achievability.JaDomain

noncomputable abbrev jaAccuracy := Qatlib.Concepts.QspSimulation.Achievability.jaAccuracy

noncomputable abbrev jaCount := Qatlib.Concepts.QspSimulation.Achievability.jaCount

noncomputable abbrev jaIdealShape := Qatlib.Concepts.QspSimulation.Achievability.jaIdealShape

noncomputable abbrev jaLogBudget := Qatlib.Concepts.QspSimulation.Achievability.jaLogBudget

abbrev honestPhaseRun := Qatlib.Concepts.QspSimulation.Achievability.honestPhaseRun

noncomputable abbrev phaseSearchWords :=
  Qatlib.Concepts.QspSimulation.Achievability.phaseSearchWords

abbrev PhaseRunLedger := Qatlib.Concepts.QspSimulation.Achievability.PhaseRunLedger

abbrev PhaseRunOutput := Qatlib.Concepts.QspSimulation.Achievability.PhaseRunOutput

abbrev EffectiveValueBound := Qatlib.Concepts.QspSimulation.Achievability.EffectiveValueBound

abbrev EffectiveSparseLegal := Qatlib.Concepts.QspSimulation.Achievability.EffectiveSparseLegal

noncomputable abbrev quantizationErrorBound :=
  Qatlib.Concepts.QspSimulation.Achievability.quantizationErrorBound

noncomputable abbrev entryQuantizationError :=
  Qatlib.Concepts.QspSimulation.Achievability.entryQuantizationError

noncomputable abbrev hostingQubits := Qatlib.Concepts.QspSimulation.Achievability.hostingQubits

noncomputable abbrev sparseSimulationWord {H I : Type} [Fintype H] [DecidableEq H]
    [Fintype I] [DecidableEq I] (F : Matrix H I ℂ) (p : List ℚ) (d : ℕ) (eps : ℚ) :
    List (AdjointStep (Bool × (Bool × H))) :=
  Qatlib.Concepts.QspSimulation.Achievability.sparseSimulationWord F p d eps

noncomputable abbrev sparseSimulationLedger {H I : Type} [Fintype H] [DecidableEq H]
    [Fintype I] [DecidableEq I] (F : Matrix H I ℂ) (p : List ℚ) (d : ℕ) (eps : ℚ)
    (targetError : ℝ) : Qatlib.Concepts.QspSimulation.Achievability.SparseSimulationLedger :=
  Qatlib.Concepts.QspSimulation.Achievability.sparseSimulationLedger F p d eps targetError

abbrev RatProgram :=
    Qatlib.Concepts.RandCompile.ChannelBudget.FiniteDiamondQdriftRefinedDefs.RatProgram

abbrev ratLit : ℚ → RatProgram :=
  @Qatlib.Concepts.RandCompile.ChannelBudget.FiniteDiamondQdriftRefinedDefs.RatProgram.lit

abbrev ratAdd : RatProgram → RatProgram → RatProgram :=
  @Qatlib.Concepts.RandCompile.ChannelBudget.FiniteDiamondQdriftRefinedDefs.RatProgram.add

abbrev ratEval : RatProgram → ℚ :=
  Qatlib.Concepts.RandCompile.ChannelBudget.FiniteDiamondQdriftRefinedDefs.RatProgram.eval

abbrev phaseToleranceBits : ℚ → ℕ :=
  Qatlib.Concepts.NativeNumerics.PhaseSynthesis.phaseToleranceBits

abbrev phaseGridBits : ℕ → ℕ → ℕ :=
  Qatlib.Concepts.NativeNumerics.PhaseSynthesis.phaseGridBits

noncomputable def analyticPhasePacket (t : ℚ) (k : ℕ) (cosine : Bool) : PhaseData :=
  let h := computed_signal_synthesized_packets t k
  let c := Classical.choose h
  let s := Classical.choose (Classical.choose_spec h)
  if cosine then c else s

noncomputable def analyticPhaseCost (t : ℚ) (k : ℕ) : ℕ := computedSignalCutoff t k + 1

noncomputable def exhaustivePhaseCost (t : ℚ) (k : ℕ) : ℕ :=
  phaseSearchWords (2 * computedSignalCutoff t k + 1)
    (phaseToleranceBits (computedSignalTolerance t k))

def simQspTimeRead (x : ℝ) (q : ℕ → ℚ) : Prop :=
  ∀ k : ℕ, |x - (q k : ℝ)| ≤ (1 / 2 : ℝ) ^ k

structure QspSimulationLedger where

  qubits : ℕ

  fixedGates : ℕ

  oracleQueries : ℕ

  failureRate : ℝ

  truncationError : ℝ

noncomputable def simQspLedger {H I : Type} [Fintype H] [DecidableEq H]
    [Fintype I] [DecidableEq I] (F : Matrix H I ℂ) (t : ℚ) (k : ℕ) (δ : ℝ) :
    QspSimulationLedger :=
  let cs := computedSignalWord F t k
  { qubits := hostingQubits (Fintype.card H)
    fixedGates := adjointGateCount cs
    oracleQueries := adjointQueryCount cs
    failureRate := (adjointQueryCount cs : ℝ) * δ
    truncationError := (1 / 2 : ℝ) ^ k }

noncomputable def simQspReadProgram (t : ℚ) (k : ℕ) : RatProgram :=
  ratAdd (ratLit (computedSignalSegments t : ℚ))
    (ratAdd (ratLit (computedSignalCutoff t k : ℚ))
      (ratAdd (ratLit ((1 / 2 : ℚ) ^ k)) (ratLit (computedSignalTolerance t k))))

end Qatlib.Concepts.QspSimulation.JacobiAnger
