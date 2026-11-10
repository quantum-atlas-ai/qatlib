/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.Cbmd26.Algorithms.SecondOrderCertificateBudget
set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

open Qatlib.Concepts.AEMeanReadout.LocalAEBackend
open Qatlib.Concepts.CoherentSim.CoherentOAA Qatlib.Foundations.InstrumentCore.ProjectiveMeasurementLaws Qatlib.Foundations.OperatorErrors.OperatorError
open Qatlib.Concepts.LchsSimulation.StaticLchs Qatlib.Foundations.PureStateMath.Reflection
open Qatlib.Concepts.LcuPostselect.ScaledLCU
open Qatlib.Concepts.LocalMachine.LocalTransport
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.QsvtCore.QueryLowerBound
open Qatlib.Concepts.SignalPrimitive.HermitianQSVT
open Qatlib.Concepts.SpectralReadout.PhaseReadout Qatlib.Foundations.InstrumentCore.Measurement
open Qatlib.Concepts.SpectralSketch.SpectrumPerturb
open Qatlib.Concepts.TrotterFormula.SuzukiFourth
open Qatlib.Foundations.BornMetrics.EventProbability
open Qatlib.Concepts.Execution.WorkspaceCP
open Qatlib.Foundations.InstrumentCore.ProjectiveMeasurement
open Qatlib.Concepts.QueryWordCore.AdjointCircuits
open Qatlib.Foundations.QueryWordCore.Circuit
open Qatlib.Concepts.ReferenceError.RefTraceError
open Qatlib.Concepts.BlockEncoding.EncodingCore
open Qatlib.Concepts.FairRandomBits.FiniteCoinExecution
open Qatlib.Concepts.QspSimulation.Achievability
open Qatlib.Concepts.PhaseGeometry.Phase
open Qatlib.Concepts.LinearLearning.ConcisePipeline
open Qatlib.Concepts.BlockEncoding
open Qatlib.Concepts.BlockEncoding.Encoding
open Qatlib.Concepts.BlockEncoding.Postselection
open Qatlib.Concepts.BlockEncoding.Postselection.Encoding
open Qatlib.Concepts.WalkSearch.Spectral
open Qatlib.Concepts.BlockEncoding.LCU Qatlib.Foundations.PureStateMath.BornBridge Qatlib.Concepts.CopyEvolution.Discriminate
open Qatlib.Concepts.RandCompile.ChannelBudget
open Qatlib.Concepts.OperatorErrors.Robustness.SignalProcessing

namespace Qatlib.Papers.Cbmd26.Algorithms

set_option autoImplicit false
noncomputable section
namespace CBMD
open Matrix
open scoped ENNReal

variable {W I : Type} [Fintype W] [DecidableEq W] [Fintype I] [DecidableEq I]

theorem ThreeOracleOutputCertificate.combined_matrix_queries
    {target : Matrix I I ℂ} {O1 O2 B : Matrix W W ℂ} {cs : List (PreparedStep W)}
    {F : Matrix W I ℂ} {zero : W} {S : Finset W} {ψ : QState I} {ε : ℝ}
    {m : ℕ} [NeZero m] {matrixBudget stateBudget : ℝ}
    (h : ThreeOracleOutputCertificate target O1 O2 B cs F zero S ψ ε m matrixBudget stateBudget)
    (hbudget : 0 ≤ matrixBudget) :
    let A := evaluatePrepared O1 O2 cs * B
    ∃ hA : A ∈ Matrix.unitaryGroup W ℂ,
      Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectation (randomizedAAHerald A hA zero S m)
        (fun x => ((threeFirstQueries (threeAAWord cs zero S (aaRounds x.1)) +
          threeSecondQueries (threeAAWord cs zero S (aaRounds x.1)) : ℕ) : ℝ≥0∞)) ≤
        ENNReal.ofReal (2 * matrixBudget) ∧
      ∀ choice : Bool × Fin m,
        ((threeFirstQueries (threeAAWord cs zero S (aaRounds choice)) +
          threeSecondQueries (threeAAWord cs zero S (aaRounds choice)) : ℕ) : ℝ) ≤
          8 * matrixBudget := by
  obtain ⟨_,hA,_,hq1,hq2,_,hpath,_,_⟩ := h
  refine ⟨hA, ?_, ?_⟩
  · simp only [Nat.cast_add]
    rw [Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectation_add]
    apply (add_le_add hq1 hq2).trans
    rw [← ENNReal.ofReal_add hbudget hbudget]
    exact le_of_eq (congrArg ENNReal.ofReal (by ring))
  · intro choice
    obtain ⟨ha,hb,_⟩ := hpath choice
    push_cast
    linarith only [ha,hb]

end CBMD

end
end Qatlib.Papers.Cbmd26.Algorithms
