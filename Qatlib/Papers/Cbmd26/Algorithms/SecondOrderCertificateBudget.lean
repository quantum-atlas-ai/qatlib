/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.Cbmd26.Algorithms.CosineSecondOrderAmplification

/-!
# Monotonicity of Second-Order Query Budgets

`ThreeOracleOutputCertificate.mono` allows the matrix-oracle and state-preparation budgets in a
three-oracle output certificate to be enlarged. Its proof transports both expected query bounds
and the bounds for each execution path while retaining the certificate's preparation and output
guarantees.

This budget relaxation supports reporting convenient upper bounds for the second-order CBMD
algorithms of [WangEtAl2026].

## Main statements

* `ThreeOracleOutputCertificate.mono` preserves a certificate whenever both replacement budgets
  are at least the original budgets.

## References

* [Wang et al., 2026][WangEtAl2026]
-/

set_option backward.isDefEq.respectTransparency false

open Qatlib.Concepts.AEMeanReadout.LocalAEBackend
open Qatlib.Concepts.CoherentSim.CoherentOAA
open Qatlib.Foundations.InstrumentCore.ProjectiveMeasurementLaws
open Qatlib.Foundations.OperatorErrors.OperatorError
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
open Qatlib.Concepts.BlockEncoding.LCU Qatlib.Foundations.PureStateMath.BornBridge
open Qatlib.Concepts.CopyEvolution.Discriminate
open Qatlib.Concepts.RandCompile.ChannelBudget
open Qatlib.Concepts.OperatorErrors.Robustness.SignalProcessing

namespace Qatlib.Papers.Cbmd26.Algorithms

set_option autoImplicit false
noncomputable section
namespace CBMD
open Matrix

variable {W I : Type} [Fintype W] [DecidableEq W] [Fintype I] [DecidableEq I]

/-- A three-oracle output certificate remains valid when its matrix-query and state-preparation
budgets are enlarged, including both expected and per-path bounds. -/
theorem ThreeOracleOutputCertificate.mono
    {target : Matrix I I ℂ} {O1 O2 B : Matrix W W ℂ} {cs : List (PreparedStep W)}
    {F : Matrix W I ℂ} {zero : W} {S : Finset W} {ψ : QState I} {ε : ℝ}
    {m : ℕ} [NeZero m] {matrixBudget stateBudget matrixBudget' stateBudget' : ℝ}
    (h : ThreeOracleOutputCertificate target O1 O2 B cs F zero S ψ ε m matrixBudget stateBudget)
    (hm : matrixBudget ≤ matrixBudget') (hs : stateBudget ≤ stateBudget') :
    ThreeOracleOutputCertificate target O1 O2 B cs F zero S ψ ε m matrixBudget' stateBudget' := by
  obtain ⟨hw,hA,hprob,hq1,hq2,hqs,hpath,hrun,hout⟩ := h
  refine ⟨hw,hA,hprob,hq1.trans (ENNReal.ofReal_le_ofReal hm),
    hq2.trans (ENNReal.ofReal_le_ofReal hm),hqs.trans (ENNReal.ofReal_le_ofReal hs),?_,hrun,hout⟩
  intro choice
  obtain ⟨ha,hb,hc⟩ := hpath choice
  exact ⟨ha.trans (mul_le_mul_of_nonneg_left hm (by norm_num)),
    hb.trans (mul_le_mul_of_nonneg_left hm (by norm_num)),
    hc.trans (mul_le_mul_of_nonneg_left hs (by norm_num))⟩

end CBMD

end
end Qatlib.Papers.Cbmd26.Algorithms
