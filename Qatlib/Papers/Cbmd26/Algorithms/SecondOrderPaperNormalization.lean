/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.Cbmd26.Algorithms.CosineOutputQueryBudget
import Qatlib.Concepts.BlockEncoding.Postselection
import Qatlib.Foundations.CbmdAnalysis.Core.AiryMatrixProjection
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
open scoped Matrix.Norms.L2Operator

def secondOrderPaperNormalization : SecondOrderFamily → ℝ
  | .wave => 1
  | .bessel => 1
  | .airy => _root_.Qatlib.Foundations.CbmdAnalysis.Core.CBMD.airyAi0

theorem secondOrderPaperNormalization_pos (kind : SecondOrderFamily) :
    0 < secondOrderPaperNormalization kind := by
  cases kind
  · norm_num [secondOrderPaperNormalization]
  · norm_num [secondOrderPaperNormalization]
  · exact _root_.Qatlib.Foundations.CbmdAnalysis.Core.CBMD.airyAi0_pos

def secondOrderPaperMatrix {I : Type} [Fintype I] [DecidableEq I]
    (kind : SecondOrderFamily) (A : Matrix I I ℂ) (t : ℝ) : Matrix I I ℂ :=
  (secondOrderPaperNormalization kind : ℂ) • secondOrderPropagator kind A t

theorem secondOrderPaperMatrix_wave {I : Type} [Fintype I] [DecidableEq I]
    (A : Matrix I I ℂ) (t : ℝ) :
    secondOrderPaperMatrix .wave A t = _root_.Qatlib.Foundations.CbmdAnalysis.Core.CBMD.wavePropagator A (t : ℂ) := by
  simp [secondOrderPaperMatrix, secondOrderPaperNormalization, secondOrderPropagator]

theorem secondOrderPaperMatrix_bessel {I : Type} [Fintype I] [DecidableEq I]
    (A : Matrix I I ℂ) (t : ℝ) :
    secondOrderPaperMatrix .bessel A t = _root_.Qatlib.Foundations.CbmdAnalysis.Core.CBMD.besselPropagator A (t : ℂ) := by
  simp [secondOrderPaperMatrix, secondOrderPaperNormalization, secondOrderPropagator]

theorem secondOrderPaperMatrix_airy {I : Type} [Fintype I] [DecidableEq I]
    (A : Matrix I I ℂ) (t : ℝ) :
    secondOrderPaperMatrix .airy A t = _root_.Qatlib.Foundations.CbmdAnalysis.Core.CBMD.airyMatrixProjection A (t : ℂ) :=
  (_root_.Qatlib.Foundations.CbmdAnalysis.Core.CBMD.airyMatrixProjection_eq A (t : ℂ)).symm

def secondOrderPaperOutputNorm {I : Type} [Fintype I] [DecidableEq I]
    (kind : SecondOrderFamily) (A : Matrix I I ℂ) (t : ℝ) (ψ : QState I) : ℝ :=
  ‖stateVector (secondOrderPaperMatrix kind A t *ᵥ ψ)‖

theorem secondOrderPaperOutputNorm_eq {I : Type} [Fintype I] [DecidableEq I]
    (kind : SecondOrderFamily) (A : Matrix I I ℂ) (t : ℝ) (ψ : QState I) :
    secondOrderPaperOutputNorm kind A t ψ = secondOrderPaperNormalization kind *
      ‖stateVector (secondOrderPropagator kind A t *ᵥ ψ)‖ := by
  rw [secondOrderPaperOutputNorm, secondOrderPaperMatrix, Matrix.smul_mulVec]
  change ‖(secondOrderPaperNormalization kind : ℂ) •
    stateVector (secondOrderPropagator kind A t *ᵥ ψ)‖ = _
  rw [norm_smul, Complex.norm_real, Real.norm_of_nonneg (secondOrderPaperNormalization_pos kind).le]

def secondOrderOutputEstimateFactor (kind : SecondOrderFamily) (c : ℝ) : ℝ :=
  max 1 (c * secondOrderPaperNormalization kind)

theorem secondOrderOutputEstimateFactor_ge_one (kind : SecondOrderFamily) (c : ℝ) :
    1 ≤ secondOrderOutputEstimateFactor kind c := le_max_left _ _

theorem secondOrderPaperOutputNorm_pos {I : Type} [Fintype I] [DecidableEq I]
    (kind : SecondOrderFamily) (A : Matrix I I ℂ) (t : ℝ) (ψ : QState I) {η : ℝ}
    (hη : 0 < η) (houtput : η ≤ ‖stateVector (secondOrderPropagator kind A t *ᵥ ψ)‖) :
    0 < secondOrderPaperOutputNorm kind A t ψ := by
  rw [secondOrderPaperOutputNorm_eq]
  exact mul_pos (secondOrderPaperNormalization_pos kind) (hη.trans_le houtput)

theorem secondOrderPaperRatio_compare {I : Type} [Fintype I] [DecidableEq I]
    (kind : SecondOrderFamily) (A : Matrix I I ℂ) (t : ℝ) (ψ : QState I)
    (γ τ η c : ℝ) (hη : 0 < η)
    (houtput : η ≤ ‖stateVector (secondOrderPropagator kind A t *ᵥ ψ)‖)
    (hestimate : ‖stateVector (secondOrderPropagator kind A t *ᵥ ψ)‖ ≤ c * η) :
    cosineRelativeEnvelope γ τ η ≤ secondOrderOutputEstimateFactor kind c *
      cosineRelativeEnvelope γ τ (secondOrderPaperOutputNorm kind A t ψ) := by
  have hν := secondOrderPaperOutputNorm_pos kind A t ψ hη houtput
  have hupper : secondOrderPaperOutputNorm kind A t ψ ≤
      secondOrderOutputEstimateFactor kind c * η := by
    rw [secondOrderPaperOutputNorm_eq]
    calc
      _ ≤ secondOrderPaperNormalization kind * (c * η) :=
        mul_le_mul_of_nonneg_left hestimate (secondOrderPaperNormalization_pos kind).le
      _ = (c * secondOrderPaperNormalization kind) * η := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right (le_max_right _ _) hη.le
  unfold cosineRelativeEnvelope
  rw [← mul_div_assoc]
  apply (le_div_iff₀ hν).mpr
  calc
    _ ≤ (Real.exp (τ * Real.sqrt (γ / 2)) / η) *
        (secondOrderOutputEstimateFactor kind c * η) :=
      mul_le_mul_of_nonneg_left hupper (by positivity)
    _ = _ := by field_simp

end CBMD

end
end Qatlib.Papers.Cbmd26.Algorithms
