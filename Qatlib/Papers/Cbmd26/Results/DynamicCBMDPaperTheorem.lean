/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.Cbmd26.Algorithms.DynamicCBMDConsumer
import Qatlib.Papers.Cbmd26.Algorithms.ComputationalAmplificationBudget
import Qatlib.Papers.Cbmd26.Algorithms.DynamicZeroTimeBridge

/-!
# Dynamic CBMD with output-norm query bounds

This module gives the dynamic preparation result in terms of the actual output norm and a
fixed-factor estimate. Its hypotheses include piecewise-continuous dissipative coefficients,
exact original-matrix encodings, a monotone supplied time grid, and a weighted grid-error bound,
as required for the dynamic construction of [WangEtAl2026].

## Main statements

* `dynamic_cbmd_paper_theorem4`: supplies the budgeted computational amplification result with
  explicit input and data query envelopes.

## References

* [Wang et al., 2026][WangEtAl2026]
-/

set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

open Qatlib.Concepts.AEMeanReadout.LocalAEBackend
open Qatlib.Concepts.CoherentSim.CoherentOAA Qatlib.Foundations.InstrumentCore.ProjectiveMeasurementLaws Qatlib.Foundations.OperatorErrors.OperatorError
open Qatlib.Concepts.CoherentSim.CoherentOAA.SignalProcessing
open Qatlib.Concepts.InteractionEvo.DysonGrid
open Qatlib.Concepts.InteractionEvo.MeanDerivGrid.DysonMeanDerivativeGrid
open Qatlib.Concepts.LchsSimulation.StaticLchs Qatlib.Foundations.PureStateMath.Reflection
open Qatlib.Concepts.LcuPostselect.ScaledLCU
open Qatlib.Concepts.LocalMachine.LocalTransport
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.QsvtCore.QueryLowerBound
open Qatlib.Concepts.SharedAncilla.AncillaProduct
open Qatlib.Concepts.SignalPrimitive.HermitianQSVT
open Qatlib.Concepts.SpectralReadout.PhaseReadout Qatlib.Foundations.InstrumentCore.Measurement
open Qatlib.Concepts.SpectralSketch.SpectrumPerturb
open Qatlib.Concepts.TrotterFormula.SuzukiFourth
open Qatlib.Foundations.BornMetrics.EventProbability
open Qatlib.Concepts.Execution.WorkspaceCP
open Qatlib.Foundations.InstrumentCore.ProjectiveMeasurement
open Qatlib.Concepts.QueryWordCore.AdjointCircuits
open Qatlib.Foundations.QueryWordCore.Circuit Qatlib.Concepts.ReferenceError.MixturePaths
open Qatlib.Concepts.ReferenceError.RefTraceError
open Qatlib.Concepts.BlockEncoding.EncodingCore
open Qatlib.Concepts.FairRandomBits.FiniteCoinExecution
open Qatlib.Concepts.QspSimulation.Achievability
open Qatlib.Concepts.PhaseGeometry.Phase
open Qatlib.Concepts.LchsSimulation.TimeOrdered
open Qatlib.Concepts.LinearLearning.ConcisePipeline
open Qatlib.Concepts.TimeEvolution.TimeOrderedEvolution
open Qatlib.Concepts.BlockEncoding
open Qatlib.Concepts.BlockEncoding.Encoding
open Qatlib.Concepts.BlockEncoding.Postselection
open Qatlib.Concepts.BlockEncoding.Postselection.Encoding
open Qatlib.Concepts.WalkSearch.Spectral
open Qatlib.Concepts.BlockEncoding.LCU Qatlib.Foundations.PureStateMath.BornBridge Qatlib.Concepts.CopyEvolution.Discriminate
open Qatlib.Concepts.RandCompile.ChannelBudget
open Qatlib.Concepts.OperatorErrors.Robustness.SignalProcessing
open Qatlib.Concepts.CoherentSim.TaylorEncoding

open Qatlib.Papers.Cbmd26.Algorithms.CBMD

namespace Qatlib.Papers.Cbmd26.Results

set_option autoImplicit false
set_option maxHeartbeats 1500000
set_option synthInstance.maxSize 2048
noncomputable section
namespace CBMD
open Matrix Set
open scoped BigOperators Matrix.Norms.L2Operator ComplexOrder ENNReal
variable {Anc I : Type} [Fintype Anc] [DecidableEq Anc] [Fintype I] [DecidableEq I]
local instance cbmdDynamicCBMDPaperTheoremInstance1 (Anc : Type) [DecidableEq Anc] : DecidableEq (DynamicSampleAnc Anc) :=
  inferInstanceAs (DecidableEq (Bool × (Bool × Anc)))
local instance cbmdDynamicCBMDPaperTheoremInstance2 (T : Type) [DecidableEq T] : DecidableEq (DynamicOriginalLabels T) :=
  inferInstanceAs (DecidableEq (T × (Bool × (Bool × Bool))))
local instance cbmdDynamicCBMDPaperTheoremInstance3 (Anc J : Type) (K : ℕ) [DecidableEq Anc] [DecidableEq J] :
    DecidableEq (DynamicFreshStored Anc J K) :=
  inferInstanceAs (DecidableEq (TaylorWordLabel J K × FreshSignals (DynamicSampleAnc Anc) K))
local instance cbmdDynamicCBMDPaperTheoremInstance4 (F Anc J I : Type) (K : ℕ) [DecidableEq F] [DecidableEq Anc]
    [DecidableEq J] [DecidableEq I] : DecidableEq (DynamicFreshFinalSpace F Anc J I K) :=
  inferInstanceAs (DecidableEq (Bool × ((DynamicOriginalLabels (DynamicFreshStored Anc J K) × F) × (J × (Anc × I)))))
local instance cbmdDynamicCBMDPaperTheoremInstance5 (F Anc J : Type) (K : ℕ) [DecidableEq F] [DecidableEq Anc]
    [DecidableEq J] : DecidableEq (DynamicFreshAux F Anc J K) :=
  inferInstanceAs (DecidableEq (Bool × ((DynamicOriginalLabels (DynamicFreshStored Anc J K) × F) × (J × Anc))))

/-- Piecewise-continuous dissipative coefficients with exact original-matrix encodings, a
monotone time grid satisfying the weighted sample-error bound, and a fixed-factor output
estimate yield a `BudgetedComputationalAmplificationResult` for the dynamic propagator. Its
explicit input and data budgets use the actual output norm, giving the dynamic preparation
statement of [Wang et al., Theorem 4][WangEtAl2026]. -/
theorem dynamic_cbmd_paper_theorem4
    (a₀ : Anc) (α T ε η c : ℝ) (hα : 0 < α) (hT : 0 < T)
    (hε : 0 < ε) (hεhalf : ε ≤ 1/2) (hη : 0 < η) (hc : 1 ≤ c)
    (τ : ℕ → ℝ) (N : ℕ) (hτ : Monotone τ) (hτ0 : τ 0 = 0) (hτN : τ N = T)
    (L H : ℝ → Matrix I I ℂ)
    (P : _root_.Qatlib.Foundations.CbmdAnalysis.Core.CBMD.FinitePiecewiseContinuousOn (fun u => (H u,L u)) 0 T)
    (hL : ∀ t ∈ Icc 0 T, (L t).PosSemidef)
    (hH : ∀ t ∈ Icc 0 T, (H t).IsHermitian)
    (U : ℝ → Matrix (Anc × I) (Anc × I) ℂ)
    (henc : ∀ t ∈ Icc 0 T, BlockEncoding (L t + Complex.I • H t) (U t)
      (tagFrame a₀ (1 : Matrix I I ℂ)) (tagFrame a₀ (1 : Matrix I I ℂ)) α 0)
    (hgrid : (∑ j, ‖staticKernelWeight α T (staticAnalyticBudget ε η) j‖ *
      ‖dynamicKernelSample P α (staticAnalyticBudget ε η) j -
        dynamicSuppliedGridSample H L τ N α T (staticAnalyticBudget ε η) j‖) ≤ ε * η / 16)
    (B : Matrix I I ℂ) (hB : B ∈ Matrix.unitaryGroup I ℂ)
    (i₀ : I) (ψ : QState I) (hprepare : ApplyGate B (Ket i₀) = ψ)
    (htarget : η ≤ ‖stateVector (P.evolution (-Complex.I) T *ᵥ ψ)‖)
    (hestimate : ‖stateVector (P.evolution (-Complex.I) T *ᵥ ψ)‖ ≤ c * η) :
    let ν := ‖stateVector (P.evolution (-Complex.I) T *ᵥ ψ)‖
    BudgetedComputationalAmplificationResult (dynamicCBMDEquiv Anc I α T N ε η)
      (dynamicCBMDCleanAux a₀ α T N ε η) (dynamicCBMDSource U τ α T N ε η)
      (dynamicCBMDWord (I := I) a₀ α T N ε η) B i₀ ψ (P.evolution (-Complex.I) T) ε η
      (c * ((4 * staticMassBudget + 1) / ν))
      ((18 * dynamicPaperQueryConstant * c * outputEstimateLogFactor c ^ 2) *
        ((1 + α*T) / ν) * Real.log (2/(ε*ν)) *
        (Real.log (2+α*T) + Real.log (2/(ε*ν)))) := by
  have halg := dynamic_cbmd_original_oracle_algorithm a₀ α T ε η hα hT hε hεhalf hη
    τ N hτ hτ0 hτN L H P hL hH U henc hgrid B hB i₀ ψ hprepare htarget
  have hψ : Normalized ψ := by
    rw [← hprepare]
    exact normalized_applyGate hB (normalized_ket i₀)
  have hν1 : ‖stateVector (P.evolution (-Complex.I) T *ᵥ ψ)‖ ≤ 1 := by
    have hv := stateVector_mulVec_norm_le (P.evolution (-Complex.I) T) ψ
    rw [(normalized_iff_stateVector_norm ψ).mp hψ, mul_one] at hv
    exact hv.trans (dynamicKernel_target_contraction P hH hL)
  have hε1 : ε ≤ 1 := by linarith
  apply computationalAmplificationResult_budget _ _ _ _ _ _ _ _ _ _ _ _ halg.1
  · exact (output_estimate_envelope_bound hη htarget hestimate
      (by linarith [staticMassBudget_ge_one] : 0 ≤ 4 * staticMassBudget + 1)).2
  · apply halg.2.2.trans
    exact dynamic_true_output_query_bound hα.le hT.le hε hε1 hη htarget hestimate hc hν1
      (by have := dynamicPaperQueryConstant_pos; positivity)

end CBMD

end
end Qatlib.Papers.Cbmd26.Results
