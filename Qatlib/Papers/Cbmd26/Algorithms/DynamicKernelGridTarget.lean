/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.Cbmd26.Algorithms.DynamicKernelFamily
import Qatlib.Papers.Cbmd26.Algorithms.DynamicCBMDParameters
import Qatlib.Papers.Cbmd26.Algorithms.PiecewiseGridFreeze
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
open Qatlib.Concepts.BlockEncoding.Postselection.Encoding
open Qatlib.Concepts.WalkSearch.Spectral
open Qatlib.Concepts.BlockEncoding.LCU Qatlib.Foundations.PureStateMath.BornBridge Qatlib.Concepts.CopyEvolution.Discriminate
open Qatlib.Concepts.RandCompile.ChannelBudget
open Qatlib.Concepts.OperatorErrors.Robustness.SignalProcessing

namespace Qatlib.Papers.Cbmd26.Algorithms

set_option autoImplicit false
set_option maxHeartbeats 200000
noncomputable section
namespace CBMD
open Matrix Set
open scoped BigOperators Matrix.Norms.L2Operator ComplexOrder

section Weighted
variable {J I : Type} [Fintype J] [Fintype I] [DecidableEq I]

theorem weightedMatrixSum_error (c : J → ℂ) (X Y : J → Matrix I I ℂ) :
    ‖(∑ j, c j • X j) - ∑ j, c j • Y j‖ ≤ ∑ j, ‖c j‖ * ‖X j - Y j‖ := by
  rw [← Finset.sum_sub_distrib]
  simp_rw [← smul_sub]
  exact (norm_sum_le _ _).trans_eq (by simp only [norm_smul])

theorem weightedMatrixSum_uniform_error (c : J → ℂ) (X Y : J → Matrix I I ℂ)
    (ζ : ℝ) (hXY : ∀ j, ‖X j - Y j‖ ≤ ζ) :
    ‖(∑ j, c j • X j) - ∑ j, c j • Y j‖ ≤ ζ * coefficientMass c := by
  calc
    _ ≤ ∑ j, ‖c j‖ * ‖X j - Y j‖ := weightedMatrixSum_error c X Y
    _ ≤ ∑ j, ‖c j‖ * ζ := Finset.sum_le_sum
      (fun j _ => mul_le_mul_of_nonneg_left (hXY j) (norm_nonneg _))
    _ = _ := by rw [← Finset.sum_mul]; simp only [coefficientMass]; ring

end Weighted

section Grid
variable {I : Type} [Fintype I] [DecidableEq I]

def dynamicSuppliedGridSample (H L : ℝ → Matrix I I ℂ) (τ : ℕ → ℝ)
    (N : ℕ) (α T δ : ℝ) (j : StaticKernelIndex α T δ) : Matrix I I ℂ :=
  suppliedGridEvolution τ
    (fun k => H (τ k) + (staticKernelFrequency α T δ j : ℂ) • L (τ k)) N

def dynamicSuppliedGridLCU (H L : ℝ → Matrix I I ℂ) (τ : ℕ → ℝ)
    (N : ℕ) (α T δ : ℝ) : Matrix I I ℂ :=
  ∑ j, staticKernelWeight α T δ j • dynamicSuppliedGridSample H L τ N α T δ j

variable {H L : ℝ → Matrix I I ℂ} {T : ℝ}

theorem dynamicSuppliedGrid_target_error
    (P : _root_.Qatlib.Foundations.CbmdAnalysis.Core.CBMD.FinitePiecewiseContinuousOn (fun u => (H u, L u)) 0 T)
    (τ : ℕ → ℝ) (N : ℕ) (ht : 0 ≤ T)
    (hH : ∀ u ∈ Icc 0 T, (H u).IsHermitian)
    (hL : ∀ u ∈ Icc 0 T, (L u).PosSemidef) {α δ ρ : ℝ}
    (hbound : ∀ u ∈ Icc 0 T, ‖L u + Complex.I • H u‖ ≤ α)
    (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    (hgrid : (∑ j, ‖staticKernelWeight α T δ j‖ *
      ‖dynamicKernelSample P α δ j - dynamicSuppliedGridSample H L τ N α T δ j‖) ≤ ρ) :
    ‖P.evolution (-Complex.I) T - dynamicSuppliedGridLCU H L τ N α T δ‖ ≤ δ + ρ := by
  have hg : ‖dynamicKernelLCU P α δ - dynamicSuppliedGridLCU H L τ N α T δ‖ ≤ ρ :=
    (weightedMatrixSum_error (staticKernelWeight α T δ)
      (dynamicKernelSample P α δ) (dynamicSuppliedGridSample H L τ N α T δ)).trans hgrid
  exact (norm_sub_le_norm_sub_add_norm_sub _ (dynamicKernelLCU P α δ) _).trans
    (add_le_add (dynamicKernel_target_error P ht hH hL hbound hδ hδ1) hg)

theorem dynamicSuppliedGrid_chosen_target_error
    (P : _root_.Qatlib.Foundations.CbmdAnalysis.Core.CBMD.FinitePiecewiseContinuousOn (fun u => (H u, L u)) 0 T)
    (τ : ℕ → ℝ) (N : ℕ) (ht : 0 ≤ T)
    (hH : ∀ u ∈ Icc 0 T, (H u).IsHermitian)
    (hL : ∀ u ∈ Icc 0 T, (L u).PosSemidef) {α ε η : ℝ}
    (hbound : ∀ u ∈ Icc 0 T, ‖L u + Complex.I • H u‖ ≤ α)
    (hε : 0 < ε) (hε1 : ε ≤ 1) (hη : 0 < η) (hη1 : η ≤ 1)
    (hgrid : (∑ j, ‖staticKernelWeight α T (staticAnalyticBudget ε η) j‖ *
      ‖dynamicKernelSample P α (staticAnalyticBudget ε η) j -
        dynamicSuppliedGridSample H L τ N α T (staticAnalyticBudget ε η) j‖) ≤ ε * η / 16) :
    ‖P.evolution (-Complex.I) T -
      dynamicSuppliedGridLCU H L τ N α T (staticAnalyticBudget ε η)‖ ≤
      staticAnalyticBudget ε η + ε * η / 16 := by
  have hb := static_chosen_error_budgets ε η hε hε1 hη hη1
  exact dynamicSuppliedGrid_target_error P τ N ht hH hL hbound hb.1 hb.2.1 hgrid

end Grid

theorem dynamicKernel_grid_simulation_budget (α T ε η : ℝ)
    (hε : 0 < ε) (hε1 : ε ≤ 1) (hη : 0 < η) (hη1 : η ≤ 1) :
    dynamicSimulationAccuracy ε η *
        coefficientMass (staticKernelWeight α T (staticAnalyticBudget ε η)) +
      staticAnalyticBudget ε η + ε * η / 16 ≤ ε * η / 4 := by
  have hb := dynamicSimulationAccuracy_bounds hε hε1 hη hη1
  have hm : coefficientMass (staticKernelWeight α T (staticAnalyticBudget ε η)) ≤
      staticMassBudget := (staticKernel_mass_le α T (staticAnalyticBudget ε η)).trans
        (by unfold staticMassBudget; linarith)
  have he := mul_le_mul_of_nonneg_left hm hb.1.le
  nlinarith [hb.2.2]

section Implementation
variable {I : Type} [Fintype I] [DecidableEq I]
  {H L : ℝ → Matrix I I ℂ} {T : ℝ}

theorem dynamicSuppliedGrid_implementation_error
    (P : _root_.Qatlib.Foundations.CbmdAnalysis.Core.CBMD.FinitePiecewiseContinuousOn (fun u => (H u, L u)) 0 T)
    (τ : ℕ → ℝ) (N : ℕ) (ht : 0 ≤ T)
    (hH : ∀ u ∈ Icc 0 T, (H u).IsHermitian)
    (hL : ∀ u ∈ Icc 0 T, (L u).PosSemidef) {α ε η : ℝ}
    (hbound : ∀ u ∈ Icc 0 T, ‖L u + Complex.I • H u‖ ≤ α)
    (hε : 0 < ε) (hε1 : ε ≤ 1) (hη : 0 < η) (hη1 : η ≤ 1)
    (hgrid : (∑ j, ‖staticKernelWeight α T (staticAnalyticBudget ε η) j‖ *
      ‖dynamicKernelSample P α (staticAnalyticBudget ε η) j -
        dynamicSuppliedGridSample H L τ N α T (staticAnalyticBudget ε η) j‖) ≤ ε * η / 16)
    (V : StaticKernelIndex α T (staticAnalyticBudget ε η) → Matrix I I ℂ)
    (hV : ∀ j, ‖dynamicSuppliedGridSample H L τ N α T (staticAnalyticBudget ε η) j - V j‖ ≤
      dynamicSimulationAccuracy ε η) :
    ‖P.evolution (-Complex.I) T -
      ∑ j, staticKernelWeight α T (staticAnalyticBudget ε η) j • V j‖ ≤ ε * η / 4 := by
  have htgt := dynamicSuppliedGrid_chosen_target_error P τ N ht hH hL hbound hε hε1 hη hη1 hgrid
  have himpl := weightedMatrixSum_uniform_error
    (staticKernelWeight α T (staticAnalyticBudget ε η))
    (dynamicSuppliedGridSample H L τ N α T (staticAnalyticBudget ε η)) V
    (dynamicSimulationAccuracy ε η) hV
  have htri := norm_sub_le_norm_sub_add_norm_sub (P.evolution (-Complex.I) T)
    (dynamicSuppliedGridLCU H L τ N α T (staticAnalyticBudget ε η))
    (∑ j, staticKernelWeight α T (staticAnalyticBudget ε η) j • V j)
  have hbudget := dynamicKernel_grid_simulation_budget α T ε η hε hε1 hη hη1
  change ‖dynamicSuppliedGridLCU H L τ N α T (staticAnalyticBudget ε η) - _‖ ≤ _ at himpl
  linarith

end Implementation
end CBMD

end
end Qatlib.Papers.Cbmd26.Algorithms
