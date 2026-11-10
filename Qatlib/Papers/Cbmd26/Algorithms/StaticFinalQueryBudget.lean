/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.Cbmd26.Algorithms.StaticCBMDParameters
import Qatlib.Papers.Cbmd26.Algorithms.StaticQueryBudget
set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

open Qatlib.Concepts.AEMeanReadout.LocalAEBackend
open Qatlib.Concepts.CoherentSim.CoherentOAA Qatlib.Foundations.InstrumentCore.ProjectiveMeasurementLaws Qatlib.Foundations.OperatorErrors.OperatorError
open Qatlib.Concepts.LchsSimulation.StaticLchs Qatlib.Foundations.PureStateMath.Reflection
open Qatlib.Concepts.LcuPostselect.ScaledLCU
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.SignalPrimitive.HermitianQSVT
open Qatlib.Concepts.SpectralReadout.PhaseReadout Qatlib.Foundations.InstrumentCore.Measurement
open Qatlib.Concepts.SpectralSketch.SpectrumPerturb
open Qatlib.Foundations.BornMetrics.EventProbability
open Qatlib.Foundations.InstrumentCore.ProjectiveMeasurement
open Qatlib.Foundations.QueryWordCore.Circuit
open Qatlib.Concepts.ReferenceError.RefTraceError
open Qatlib.Concepts.BlockEncoding.EncodingCore
open Qatlib.Concepts.FairRandomBits.FiniteCoinExecution
open Qatlib.Concepts.LinearLearning.ConcisePipeline
open Qatlib.Concepts.BlockEncoding.LCU Qatlib.Foundations.PureStateMath.BornBridge Qatlib.Concepts.CopyEvolution.Discriminate

namespace Qatlib.Papers.Cbmd26.Algorithms

set_option autoImplicit false
noncomputable section
namespace CBMD

def staticQueryLogConstant : ℝ :=
  1 + 16 * _root_.Qatlib.Foundations.CbmdAnalysis.Core.CBMD.kernelTailConstant + 32 * staticMassBudget + Real.exp 1

def staticSourceQueryConstant : ℝ := 224 / Real.log 2 + 24

def staticPaperLogFactor : ℝ :=
  1 + |Real.log (staticQueryLogConstant / 2)| / Real.log 2

def staticPaperQueryConstant : ℝ :=
  (4 * staticMassBudget + 1) * staticSourceQueryConstant * staticPaperLogFactor

private theorem staticQueryLogConstant_bounds :
    0 < staticQueryLogConstant ∧
    16 * _root_.Qatlib.Foundations.CbmdAnalysis.Core.CBMD.kernelTailConstant ≤ staticQueryLogConstant ∧
    32 * staticMassBudget ≤ staticQueryLogConstant ∧
    Real.exp 1 ≤ staticQueryLogConstant := by
  have hT := _root_.Qatlib.Foundations.CbmdAnalysis.Core.CBMD.kernelTailConstant_pos
  have hC := staticMassBudget_ge_one
  have hE := Real.exp_pos (1:ℝ)
  unfold staticQueryLogConstant
  constructor
  · positivity
  constructor
  · linarith
  constructor <;> linarith

theorem staticChosen_log_bound (ε η : ℝ) (hε : 0 < ε) (hε1 : ε ≤ 1)
    (hη : 0 < η) (hη1 : η ≤ 1) :
    let ℓ := Real.log (staticQueryLogConstant / (ε * η))
    1 ≤ ℓ ∧
    1 + staticKernelFrequencyBound (staticAnalyticBudget ε η) ≤ 7 * ℓ ∧
    Real.log (4 / staticSampleBudget ε η) ≤ ℓ := by
  have hp : 0 < ε * η := mul_pos hε hη
  have hp1 : ε * η ≤ 1 := by nlinarith
  obtain ⟨hC,hCT,hCM,hCE⟩ := staticQueryLogConstant_bounds
  have he : Real.exp 1 ≤ staticQueryLogConstant / (ε * η) := by
    apply (le_div_iff₀ hp).mpr
    exact (mul_le_of_le_one_right (Real.exp_pos 1).le hp1).trans hCE
  have hlog : 1 ≤ Real.log (staticQueryLogConstant / (ε * η)) := by
    simpa only [Real.log_exp] using! Real.log_le_log (Real.exp_pos 1) he
  have ht : Real.log (_root_.Qatlib.Foundations.CbmdAnalysis.Core.CBMD.kernelTailConstant / (staticAnalyticBudget ε η / 2)) ≤
      Real.log (staticQueryLogConstant / (ε * η)) := by
    rw [show _root_.Qatlib.Foundations.CbmdAnalysis.Core.CBMD.kernelTailConstant / (staticAnalyticBudget ε η / 2) =
      16 * _root_.Qatlib.Foundations.CbmdAnalysis.Core.CBMD.kernelTailConstant / (ε * η) by unfold staticAnalyticBudget; ring]
    exact Real.log_le_log (by positivity [ _root_.Qatlib.Foundations.CbmdAnalysis.Core.CBMD.kernelTailConstant_pos])
      (div_le_div_of_nonneg_right hCT hp.le)
  refine ⟨hlog, ?_, ?_⟩
  · have hm : max 0 (Real.log (_root_.Qatlib.Foundations.CbmdAnalysis.Core.CBMD.kernelTailConstant /
        (staticAnalyticBudget ε η / 2)) / 2) ≤
        Real.log (staticQueryLogConstant / (ε * η)) / 2 :=
      max_le (by linarith) (by linarith)
    unfold staticKernelFrequencyBound
    linarith
  · rw [show 4 / staticSampleBudget ε η = 32 * staticMassBudget / (ε * η) by
      unfold staticSampleBudget; field_simp; ring]
    exact Real.log_le_log (by have := staticMassBudget_ge_one; positivity)
      (div_le_div_of_nonneg_right hCM hp.le)

theorem staticChosen_source_query_bound (α t ε η : ℝ) (hα : 0 ≤ α) (ht : 0 ≤ t)
    (hε : 0 < ε) (hε1 : ε ≤ 1) (hη : 0 < η) (hη1 : η ≤ 1) :
    let δ := staticAnalyticBudget ε η
    let e := staticSampleBudget ε η
    let Λ := staticKernelNormalization α δ
    ((8 * (2 * dyadicOrder ((e / 2) / (2 * Real.exp (2 * |t * Λ|))) + 1) : ℕ) : ℝ) ≤
      staticSourceQueryConstant * (1 + α * t) *
        Real.log (staticQueryLogConstant / (ε * η)) := by
  (try dsimp only)
  let ℓ := Real.log (staticQueryLogConstant / (ε * η))
  have hb := static_chosen_error_budgets ε η hε hε1 hη hη1
  have hq := static_exponential_source_query_budget
    (t * staticKernelNormalization α (staticAnalyticBudget ε η))
    (staticSampleBudget ε η) hb.2.2.1 hb.2.2.2.1
  obtain ⟨hl,hf,he⟩ := staticChosen_log_bound ε η hε hε1 hη hη1
  change 1 ≤ ℓ at hl
  change 1 + staticKernelFrequencyBound (staticAnalyticBudget ε η) ≤ 7 * ℓ at hf
  change Real.log (4 / staticSampleBudget ε η) ≤ ℓ at he
  have hΛ : 0 ≤ staticKernelNormalization α (staticAnalyticBudget ε η) := by
    unfold staticKernelNormalization
    exact mul_nonneg hα (by linarith [staticKernelFrequencyBound_pos (staticAnalyticBudget ε η)])
  rw [abs_of_nonneg (mul_nonneg ht hΛ)] at hq ⊢
  have htΛ : t * staticKernelNormalization α (staticAnalyticBudget ε η) ≤ 7 * (α * t) * ℓ := by
    have := mul_le_mul_of_nonneg_left hf (mul_nonneg hα ht)
    unfold staticKernelNormalization
    nlinarith
  have hd : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hz : 0 ≤ α * t := mul_nonneg hα ht
  have hℓ : 0 ≤ ℓ := by linarith
  calc
    _ ≤ 16 * (2 * (t * staticKernelNormalization α (staticAnalyticBudget ε η)) +
        Real.log (4 / staticSampleBudget ε η)) / Real.log 2 + 24 := hq
    _ ≤ 224 * (1 + α * t) * ℓ / Real.log 2 + 24 := by
      have hnum : 16 * (2 * (t * staticKernelNormalization α (staticAnalyticBudget ε η)) +
          Real.log (4 / staticSampleBudget ε η)) ≤ 224 * (1 + α * t) * ℓ := by nlinarith
      have hv := (div_le_div_iff_of_pos_right hd).mpr hnum
      linarith
    _ ≤ staticSourceQueryConstant * (1 + α * t) * ℓ := by
      unfold staticSourceQueryConstant
      have h24 : 24 ≤ 24 * ((1 + α * t) * ℓ) := by nlinarith
      calc
        _ ≤ 224 * (1 + α * t) * ℓ / Real.log 2 + 24 * ((1 + α * t) * ℓ) := by linarith
        _ = _ := by ring

theorem staticChosen_log_paper_bound (ε η : ℝ) (hε : 0 < ε) (hε1 : ε ≤ 1)
    (hη : 0 < η) (hη1 : η ≤ 1) :
    Real.log (staticQueryLogConstant / (ε * η)) ≤
      staticPaperLogFactor * Real.log (2 / (ε * η)) := by
  have hp : 0 < ε * η := mul_pos hε hη
  have hp1 : ε * η ≤ 1 := by nlinarith
  have hd : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hℓ : Real.log 2 ≤ Real.log (2 / (ε * η)) := by
    apply Real.log_le_log (by norm_num)
    exact (le_div_iff₀ hp).mpr (by nlinarith)
  have hr : Real.log (staticQueryLogConstant / (ε * η)) =
      Real.log (staticQueryLogConstant / 2) + Real.log (2 / (ε * η)) := by
    rw [← Real.log_mul (by have := staticQueryLogConstant_bounds.1; positivity :
      staticQueryLogConstant / 2 ≠ 0) (by positivity : (2:ℝ) / (ε * η) ≠ 0)]
    congr 1
    ring
  rw [hr]
  have hm := mul_le_mul_of_nonneg_left hℓ
    (div_nonneg (abs_nonneg (Real.log (staticQueryLogConstant / 2))) hd.le)
  have hcancel : |Real.log (staticQueryLogConstant / 2)| / Real.log 2 * Real.log 2 =
      |Real.log (staticQueryLogConstant / 2)| := by field_simp
  rw [hcancel] at hm
  unfold staticPaperLogFactor
  nlinarith [le_abs_self (Real.log (staticQueryLogConstant / 2))]

theorem staticChosen_query_envelope_bound (α t ε η : ℝ) (hα : 0 ≤ α) (ht : 0 ≤ t)
    (hε : 0 < ε) (hε1 : ε ≤ 1) (hη : 0 < η) (hη1 : η ≤ 1) :
    let δ := staticAnalyticBudget ε η
    let e := staticSampleBudget ε η
    let Λ := staticKernelNormalization α δ
    ((4 * staticMassBudget + 1) / η) *
      ((8 * (2 * dyadicOrder ((e / 2) / (2 * Real.exp (2 * |t * Λ|))) + 1) : ℕ) : ℝ) ≤
      staticPaperQueryConstant * ((1 + α * t) / η) * Real.log (2 / (ε * η)) := by
  (try dsimp only)
  have hq := staticChosen_source_query_bound α t ε η hα ht hε hε1 hη hη1
  (try dsimp only at hq)
  have hl := staticChosen_log_paper_bound ε η hε hε1 hη hη1
  have hC : 0 ≤ (4 * staticMassBudget + 1) / η := by
    have := staticMassBudget_ge_one
    positivity
  have hS : 0 ≤ staticSourceQueryConstant := by
    unfold staticSourceQueryConstant
    exact add_nonneg (div_nonneg (by norm_num) (Real.log_pos (by norm_num)).le) (by norm_num)
  have hprod : 0 ≤ (4 * staticMassBudget + 1) / η *
      (staticSourceQueryConstant * (1 + α * t)) := by positivity
  calc
    _ ≤ ((4 * staticMassBudget + 1) / η) *
        (staticSourceQueryConstant * (1 + α * t) *
          Real.log (staticQueryLogConstant / (ε * η))) :=
      mul_le_mul_of_nonneg_left hq hC
    _ = ((4 * staticMassBudget + 1) / η *
        (staticSourceQueryConstant * (1 + α * t))) *
          Real.log (staticQueryLogConstant / (ε * η)) := by ring
    _ ≤ ((4 * staticMassBudget + 1) / η *
        (staticSourceQueryConstant * (1 + α * t))) *
          (staticPaperLogFactor * Real.log (2 / (ε * η))) :=
      mul_le_mul_of_nonneg_left hl hprod
    _ = _ := by unfold staticPaperQueryConstant; ring

theorem staticChosen_amplified_query_bound (α t ε η : ℝ) (hα : 0 ≤ α) (ht : 0 ≤ t)
    (hε : 0 < ε) (hε1 : ε ≤ 1) (hη : 0 < η) (hη1 : η ≤ 1) :
    let δ := staticAnalyticBudget ε η
    let e := staticSampleBudget ε η
    let Λ := staticKernelNormalization α δ
    (((staticAmplificationWindow η : ℝ) + 1) / 2) *
      ((8 * (2 * dyadicOrder ((e / 2) / (2 * Real.exp (2 * |t * Λ|))) + 1) : ℕ) : ℝ) ≤
      staticPaperQueryConstant * ((1 + α * t) / η) * Real.log (2 / (ε * η)) := by
  (try dsimp only)
  exact (mul_le_mul_of_nonneg_right (static_chosen_window η hη hη1).2.2
    (by positivity)).trans (staticChosen_query_envelope_bound α t ε η hα ht hε hε1 hη hη1)

theorem staticPaperQueryConstant_pos : 0 < staticPaperQueryConstant := by
  have hd : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hC := staticMassBudget_ge_one
  unfold staticPaperQueryConstant staticSourceQueryConstant staticPaperLogFactor
  positivity

end CBMD

end
end Qatlib.Papers.Cbmd26.Algorithms
