/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.Cbmd26.Algorithms.StaticFinalQueryBudget
set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

open Qatlib.Concepts.AEMeanReadout.LocalAEBackend
open Qatlib.Concepts.CoherentSim.CoherentOAA
open Qatlib.Foundations.InstrumentCore.ProjectiveMeasurementLaws
open Qatlib.Foundations.OperatorErrors.OperatorError
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
open Qatlib.Concepts.BlockEncoding.LCU Qatlib.Foundations.PureStateMath.BornBridge
open Qatlib.Concepts.CopyEvolution.Discriminate

namespace Qatlib.Papers.Cbmd26.Algorithms

set_option autoImplicit false
noncomputable section
namespace CBMD

def dynamicSegmentCount (Λ T : ℝ) : ℕ := max 1 ⌈2 * Λ * T⌉₊
def dynamicSimulationAccuracy (ε η : ℝ) : ℝ := ε * η / (16 * staticMassBudget)
def dynamicSegmentAccuracy (S : ℕ) (ζ : ℝ) : ℝ := ζ ^ 2 / (10 * (S : ℝ) ^ 2)
def dynamicDysonDegree (S : ℕ) (ζ : ℝ) : ℕ := dyadicOrder (dynamicSegmentAccuracy S ζ / 2)
def dynamicFineGridSize (C ξ : ℝ) : ℕ := max 1 ⌈2 * C / ξ⌉₊

theorem dynamicSegmentCount_bounds {Λ T : ℝ} (hΛ : 0 ≤ Λ) (hT : 0 ≤ T) :
    0 < dynamicSegmentCount Λ T ∧
    2 * Λ * T ≤ (dynamicSegmentCount Λ T : ℝ) ∧
    (dynamicSegmentCount Λ T : ℝ) ≤ 2 * Λ * T + 1 ∧
    Λ * (T / dynamicSegmentCount Λ T) ≤ 1 / 2 := by
  have hn : 1 ≤ dynamicSegmentCount Λ T := le_max_left _ _
  have hpos : 0 < dynamicSegmentCount Λ T := by omega
  have hl : 2 * Λ * T ≤ (dynamicSegmentCount Λ T : ℝ) :=
    (Nat.le_ceil _).trans (by exact_mod_cast (le_max_right 1 ⌈2 * Λ * T⌉₊))
  have hu : (dynamicSegmentCount Λ T : ℝ) ≤ 2 * Λ * T + 1 := by
    unfold dynamicSegmentCount
    rw [Nat.cast_max, Nat.cast_one]
    exact max_le (by nlinarith) (Nat.ceil_lt_add_one (by positivity : 0 ≤ 2 * Λ * T)).le
  refine ⟨hpos,hl,hu,?_⟩
  rw [← mul_div_assoc]
  apply (div_le_iff₀ (by exact_mod_cast hpos)).mpr
  linarith

theorem dynamicSimulationAccuracy_bounds {ε η : ℝ}
    (hε : 0 < ε) (hε1 : ε ≤ 1) (hη : 0 < η) (hη1 : η ≤ 1) :
    0 < dynamicSimulationAccuracy ε η ∧ dynamicSimulationAccuracy ε η ≤ 1 ∧
    staticAnalyticBudget ε η + ε * η / 16 +
      staticMassBudget * dynamicSimulationAccuracy ε η = ε * η / 4 := by
  have hC : 0 < staticMassBudget := lt_of_lt_of_le zero_lt_one staticMassBudget_ge_one
  have hp : ε * η ≤ 1 := by nlinarith
  unfold dynamicSimulationAccuracy staticAnalyticBudget
  refine ⟨by positivity, ?_, ?_⟩
  · apply (div_le_one (by positivity)).mpr
    linarith [staticMassBudget_ge_one]
  · field_simp
    ring

theorem dynamicSegmentAccuracy_bounds {S : ℕ} (hS : 0 < S) {ζ : ℝ}
    (hζ : 0 < ζ) (hζ1 : ζ ≤ 1) :
    0 < dynamicSegmentAccuracy S ζ ∧ dynamicSegmentAccuracy S ζ ≤ 1 := by
  have hSr : (1:ℝ) ≤ S := by exact_mod_cast hS
  unfold dynamicSegmentAccuracy
  refine ⟨by positivity, ?_⟩
  apply (div_le_one (by positivity)).mpr
  nlinarith [sq_nonneg ((S:ℝ)-1)]

theorem dynamicFineGridSize_error {C ξ : ℝ} (_hC : 0 ≤ C) (hξ : 0 < ξ) :
    0 < dynamicFineGridSize C ξ ∧ C / dynamicFineGridSize C ξ ≤ ξ / 2 := by
  have hn : 1 ≤ dynamicFineGridSize C ξ := le_max_left _ _
  have hpos : 0 < dynamicFineGridSize C ξ := by omega
  have hm : 2 * C / ξ ≤ (dynamicFineGridSize C ξ : ℝ) :=
    (Nat.le_ceil _).trans (by exact_mod_cast (le_max_right 1 ⌈2 * C / ξ⌉₊))
  refine ⟨hpos, ?_⟩
  apply (div_le_iff₀ (by exact_mod_cast hpos)).mpr
  have hmul := (div_le_iff₀ hξ).mp hm
  nlinarith

theorem dynamicDysonDegree_tail {S : ℕ} (hS : 0 < S) {ζ : ℝ}
    (hζ : 0 < ζ) (hζ1 : ζ ≤ 1) {a : ℝ} (ha : 0 ≤ a) (ha2 : a ≤ 1 / 2) :
    2 * a ^ (dynamicDysonDegree S ζ + 1) /
      ((dynamicDysonDegree S ζ + 1).factorial : ℝ) ≤ dynamicSegmentAccuracy S ζ / 2 := by
  have hξ := (dynamicSegmentAccuracy_bounds hS hζ hζ1).1
  have he := dyadicOrder_error (show 0 < dynamicSegmentAccuracy S ζ / 2 by positivity)
  have hf : (1:ℝ) ≤ ((dynamicDysonDegree S ζ + 1).factorial : ℝ) := by
    exact_mod_cast Nat.factorial_pos (dynamicDysonDegree S ζ + 1)
  calc
    _ ≤ 2 * a ^ (dynamicDysonDegree S ζ + 1) :=
      div_le_self (by positivity) hf
    _ ≤ 2 * (1/2 : ℝ) ^ (dynamicDysonDegree S ζ + 1) := by gcongr
    _ = (1/2 : ℝ) ^ dynamicDysonDegree S ζ := by rw [pow_succ]; ring
    _ ≤ _ := he

theorem dynamicDysonDegree_log_bound {S : ℕ} (hS : 0 < S) {ζ : ℝ}
    (hζ : 0 < ζ) (hζ1 : ζ ≤ 1) :
    (dynamicDysonDegree S ζ : ℝ) ≤
      Real.log (20 * (S : ℝ) ^ 2 / ζ ^ 2) / Real.log 2 + 1 := by
  have hξ := dynamicSegmentAccuracy_bounds hS hζ hζ1
  have hξpos := hξ.1
  have hi : (dynamicSegmentAccuracy S ζ / 2)⁻¹ = 20 * (S : ℝ)^2 / ζ^2 := by
    unfold dynamicSegmentAccuracy
    field_simp
    ring
  have hl : 0 ≤ Real.log (20 * (S : ℝ)^2 / ζ^2) / Real.log 2 := by
    apply div_nonneg _ (Real.log_pos (by norm_num)).le
    apply Real.log_nonneg
    rw [← hi]
    exact (one_le_inv₀ (by positivity)).mpr (by linarith)
  unfold dynamicDysonDegree dyadicOrder
  rw [hi]
  exact (Nat.ceil_lt_add_one hl).le

theorem dynamicChosen_segments_bound {α T ε η : ℝ}
    (hα : 0 ≤ α) (hT : 0 ≤ T) (hε : 0 < ε) (hε1 : ε ≤ 1)
    (hη : 0 < η) (hη1 : η ≤ 1) :
    (dynamicSegmentCount (staticKernelNormalization α (staticAnalyticBudget ε η)) T : ℝ) ≤
      15 * (1 + α * T) * Real.log (staticQueryLogConstant / (ε * η)) := by
  obtain ⟨hl,hf,_⟩ := staticChosen_log_bound ε η hε hε1 hη hη1
  have hΛ : 0 ≤ staticKernelNormalization α (staticAnalyticBudget ε η) := by
    unfold staticKernelNormalization
    exact mul_nonneg hα (by linarith [staticKernelFrequencyBound_pos (staticAnalyticBudget ε η)])
  have hu := (dynamicSegmentCount_bounds hΛ hT).2.2.1
  have hm := mul_le_mul_of_nonneg_left hf (mul_nonneg hα hT)
  unfold staticKernelNormalization at hu ⊢
  have hp : 0 ≤ α * T := mul_nonneg hα hT
  nlinarith

end CBMD

end
end Qatlib.Papers.Cbmd26.Algorithms
