/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.Cbmd26.Algorithms.StaticKernelFamily
import Qatlib.Papers.Cbmd26.Algorithms.OriginalAStaticDecodedAmplification
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
open scoped Matrix.Norms.L2Operator ComplexOrder
variable {W I : Type} [Fintype W] [DecidableEq W] [Fintype I] [DecidableEq I]

theorem exact_blockEncoding_norm_bound (A : Matrix I I ℂ) (U : Matrix W W ℂ)
    (R : Matrix W I ℂ) (α : ℝ) (h : BlockEncoding A U R R α 0) : ‖A‖ ≤ α := by
  have he : A = α • compress R U R := sub_eq_zero.mp (norm_eq_zero.mp
    (le_antisymm h.error_le (norm_nonneg _)))
  rw [he, norm_smul, Real.norm_eq_abs, abs_of_pos h.normalization_pos]
  simpa using! mul_le_mul_of_nonneg_left
    (l2_norm_compress_le_one h.left_isometry h.unitary h.right_isometry) h.normalization_pos.le

theorem originalA_hermitian_part_norm_bound (L H : Matrix I I ℂ)
    (hL : L.IsHermitian) (hH : H.IsHermitian)
    (U : Matrix W W ℂ) (R : Matrix W I ℂ) (α : ℝ)
    (h : BlockEncoding (L + Complex.I • H) U R R α 0) : ‖L‖ ≤ α := by
  have hs := original_oracle_sample_blockEncoding L H hL hH U R α 0 0 h
  simp only [Complex.ofReal_zero, zero_smul, add_zero, zero_pow (by decide : 2 ≠ 0),
    Real.sqrt_one, mul_one] at hs
  exact exact_blockEncoding_norm_bound _ _ _ _ hs

theorem static_dissipative_target_norm_le_one (L H : Matrix I I ℂ)
    (hL : L.PosSemidef) (hH : H.IsHermitian) (t : ℝ) (ht : 0 ≤ t) :
    ‖NormedSpace.exp (t • (-(L + Complex.I • H)))‖ ≤ 1 := by
  have hg := _root_.Qatlib.Foundations.CbmdAnalysis.Core.CBMD.dysonPropagator_norm_le (fun _ => H) (fun _ => L)
    continuous_const continuous_const (fun _ => hH) (fun _ => hL) 0 t ht (-Complex.I)
  simpa only [_root_.Qatlib.Foundations.CbmdAnalysis.Core.CBMD.dysonPropagator_at_neg_I, _root_.Qatlib.Foundations.CbmdAnalysis.Core.CBMD.orderedEvolution_const,
    sub_zero, Complex.neg_im, Complex.I_im, max_eq_right (by norm_num : -(1:ℝ) ≤ 0),
    zero_mul, Real.exp_zero] using! hg

def staticMassBudget : ℝ :=
    1 + 5 * _root_.Qatlib.Foundations.CbmdAnalysis.Core.CBMD.integerWeightConstant
def staticAnalyticBudget (ε η : ℝ) : ℝ := ε * η / 8
def staticSampleBudget (ε η : ℝ) : ℝ := ε * η / (8 * staticMassBudget)
def staticAmplificationWindow (η : ℝ) : ℕ := ⌈8 * staticMassBudget / η⌉₊

theorem staticMassBudget_ge_one : 1 ≤ staticMassBudget := by
  unfold staticMassBudget
  have h := _root_.Qatlib.Foundations.CbmdAnalysis.Core.CBMD.integerWeightConstant_pos
  linarith

theorem static_chosen_error_budgets (ε η : ℝ) (hε : 0 < ε) (hε1 : ε ≤ 1)
    (hη : 0 < η) (hη1 : η ≤ 1) :
    0 < staticAnalyticBudget ε η ∧ staticAnalyticBudget ε η ≤ 1 ∧
    0 < staticSampleBudget ε η ∧ staticSampleBudget ε η ≤ 1 ∧
    staticSampleBudget ε η * staticMassBudget + staticAnalyticBudget ε η = ε * η / 4 := by
  have hC : 0 < staticMassBudget := lt_of_lt_of_le zero_lt_one staticMassBudget_ge_one
  have hprod : ε * η ≤ 1 := by nlinarith
  unfold staticAnalyticBudget staticSampleBudget
  refine ⟨by positivity, by linarith, by positivity, ?_, ?_⟩
  · apply (div_le_iff₀ (by positivity : 0 < 8 * staticMassBudget)).mpr
    nlinarith [staticMassBudget_ge_one]
  · field_simp
    ring

theorem static_chosen_total_error (α t ε η : ℝ) (hε : 0 < ε) (hε1 : ε ≤ 1)
    (hη : 0 < η) (hη1 : η ≤ 1) :
    staticSampleBudget ε η * coefficientMass
      (staticKernelWeight α t (staticAnalyticBudget ε η)) + staticAnalyticBudget ε η ≤ ε * η / 4 := by
  have hb := static_chosen_error_budgets ε η hε hε1 hη hη1
  have hm : coefficientMass (staticKernelWeight α t (staticAnalyticBudget ε η)) ≤ staticMassBudget :=
    (staticKernel_mass_le _ _ _).trans (by unfold staticMassBudget; linarith)
  calc
    _ ≤ staticSampleBudget ε η * staticMassBudget + staticAnalyticBudget ε η :=
      add_le_add (mul_le_mul_of_nonneg_left hm hb.2.2.1.le) le_rfl
    _ = _ := hb.2.2.2.2

theorem static_chosen_window (η : ℝ) (hη : 0 < η) (hη1 : η ≤ 1) :
    0 < staticAmplificationWindow η ∧
    8 * staticMassBudget / η ≤ (staticAmplificationWindow η : ℝ) ∧
    ((staticAmplificationWindow η : ℝ) + 1) / 2 ≤ (4 * staticMassBudget + 1) / η := by
  have hC : 0 < staticMassBudget := lt_of_lt_of_le zero_lt_one staticMassBudget_ge_one
  have hceil := Nat.le_ceil (8 * staticMassBudget / η)
  have hupper := Nat.ceil_lt_add_one (by positivity : 0 ≤ 8 * staticMassBudget / η)
  refine ⟨Nat.ceil_pos.mpr (by positivity), hceil, ?_⟩
  unfold staticAmplificationWindow
  have hη₁ : η⁻¹ ≥ 1 := (one_le_inv₀ hη).mpr hη1
  calc
    _ ≤ ((8 * staticMassBudget / η + 1) + 1) / 2 := by linarith
    _ = 4 * staticMassBudget / η + 1 := by ring
    _ ≤ (4 * staticMassBudget + 1) / η := by
      rw [add_div, one_div]
      linarith

end CBMD

end
end Qatlib.Papers.Cbmd26.Algorithms
