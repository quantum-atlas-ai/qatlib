/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Foundations.CbmdAnalysis.Core.KernelSeriesIdentity
import Qatlib.Foundations.CbmdAnalysis.Core.StaticDyson
import Qatlib.Foundations.CbmdAnalysis.Core.KernelWeightPositive
import Qatlib.Papers.Cbmd26.Algorithms.InputBridge
set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

open Qatlib.Concepts.CoherentSim.CoherentOAA Qatlib.Foundations.InstrumentCore.ProjectiveMeasurementLaws Qatlib.Foundations.OperatorErrors.OperatorError
open Qatlib.Concepts.LchsSimulation.StaticLchs Qatlib.Foundations.PureStateMath.Reflection
open Qatlib.Concepts.LcuPostselect.ScaledLCU
open Qatlib.Foundations.PureStateMath
open Qatlib.Foundations.InstrumentCore.Measurement
open Qatlib.Concepts.TrotterFormula.SuzukiFourth
open Qatlib.Foundations.BornMetrics.EventProbability
open Qatlib.Concepts.Execution.WorkspaceCP
open Qatlib.Foundations.InstrumentCore.ProjectiveMeasurement
open Qatlib.Foundations.QueryWordCore.Circuit
open Qatlib.Concepts.ReferenceError.RefTraceError
open Qatlib.Concepts.BlockEncoding.EncodingCore
open Qatlib.Concepts.PhaseGeometry.Phase
open Qatlib.Concepts.BlockEncoding
open Qatlib.Concepts.BlockEncoding.Postselection.Encoding
open Qatlib.Concepts.BlockEncoding.LCU Qatlib.Foundations.PureStateMath.BornBridge

namespace Qatlib.Papers.Cbmd26.Algorithms

set_option autoImplicit false
set_option maxHeartbeats 600000
noncomputable section
namespace CBMD
open Matrix
open scoped BigOperators Matrix.Norms.L2Operator ComplexOrder

def staticKernelOrder (δ : ℝ) : ℕ :=
    _root_.Qatlib.Foundations.CbmdAnalysis.Core.CBMD.kernelOrder (δ / 2)
def staticKernelSpacing (α t δ : ℝ) : ℝ :=
  _root_.Qatlib.Foundations.CbmdAnalysis.Core.CBMD.kernelSpacing (t * α) (δ / 2) (staticKernelOrder δ)
def staticKernelCutoff (α t δ : ℝ) : ℕ :=
  _root_.Qatlib.Foundations.CbmdAnalysis.Core.CBMD.kernelCutoff (staticKernelSpacing α t δ) (δ / 2)
abbrev StaticKernelIndex (α t δ : ℝ) :=
  {k : ℤ // k ∈ Finset.Icc (-(staticKernelCutoff α t δ : ℤ)) (staticKernelCutoff α t δ)}
def staticKernelZero (α t δ : ℝ) : StaticKernelIndex α t δ := ⟨0, by simp⟩
def staticKernelFrequency (α t δ : ℝ) (k : StaticKernelIndex α t δ) : ℝ :=
  (k.val : ℝ) / staticKernelSpacing α t δ
def staticKernelWeight (α t δ : ℝ) (k : StaticKernelIndex α t δ) : ℂ :=
  _root_.Qatlib.Foundations.CbmdAnalysis.Core.CBMD.integerWeight (staticKernelOrder δ) (staticKernelSpacing α t δ)
    (staticKernelFrequency α t δ k)
def staticKernelFrequencyBound (δ : ℝ) : ℝ :=
  2 * max 0 (Real.log (_root_.Qatlib.Foundations.CbmdAnalysis.Core.CBMD.kernelTailConstant / (δ / 2)) / 2) + 5
def staticKernelNormalization (α δ : ℝ) : ℝ := α * (1 + staticKernelFrequencyBound δ)

theorem staticKernelSpacing_ge_one (α t δ : ℝ) : 1 ≤ staticKernelSpacing α t δ :=
  _root_.Qatlib.Foundations.CbmdAnalysis.Core.CBMD.kernelSpacing_ge_one _ _ _

theorem staticKernel_mass_pos (α t δ : ℝ) : 0 < coefficientMass (staticKernelWeight α t δ) :=
  _root_.Qatlib.Foundations.CbmdAnalysis.Core.CBMD.integerWeight_attached_mass_pos _
    (lt_of_lt_of_le (by norm_num) (staticKernelSpacing_ge_one α t δ)) _

theorem staticKernel_mass_le (α t δ : ℝ) :
    coefficientMass (staticKernelWeight α t δ) ≤ 5 * _root_.Qatlib.Foundations.CbmdAnalysis.Core.CBMD.integerWeightConstant := by
  unfold coefficientMass staticKernelWeight staticKernelFrequency
  rw [← Finset.sum_subtype (Finset.Icc (-(staticKernelCutoff α t δ : ℤ))
    (staticKernelCutoff α t δ)) (fun _ => Iff.rfl)
    (fun k : ℤ => ‖_root_.Qatlib.Foundations.CbmdAnalysis.Core.CBMD.integerWeight (staticKernelOrder δ)
      (staticKernelSpacing α t δ) ((k : ℝ) / staticKernelSpacing α t δ)‖)]
  exact _root_.Qatlib.Foundations.CbmdAnalysis.Core.CBMD.integerWeight_lattice_norm_sum_le _
      (staticKernelSpacing_ge_one α t δ) _

theorem staticKernelFrequencyBound_pos (δ : ℝ) : 0 < staticKernelFrequencyBound δ := by
  unfold staticKernelFrequencyBound
  positivity

theorem staticKernel_frequency_lt (α t δ : ℝ) (k : StaticKernelIndex α t δ) :
    |staticKernelFrequency α t δ k| < staticKernelFrequencyBound δ :=
  _root_.Qatlib.Foundations.CbmdAnalysis.Core.CBMD.kernelRetained_frequency_lt (staticKernelSpacing_ge_one α t δ) (δ / 2) k.val k.property

theorem staticKernelNormalization_pos {α : ℝ} (hα : 0 < α) (δ : ℝ) :
    0 < staticKernelNormalization α δ := by
  unfold staticKernelNormalization
  exact mul_pos hα (by linarith [staticKernelFrequencyBound_pos δ])

theorem staticKernel_normalization_bound {α : ℝ} (hα : 0 < α) (t δ : ℝ)
    (k : StaticKernelIndex α t δ) :
    α * Real.sqrt (1 + staticKernelFrequency α t δ k ^ 2) ≤ staticKernelNormalization α δ := by
  have hf := (staticKernel_frequency_lt α t δ k).le
  have hsq : Real.sqrt (1 + staticKernelFrequency α t δ k ^ 2) ≤
      1 + |staticKernelFrequency α t δ k| := by
    apply Real.sqrt_le_iff.mpr
    constructor
    · positivity
    · nlinarith [sq_abs (staticKernelFrequency α t δ k), abs_nonneg (staticKernelFrequency α t δ k)]
  exact mul_le_mul_of_nonneg_left (hsq.trans (by linarith)) hα.le

theorem staticKernel_card (α t δ : ℝ) :
    Fintype.card (StaticKernelIndex α t δ) = 2 * staticKernelCutoff α t δ + 1 := by
  rw [Fintype.card_coe]
  exact _root_.Qatlib.Foundations.CbmdAnalysis.Core.CBMD.kernelCutoff_card _ _

theorem staticKernel_card_log_bound {α t δ : ℝ} (hα : 0 < α) (ht : 0 ≤ t)
    (hδ : 0 < δ) (hδ1 : δ ≤ 1) :
    let M :=
        max 0 (Real.log (_root_.Qatlib.Foundations.CbmdAnalysis.Core.CBMD.kernelTailConstant / (δ / 2)) / 2) + 2
    (Fintype.card (StaticKernelIndex α t δ) : ℝ) <
      4 * (1 + (t * α + Real.log (_root_.Qatlib.Foundations.CbmdAnalysis.Core.CBMD.kernelAuxiliaryConstant / (δ / 2)) + M) /
        (2 * Real.pi)) * M + 3 := by
  have h :=
      _root_.Qatlib.Foundations.CbmdAnalysis.Core.CBMD.kernelLCU_card_log_bound (t * α)
      (mul_nonneg ht hα.le) hδ hδ1
  simpa only [StaticKernelIndex, Fintype.card_coe, staticKernelCutoff,
    staticKernelSpacing, staticKernelOrder] using! h

section Matrices
variable {I : Type} [Fintype I] [DecidableEq I]

def staticKernelLCU (α t δ : ℝ) (H L : Matrix I I ℂ) : Matrix I I ℂ :=
  ∑ k : StaticKernelIndex α t δ, staticKernelWeight α t δ k •
    NormedSpace.exp ((-Complex.I * (t : ℂ)) •
      (H + (staticKernelFrequency α t δ k : ℂ) • L))

theorem staticKernelLCU_eq_integerLCU (α t δ : ℝ) (H L : Matrix I I ℂ) :
    staticKernelLCU α t δ H L =
      _root_.Qatlib.Foundations.CbmdAnalysis.Core.CBMD.integerLCUSum (staticKernelOrder δ) (staticKernelSpacing α t δ)
        (staticKernelCutoff α t δ) (_root_.Qatlib.Foundations.CbmdAnalysis.Core.CBMD.dysonPropagator (fun _ => H) (fun _ => L) 0 t) := by
  unfold staticKernelLCU staticKernelWeight staticKernelFrequency
  rw [← Finset.sum_subtype (Finset.Icc (-(staticKernelCutoff α t δ : ℤ))
    (staticKernelCutoff α t δ)) (fun _ => Iff.rfl)
    (fun k : ℤ => _root_.Qatlib.Foundations.CbmdAnalysis.Core.CBMD.integerWeight (staticKernelOrder δ)
      (staticKernelSpacing α t δ) ((k : ℝ) / staticKernelSpacing α t δ) •
      NormedSpace.exp ((-Complex.I * (t : ℂ)) •
        (H + (((k : ℝ) / staticKernelSpacing α t δ : ℝ) : ℂ) • L)))]
  simp only [_root_.Qatlib.Foundations.CbmdAnalysis.Core.CBMD.integerLCUSum, _root_.Qatlib.Foundations.CbmdAnalysis.Core.CBMD.integerSample,
    _root_.Qatlib.Foundations.CbmdAnalysis.Core.CBMD.dysonPropagator_const_eq_exp, sub_zero]

theorem staticKernel_dyson_growth (H L : Matrix I I ℂ)
    (hH : H.IsHermitian) (hL : L.PosSemidef) {α t : ℝ}
    (hbound : ‖L‖ ≤ α) (ht : 0 ≤ t) (z : ℂ) :
    ‖_root_.Qatlib.Foundations.CbmdAnalysis.Core.CBMD.dysonPropagator (fun _ => H) (fun _ => L) 0 t z‖ ≤
      Real.exp (max z.im 0 * (t * α)) := by
  have h := _root_.Qatlib.Foundations.CbmdAnalysis.Core.CBMD.dysonPropagator_norm_le (fun _ => H) (fun _ => L)
    continuous_const continuous_const (fun _ => hH) (fun _ => hL) 0 t ht z
  simp only [intervalIntegral.integral_const, sub_zero, smul_eq_mul] at h
  exact h.trans (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left
    (mul_le_mul_of_nonneg_left hbound ht) (le_max_right _ _)))

theorem staticKernel_target_error (H L : Matrix I I ℂ)
    (hH : H.IsHermitian) (hL : L.PosSemidef) {α t δ : ℝ}
    (hbound : ‖L‖ ≤ α) (ht : 0 ≤ t) (hδ : 0 < δ) (hδ1 : δ ≤ 1) :
    ‖NormedSpace.exp (t • (-(L + Complex.I • H))) - staticKernelLCU α t δ H L‖ ≤ δ := by
  have he := _root_.Qatlib.Foundations.CbmdAnalysis.Core.CBMD.integerLCU_target_error_le (t * α) hδ hδ1
    (_root_.Qatlib.Foundations.CbmdAnalysis.Core.CBMD.dysonPropagator (fun _ => H) (fun _ => L) 0 t)
    (_root_.Qatlib.Foundations.CbmdAnalysis.Core.CBMD.dysonPropagator_differentiable _ _ continuous_const continuous_const 0 t)
    (staticKernel_dyson_growth H L hH hL hbound ht)
  rw [staticKernelLCU_eq_integerLCU]
  simpa only [_root_.Qatlib.Foundations.CbmdAnalysis.Core.CBMD.dysonPropagator_at_neg_I, _root_.Qatlib.Foundations.CbmdAnalysis.Core.CBMD.orderedEvolution_const,
    sub_zero, staticKernelOrder, staticKernelSpacing, staticKernelCutoff] using! he

theorem staticKernel_family (H L : Matrix I I ℂ) (hH : H.IsHermitian) (hL : L.PosSemidef)
    {α t δ : ℝ} (hα : 0 < α) (ht : 0 ≤ t) (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    (hbound : ‖L‖ ≤ α) :
    ‖NormedSpace.exp (t • (-(L + Complex.I • H))) - staticKernelLCU α t δ H L‖ ≤ δ ∧
    0 < coefficientMass (staticKernelWeight α t δ) ∧
    coefficientMass (staticKernelWeight α t δ) ≤ 5 * _root_.Qatlib.Foundations.CbmdAnalysis.Core.CBMD.integerWeightConstant ∧
    0 < staticKernelNormalization α δ ∧
    (∀ k, α * Real.sqrt (1 + staticKernelFrequency α t δ k ^ 2) ≤
      staticKernelNormalization α δ) ∧
    (∀ k, |staticKernelFrequency α t δ k| < staticKernelFrequencyBound δ) :=
  ⟨staticKernel_target_error H L hH hL hbound ht hδ hδ1,
    staticKernel_mass_pos α t δ, staticKernel_mass_le α t δ,
    staticKernelNormalization_pos hα δ, staticKernel_normalization_bound hα t δ,
    staticKernel_frequency_lt α t δ⟩
end Matrices
end CBMD

end
end Qatlib.Papers.Cbmd26.Algorithms
