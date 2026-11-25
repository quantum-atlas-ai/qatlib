/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Papers.QFVMChen22.TimeStep.CoherentSolver
public import Qatlib.Papers.QFVMChen22.TimeStep.PhysicalBasisReadout
public import Qatlib.Concepts.QRAM.SignedReadout.AdaptiveCalibration

@[expose] public section

/-!
# Estimating the physical scale from the staged solver

[ChenXueChenEtAl2022], Section 3.3, uses the success amplitude before
amplification to recover the norm of the correction. The marked event
here is that of the coherent raw bin word on the cached residual.
The error from the decoded unnormalized packet and the relative
amplitude-estimation error both enter the physical scale estimate.

[Published paper](https://doi.org/10.1007/s11128-022-03478-w)
-/

set_option autoImplicit false
set_option synthInstance.maxSize 512

noncomputable section

namespace Qatlib.Papers.QFVMChen22.TimeStep

open Matrix
open Qatlib.Concepts.AEMeanReadout.LocalAEBackend
open Qatlib.Concepts.LchsSimulation.StaticLchs (preparedAAState)
open Qatlib.Concepts.ProbabilityCore.Concentration (eventMass)
open Qatlib.Concepts.ProbabilityCore.Concentration.ProbabilityInterfaces (eventMass_mono)
open Qatlib.Concepts.QsvtCore.PhaseExistence (sparseAlpha sparseAlpha_pos)
open Qatlib.Foundations.PureStateMath (ApplyGate Ket MeasureProb ZeroStr)
open Qatlib.Foundations.PureStateMath.BornBridge (toEuclidean_fromVec)
open Qatlib.Concepts.QRAM.SignedReadout
open Qatlib.Foundations.QramData.SquaredNormTree (Address Tree Valid mass read)
open Qatlib.Papers.QFVMChen22.QramStorage (Geometry)
open scoped Classical

variable {n depth columns : ℕ}

/-- Convert the probability estimate for the raw bin word to a physical
norm estimate using the residual, stencil, and common coefficient scales. -/
def rawStencilScaleEstimate (residual : Tree ℝ depth) (matrixScale : ℝ)
    (condition : Fin n → ℝ) (precision probabilityEstimate : ℝ) : ℝ :=
  solutionScale (Real.sqrt (mass residual)) (commonBinMass condition precision)
    matrixScale (Real.sqrt probabilityEstimate)

set_option maxHeartbeats 1100000 in
/-- Relative accuracy for the raw success probability bounds the physical
norm estimate after adding the unnormalized inverse-target error. -/
theorem stencil_bin_raw_scale_error (geometry : Geometry depth)
    (coefficients : Address depth → Fin geometry.stencilSize → ℝ) (entryScale κ : ℝ)
    (rowScratch : Fin geometry.stencilSize) (columnScratch : Fin columns)
    (residual : Tree ℝ depth) (correction : Address depth → ℝ)
    (hValid : Valid residual) (hMass : 0 < mass residual) (hEntryScale : 0 < entryScale)
    (hEquation : stencilMatrix geometry coefficients *ᵥ correction = read residual)
    (hCondition : 1 < κ)
    (hGap : ∀ j, |(stencil_signal_hermitian geometry coefficients
      (entryScale * sparseAlpha geometry.stencilSize columns)).eigenvalues j| ∈ Set.Icc κ⁻¹ 1)
    (hNorm : 0 < ‖toEuclidean_fromVec (fun i => (correction i : ℂ))‖)
    (width : Fin n → ℕ) (pos : ∀ t, 0 < width t) (condition threshold : Fin n → ℝ) (precision : ℝ)
    (q eps rawError : ℝ) (hq : 0 ≤ q) :
    let scale := entryScale * sparseAlpha geometry.stencilSize columns
    let raw := stencilBinOutput geometry coefficients entryScale rowScratch columnScratch residual
      width pos condition threshold precision
    let S := stencilBinSuccess rowScratch columnScratch width condition precision
    let p := MeasureProb raw S
    let ideal := seededBinState width condition precision (cleanPhaseTape width pos)
      (stencilWalkFrame depth rowScratch columnScratch *ᵥ ((commonBinMass condition precision : ℂ)⁻¹ •
        (stencilSpectralInverse geometry coefficients scale *ᵥ liftedResidual residual)))
    0 < p → |Real.sqrt p - ‖toEuclidean_fromVec ideal‖| ≤ rawError → |q - p| ≤ eps * p →
      |rawStencilScaleEstimate residual scale condition precision q -
        ‖toEuclidean_fromVec (fun i => (correction i : ℂ))‖| ≤
        (Real.sqrt (mass residual) * commonBinMass condition precision / scale) *
          (eps * Real.sqrt p + rawError) := by
  intro scale raw S p ideal hp hRaw hEstimate
  let r := Real.sqrt (mass residual)
  let α := commonBinMass condition precision
  let norm := ‖toEuclidean_fromVec (fun i => (correction i : ℂ))‖
  have hr : 0 < r := Real.sqrt_pos.2 hMass
  have hα : 0 < α := (common_bin_mass_bounds condition precision).1
  have hScale : 0 < scale := mul_pos hEntryScale
    (sparseAlpha_pos (Nat.zero_lt_of_lt rowScratch.isLt) (Nat.zero_lt_of_lt columnScratch.isLt))
  have hIdeal : ‖toEuclidean_fromVec ideal‖ = α⁻¹ * (scale / r) * norm :=
    (stencil_bin_inverse_target_scale geometry coefficients scale κ rowScratch columnScratch residual
      correction hValid hMass hScale hEquation hCondition hGap hNorm width pos condition precision).2.2
  have hExact : solutionScale r α scale ‖toEuclidean_fromVec ideal‖ = norm := by
    rw [hIdeal]
    unfold solutionScale
    field_simp [hr.ne', hα.ne', hScale.ne']
  have hRead := success_amplitude_error_le_of_relative hp hq hEstimate
  have hBound := solution_scale_error r α scale (Real.sqrt p) (Real.sqrt q) ‖toEuclidean_fromVec ideal‖
    rawError (eps * Real.sqrt p) (div_nonneg (mul_nonneg hr.le hα.le) hScale.le) hRaw hRead
  rw [hExact] at hBound
  exact hBound

set_option maxHeartbeats 1400000 in
/-- Run amplitude estimation on the actual raw bin word. The finite
scale readout has a physical error budget with its prescribed failure
allowance plus pending probability. The forward-access bound and
the pending tail are from that same prepared estimator. -/
theorem exists_stencil_bin_raw_scale_schedule (geometry : Geometry depth)
    (coefficients : Address depth → Fin geometry.stencilSize → ℝ) (entryScale κ : ℝ)
    (rowScratch : Fin geometry.stencilSize) (columnScratch : Fin columns)
    (residual : Tree ℝ depth) (correction : Address depth → ℝ)
    (hValid : Valid residual) (hMass : 0 < mass residual) (hEntryScale : 0 < entryScale)
    (hEntry : ∀ row column, |stencilMatrix geometry coefficients row column| ≤ entryScale)
    (hColumns : ∀ column, (geometry.affected column).dedup.length ≤ columns)
    (hEquation : stencilMatrix geometry coefficients *ᵥ correction = read residual)
    (hCondition : 1 < κ)
    (hGap : ∀ j, |(stencil_signal_hermitian geometry coefficients
      (entryScale * sparseAlpha geometry.stencilSize columns)).eigenvalues j| ∈ Set.Icc κ⁻¹ 1)
    (hNorm : 0 < ‖toEuclidean_fromVec (fun i => (correction i : ℂ))‖)
    (width : Fin n → ℕ) (pos : ∀ t, 0 < width t) (condition threshold : Fin n → ℝ) (precision : ℝ)
    (rawError eps δ : ℝ) (heps : 0 < eps) (heps1 : eps ≤ 1) (hδ : 0 < δ) :
    let scale := entryScale * sparseAlpha geometry.stencilSize columns
    let raw := stencilBinOutput geometry coefficients entryScale rowScratch columnScratch residual
      width pos condition threshold precision
    let A := stencilBinTargetPreparation geometry coefficients entryScale rowScratch columnScratch residual
      width pos condition threshold precision
    let hA := stencil_bin_target_preparation_unitary geometry coefficients entryScale rowScratch columnScratch
      residual width pos condition threshold precision hValid hEntryScale hEntry hColumns
    let seed := stencilResidualAddress rowScratch columnScratch width pos condition precision (ZeroStr depth)
    let S := stencilBinSuccess rowScratch columnScratch width condition precision
    let p := MeasureProb raw S
    let ideal := seededBinState width condition precision (cleanPhaseTape width pos)
      (stencilWalkFrame depth rowScratch columnScratch *ᵥ ((commonBinMass condition precision : ℂ)⁻¹ •
        (stencilSpectralInverse geometry coefficients scale *ᵥ liftedResidual residual)))
    let error := (Real.sqrt (mass residual) * commonBinMass condition precision / scale) *
      (eps * Real.sqrt p + rawError)
    0 < p → |Real.sqrt p - ‖toEuclidean_fromVec ideal‖| ≤ rawError →
      ∃ r : ℕ,
        (∀ N, eventMass (freshHistoryLaw (fun _ => r) N A seed S hA)
          (fun ω => error < |rawStencilScaleEstimate residual scale condition precision
            (firstReadyEstimate eps (fun _ => r) ω) - ‖toEuclidean_fromVec (fun i => (correction i : ℂ))‖|) ≤
            δ + freshHistoryPendingMass eps (fun _ => r) N A seed S hA) ∧
        (∀ N, freshHistoryExpectedForward eps (fun _ => r) N A seed S hA ≤
          (192 * Real.pi * (2 * (r : ℝ) + 1)) / (eps * Real.sqrt p)) ∧
        (∀ η : ℝ, 0 < η → ∃ B : ℕ, ∀ N, B < N →
          freshHistoryPendingMass eps (fun _ => r) N A seed S hA < η) := by
  intro scale raw A hA seed S p ideal error hp hRaw
  have hProbability : MeasureProb (preparedAAState A seed) S = p := by
    change MeasureProb (ApplyGate A (Ket seed)) S = MeasureProb raw S
    rw [show ApplyGate A (Ket seed) = raw from
      stencil_bin_target_preparation_apply geometry coefficients entryScale rowScratch columnScratch
        residual width pos condition threshold precision hValid hMass]
  have hpA : 0 < MeasureProb (preparedAAState A seed) S := by rwa [hProbability]
  obtain ⟨r, hFailure, hCost, hTail⟩ := exists_first_ready_probability_schedule eps δ heps heps1 hδ
    A seed S hA hpA
  refine ⟨r, fun N => ?_, fun N => ?_, hTail⟩
  · refine (@eventMass_mono _ _ _ _ _ _ _ ?_).trans (hFailure N)
    intro ω hBad
    refine lt_of_not_ge fun hGood => (not_lt_of_ge ?_) hBad
    have hGoodP : |firstReadyEstimate eps (fun _ => r) ω - p| ≤ eps * p := by
      rwa [← hProbability]
    exact stencil_bin_raw_scale_error geometry coefficients entryScale κ rowScratch columnScratch
      residual correction hValid hMass hEntryScale hEquation hCondition hGap hNorm width pos
      condition threshold precision (firstReadyEstimate eps (fun _ => r) ω) eps rawError
      (first_ready_estimate_mem eps (fun _ => r) ω).1 hp hRaw hGoodP
  · have hN := hCost N
    rwa [hProbability] at hN

end Qatlib.Papers.QFVMChen22.TimeStep
