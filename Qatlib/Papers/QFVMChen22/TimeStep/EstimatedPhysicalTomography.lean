/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Papers.QFVMChen22.TimeStep.AdaptiveScaleReadout
public import Qatlib.Papers.QFVMChen22.TimeStep.PhysicalTomography

@[expose] public section

/-!
# Stencil writeback with actual amplitude-estimation records

The scale estimate in [ChenXueChenEtAl2022], Section 3.3, is read from
the raw staged solver's marked event. The calibration estimate uses the
coherent tomography preparation's marked event. Independent estimation
records give a joint finite law with the two retained measurement
batches. Both readout failures and both pending probabilities enter
the probability of an inaccurate physical update.

[Published paper](https://doi.org/10.1007/s11128-022-03478-w)
-/

set_option autoImplicit false
set_option synthInstance.maxSize 512

noncomputable section

namespace Qatlib.Papers.QFVMChen22.TimeStep

open Matrix
open Qatlib.Concepts.AEMeanReadout.LocalAEBackend
open Qatlib.Concepts.MonteCarloMean.FinDistBounds
open Qatlib.Concepts.ProbabilityCore.Concentration (eventMass)
open Qatlib.Concepts.QueryComplexity.AdaptiveQuery.FiniteSupport.JointTranscript (jointLaw)
open Qatlib.Concepts.QsvtCore.PhaseExistence (sparseAlpha)
open Qatlib.Foundations.PureStateMath (MeasureProb ZeroStr)
open Qatlib.Foundations.PureStateMath.BornBridge (toEuclidean_fromVec)
open Qatlib.Concepts.QRAM.SignedReadout
open Qatlib.Foundations.QramData.SquaredNormTree (Address Tree Valid mass read)
open Qatlib.Papers.QFVMChen22.QramStorage (Geometry Snapshot)
open scoped BigOperators Classical

/-- A first-coordinate event has its original mass in the independent pair law. -/
private theorem independent_pair_event_mass_fst {X Y : Type} [Fintype X] [Fintype Y]
    (p : FinDist X) (q : FinDist Y) (event : X → Prop) [DecidablePred event] :
    eventMass (p.independentPair q) (fun xy => event xy.1) = eventMass p event := by
  simp only [eventMass, Finset.sum_filter, Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro x _
  by_cases hx : event x
  · simp only [hx, ite_true, FinDist.independentPair_sum_left]
  · simp [hx]

/-- A second-coordinate event has its original mass in the independent pair law. -/
private theorem independent_pair_event_mass_snd {X Y : Type} [Fintype X] [Fintype Y]
    (p : FinDist X) (q : FinDist Y) (event : Y → Prop) [DecidablePred event] :
    eventMass (p.independentPair q) (fun xy => event xy.2) = eventMass q event := by
  simp only [eventMass, Finset.sum_filter, Fintype.sum_prod_type]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro y _
  by_cases hy : event y
  · simp only [hy, ite_true, FinDist.independentPair_sum_right]
  · simp [hy]

variable {depth n columns : ℕ}

set_option maxHeartbeats 2300000 in
/-- For the actual raw solver and a coherent tomography preparation,
choose finite-prefix estimation schedules and use their measured records
in sparse physical writeback. The expected forward-access bounds refer
to the two preparations separately. The probability bound holds for
every pair of prefix lengths. -/
theorem exists_stencil_writeback_with_adaptive_estimates {I : Type} [Fintype I] [DecidableEq I]
    (P : TomographyPreparation depth I) (geometry : Geometry depth)
    (localRhs : Address depth → (Fin geometry.stencilSize → ℝ) → ℝ)
    (snapshot : Snapshot depth)
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
    (rawError epsScale epsCal failScale failCal stateError tolerance failure : ℝ)
    (hEpsScale : 0 < epsScale) (hEpsScale1 : epsScale ≤ 1)
    (hEpsCal : 0 < epsCal) (hEpsCal1 : epsCal ≤ 1)
    (hFailScale : 0 < failScale) (hFailCal : 0 < failCal)
    (hTolerance : 0 < tolerance) (hFailure : 0 < failure)
    (hState : ‖toEuclidean_fromVec
      (P.decodedState - embeddedDirection P.place (normalizedStencilCorrection correction))‖ ≤ stateError) :
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
    let scaleError := (Real.sqrt (mass residual) * commonBinMass condition precision / scale) *
      (epsScale * Real.sqrt p + rawError)
    let shots := tomographyShots depth tolerance failure
    let budget := scaleError + ‖toEuclidean_fromVec (fun i => (correction i : ℂ))‖ *
      ((1 + Real.sqrt 2) * tolerance)
    0 < p → |Real.sqrt p - ‖toEuclidean_fromVec ideal‖| ≤ rawError →
      ∃ rs rc : ℕ,
        let pendingScale := fun N => freshHistoryPendingMass epsScale (fun _ => rs) N A seed S hA
        let pendingCal := fun N => freshHistoryPendingMass epsCal (fun _ => rc) N
          P.target P.seed P.success P.target_unitary
        (∀ Ns Nc : ℕ,
          let scaleLaw := freshHistoryLaw (fun _ => rs) Ns A seed S hA
          let calibrationLaw := freshHistoryLaw (fun _ => rc) Nc P.target P.seed P.success P.target_unitary
          let estimateLaw := scaleLaw.independentPair calibrationLaw
          let estimateNorm (ω : FreshHistory (fun _ => rs) Ns) :=
            rawStencilScaleEstimate residual scale condition precision (firstReadyEstimate epsScale (fun _ => rs) ω)
          let calibration (ω : FreshHistory (fun _ => rc) Nc) := firstReadyEstimate epsCal (fun _ => rc) ω
          let law := jointLaw estimateLaw (fun e => P.transcript (calibration e.2)
            (first_ready_estimate_mem epsCal (fun _ => rc) e.2).1 shots shots)
          eventMass law (fun record =>
            physicalTomographyFailure geometry localRhs snapshot correction (estimateNorm record.1.1) budget
              (List.ofFn record.2.1) (List.ofFn record.2.2)) ≤
            (failScale + pendingScale Ns) + (failCal + pendingCal Nc) +
              (failure + shots * stateError + shots * (stateError + 2 * epsCal))) ∧
        (∀ Ns, freshHistoryExpectedForward epsScale (fun _ => rs) Ns A seed S hA ≤
          (192 * Real.pi * (2 * (rs : ℝ) + 1)) / (epsScale * Real.sqrt p)) ∧
        (∀ Nc, freshHistoryExpectedForward epsCal (fun _ => rc) Nc P.target P.seed P.success P.target_unitary ≤
          (192 * Real.pi * (2 * (rc : ℝ) + 1)) / (epsCal * Real.sqrt P.successProbability)) ∧
        (∀ η : ℝ, 0 < η → ∃ Bs Bc : ℕ, ∀ Ns Nc, Bs < Ns → Bc < Nc →
          pendingScale Ns + pendingCal Nc < η) := by
  intro scale raw A hA seed S p ideal scaleError shots budget hp hRaw
  obtain ⟨rs, hScaleFailure, hScaleCost, hScaleTail⟩ := exists_stencil_bin_raw_scale_schedule
    geometry coefficients entryScale κ rowScratch columnScratch residual correction hValid hMass hEntryScale
    hEntry hColumns hEquation hCondition hGap hNorm width pos condition threshold precision
    rawError epsScale failScale hEpsScale hEpsScale1 hFailScale hp hRaw
  obtain ⟨rc, hCalFailure, hCalCost, hCalTail⟩ :=
    P.exists_calibration_schedule epsCal failCal hEpsCal hEpsCal1 hFailCal
  refine ⟨rs, rc, ?_, hScaleCost, hCalCost, ?_⟩
  · intro Ns Nc scaleLaw calibrationLaw estimateLaw estimateNorm calibration law
    have hScalePair : eventMass estimateLaw (fun e =>
        scaleError < |estimateNorm e.1 - ‖toEuclidean_fromVec (fun i => (correction i : ℂ))‖|) ≤
        failScale + freshHistoryPendingMass epsScale (fun _ => rs) Ns A seed S hA :=
      (independent_pair_event_mass_fst scaleLaw calibrationLaw _).le.trans (hScaleFailure Ns)
    have hCalPair : eventMass estimateLaw (fun e =>
        epsCal < |P.successProbability - calibration e.2| / (P.successProbability + calibration e.2)) ≤
        failCal + freshHistoryPendingMass epsCal (fun _ => rc) Nc P.target P.seed P.success P.target_unitary :=
      (independent_pair_event_mass_snd scaleLaw calibrationLaw _).le.trans (hCalFailure Nc)
    exact calibrated_physical_writeback_with_estimates_failure_le P geometry localRhs snapshot correction
      estimateLaw (fun e => estimateNorm e.1) (fun e => calibration e.2)
      (fun e => first_ready_estimate_mem epsCal (fun _ => rc) e.2)
      scaleError stateError epsCal tolerance failure _ _ hTolerance hFailure hEpsCal.le
      hNorm hState hScalePair hCalPair
  · intro η hη
    obtain ⟨Bs, hS⟩ := hScaleTail (η / 2) (half_pos hη)
    obtain ⟨Bc, hC⟩ := hCalTail (η / 2) (half_pos hη)
    exact ⟨Bs, Bc, fun Ns Nc hNs hNc =>
      (add_lt_add (hS Ns hNs) (hC Nc hNc)).trans_eq (add_halves η)⟩

end Qatlib.Papers.QFVMChen22.TimeStep
