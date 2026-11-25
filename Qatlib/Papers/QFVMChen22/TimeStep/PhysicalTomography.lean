/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Papers.QFVMChen22.TimeStep.PhysicalBasisReadout
public import Qatlib.Concepts.QRAM.SignedReadout.CalibratedRetry

@[expose] public section

/-!
# Physical writeback from calibrated stencil tomography

In [ChenXueChenEtAl2022], Section 3.3, the sparse increment is recovered
from the basis and interference records and multiplied by the estimated
norm. The actual record law uses the coherent solver, its reverse history,
and the empirical QRAM reference. A scale or calibration estimate can
fail with its own probability. Conditional on good estimates, the
writeback bound counts the measurement errors in both batches.

[Published paper](https://doi.org/10.1007/s11128-022-03478-w)
-/

set_option autoImplicit false
set_option synthInstance.maxSize 512

noncomputable section

namespace Qatlib.Papers.QFVMChen22.TimeStep

open Matrix
open Qatlib.Concepts.MonteCarloMean.FinDistBounds (FinDist independentSampleLaw)
open Qatlib.Concepts.ProbabilityCore.Concentration (eventMass)
open Qatlib.Concepts.ProbabilityCore.Concentration.ProbabilityInterfaces (eventMass_mono eventMass_or_le)
open Qatlib.Concepts.QueryComplexity.AdaptiveQuery.FiniteSupport.JointTranscript (jointLaw)
open Qatlib.Foundations.InstrumentCore.Measurement (PostMeasure)
open Qatlib.Foundations.PureStateMath (ApplyGate Ket MeasureProb)
open Qatlib.Foundations.PureStateMath.BornBridge (toEuclidean_fromVec)
open Qatlib.Foundations.QueryWordCore.Circuit (Run conjTranspose_mem_unitaryGroup)
open Qatlib.Concepts.QRAM.SignedReadout
open Qatlib.Foundations.QramData.SquaredNormTree (Address Tree Valid mass read)
open Qatlib.Papers.QFVMChen22.QramStorage (Geometry Snapshot)
open scoped BigOperators Classical

variable {n depth rows columns : ℕ}

/-- The staged stencil solver as a coherent preparation and a reverse-history
decoder with physical addresses on the clean right frame. -/
def stencilTomographyPreparation {N : Type} [Fintype N] [DecidableEq N]
    (rowScratch : Fin rows) (columnScratch : Fin columns)
    (width : Fin n → ℕ) (condition threshold : Fin n → ℝ) (precision : ℝ)
    (pos : ∀ t, 0 < width t)
    (C : Matrix (StencilWorkspace depth rows columns) N ℂ)
    (U : Matrix (StencilWorkspace depth rows columns) (StencilWorkspace depth rows columns) ℂ)
    (hC : Cᴴ * C = 1) (hU : Uᴴ = U) (hSq : U * U = 1)
    (target : Matrix (BinStageWorkspace width condition precision (StencilWorkspace depth rows columns))
      (BinStageWorkspace width condition precision (StencilWorkspace depth rows columns)) ℂ)
    (seed : BinStageWorkspace width condition precision (StencilWorkspace depth rows columns))
    (hTarget : target ∈ Matrix.unitaryGroup _ ℂ)
    (hp : 0 < MeasureProb (ApplyGate target (Ket seed))
      (stencilBinSuccess rowScratch columnScratch width condition precision))
    (fallback : Address depth) :
    TomographyPreparation depth (BinStageWorkspace width condition precision
      (StencilWorkspace depth rows columns)) where
  target := target
  decoder := (stencilBinPhasePreparation width condition threshold precision C U)ᴴ
  success := stencilBinSuccess rowScratch columnScratch width condition precision
  seed := seed
  place := stencilSolutionAddress rowScratch columnScratch width pos condition precision
  fallback := fallback
  target_unitary := hTarget
  decoder_unitary := conjTranspose_mem_unitaryGroup
    (stencil_bin_phase_preparation_unitary width condition threshold precision C U hC hU hSq pos)
  success_pos := hp

set_option maxHeartbeats 900000 in
/-- The normalized inverse-target bound for the staged solver controls the
decoded-state error in its coherent tomography preparation. -/
theorem stencil_tomography_error_le_of_inverse_error (geometry : Geometry depth)
    (coefficients : Address depth → Fin geometry.stencilSize → ℝ) (scale κ : ℝ)
    (rowScratch : Fin geometry.stencilSize) (columnScratch : Fin columns)
    (residual : Tree ℝ depth) (correction : Address depth → ℝ)
    (hValid : Valid residual) (hMass : 0 < mass residual) (hScale : 0 < scale)
    (hEquation : stencilMatrix geometry coefficients *ᵥ correction = read residual)
    (hCondition : 1 < κ)
    (hGap : ∀ j, |(stencil_signal_hermitian geometry coefficients scale).eigenvalues j| ∈ Set.Icc κ⁻¹ 1)
    (hNorm : 0 < ‖toEuclidean_fromVec (fun i => (correction i : ℂ))‖)
    (width : Fin n → ℕ) (pos : ∀ t, 0 < width t) (condition threshold : Fin n → ℝ) (precision : ℝ)
    (U : Matrix (StencilWorkspace depth geometry.stencilSize columns)
      (StencilWorkspace depth geometry.stencilSize columns) ℂ)
    (hC : (stencilWalkFrame depth rowScratch columnScratch)ᴴ * stencilWalkFrame depth rowScratch columnScratch = 1)
    (hU : Uᴴ = U) (hSq : U * U = 1)
    (target : Matrix (BinStageWorkspace width condition precision
      (StencilWorkspace depth geometry.stencilSize columns))
      (BinStageWorkspace width condition precision (StencilWorkspace depth geometry.stencilSize columns)) ℂ)
    (seed : BinStageWorkspace width condition precision (StencilWorkspace depth geometry.stencilSize columns))
    (hTarget : target ∈ Matrix.unitaryGroup _ ℂ)
    (hp : 0 < MeasureProb (ApplyGate target (Ket seed))
      (stencilBinSuccess rowScratch columnScratch width condition precision))
    (fallback : Address depth) (stateError : ℝ) :
    let C := stencilWalkFrame depth rowScratch columnScratch
    let raw := ApplyGate target (Ket seed)
    let S := stencilBinSuccess rowScratch columnScratch width condition precision
    let P := stencilTomographyPreparation rowScratch columnScratch width condition threshold precision
      pos C U hC hU hSq target seed hTarget hp fallback
    let ideal := seededBinState width condition precision (cleanPhaseTape width pos)
      (C *ᵥ ((commonBinMass condition precision : ℂ)⁻¹ •
        (stencilSpectralInverse geometry coefficients scale *ᵥ liftedResidual residual)))
    let decoded := Run 1 (stencilBinHistoryUncompute width condition threshold precision C U) (PostMeasure raw S)
    ‖toEuclidean_fromVec decoded - NormedSpace.normalize (toEuclidean_fromVec ideal)‖ ≤ stateError →
      ‖toEuclidean_fromVec
        (P.decodedState - embeddedDirection P.place (normalizedStencilCorrection correction))‖ ≤ stateError := by
  intro C raw S P ideal decoded hError
  have hDecode : P.decodedState = decoded :=
    (stencil_bin_history_uncompute_apply width condition threshold precision C U (PostMeasure raw S)).symm
  have hIdeal : NormedSpace.normalize (toEuclidean_fromVec ideal) =
      toEuclidean_fromVec (embeddedDirection P.place (normalizedStencilCorrection correction)) :=
    stencil_bin_inverse_target_normalize geometry coefficients scale κ rowScratch columnScratch
      residual correction hValid hMass hScale hEquation hCondition hGap hNorm width pos condition precision
  rw [hDecode]
  change ‖toEuclidean_fromVec decoded -
    toEuclidean_fromVec (embeddedDirection P.place (normalizedStencilCorrection correction))‖ ≤ _
  rwa [hIdeal] at hError

/-- At the solver's amplified success floor, the two retained batches
cost at most one hundred basis-attempt charges and two hundred
interference-attempt charges per requested shot of the respective kind. -/
theorem amplified_tomography_retry_cost_le {I : Type} [Fintype I] [DecidableEq I]
    (P : TomographyPreparation depth I) (hSuccess : 1 / 100 ≤ P.successProbability)
    (q : ℝ) (hq : q ∈ Set.Icc 0 1) (basisShots interferenceShots : ℕ)
    (basisCost interferenceCost : ℝ) (hBasis : 0 ≤ basisCost) (hInterference : 0 ≤ interferenceCost) :
    let first := independentSampleLaw fun _ : Fin basisShots => P.basisShot
    (basisShots : ℝ) * retainedShotExpectedCost P.successProbability basisCost +
      (interferenceShots : ℝ) * first.expect (fun b =>
        retainedShotExpectedCost (P.interferenceSuccessProbability q (List.ofFn b)) interferenceCost) ≤
      100 * basisShots * basisCost + 200 * interferenceShots * interferenceCost := by
  intro first
  refine (P.retained_transcript_expected_cost_le q hq basisShots interferenceShots (1 / 100)
    basisCost interferenceCost (by norm_num) hSuccess hBasis hInterference).trans_eq ?_
  ring

/-- At least one physical coordinate exceeds the error budget after writing
the signed estimates obtained from the two retained records. -/
abbrev physicalTomographyFailure (geometry : Geometry depth)
    (localRhs : Address depth → (Fin geometry.stencilSize → ℝ) → ℝ)
    (snapshot : Snapshot depth) (correction : Address depth → ℝ)
    (estimatedNorm errorBudget : ℝ) (basis : List (Address depth))
    (interference : List (Bool × Address depth)) : Prop :=
  ∃ i, errorBudget <
    |(applyCorrection geometry localRhs estimatedNorm (signedEstimates basis interference) snapshot).physical i -
      (snapshot.physical i + correction i)|

set_option maxHeartbeats 1000000 in
/-- The physical writeback failure under the actual conditional record law
charges the decoded-state error in both batches and the calibration error
in the interference batch. The norm estimate controls the update size. -/
theorem calibrated_physical_writeback_failure_le {I : Type} [Fintype I] [DecidableEq I]
    (P : TomographyPreparation depth I) (geometry : Geometry depth)
    (localRhs : Address depth → (Fin geometry.stencilSize → ℝ) → ℝ)
    (snapshot : Snapshot depth) (correction : Address depth → ℝ)
    (q : ℝ) (hq : 0 ≤ q)
    (estimatedNorm scaleError stateError calibrationError tolerance failure : ℝ)
    (hTolerance : 0 < tolerance) (hFailure : 0 < failure)
    (hNorm : 0 < ‖toEuclidean_fromVec (fun i => (correction i : ℂ))‖)
    (hScale : |estimatedNorm - ‖toEuclidean_fromVec (fun i => (correction i : ℂ))‖| ≤ scaleError)
    (hState : ‖toEuclidean_fromVec
      (P.decodedState - embeddedDirection P.place (normalizedStencilCorrection correction))‖ ≤ stateError)
    (hCal : |P.successProbability - q| / (P.successProbability + q) ≤ calibrationError) :
    let shots := tomographyShots depth tolerance failure
    let budget := scaleError + ‖toEuclidean_fromVec (fun i => (correction i : ℂ))‖ *
      ((1 + Real.sqrt 2) * tolerance)
    eventMass (P.transcript q hq shots shots) (fun records =>
      physicalTomographyFailure geometry localRhs snapshot correction estimatedNorm budget
        (List.ofFn records.1) (List.ofFn records.2)) ≤
      failure + shots * stateError + shots * (stateError + 2 * calibrationError) := by
  intro shots budget
  let direction := normalizedStencilCorrection correction
  have hDirection : ∑ i, direction i ^ 2 = 1 := normalized_stencil_correction_sum_sq correction hNorm
  have hExact (i : Address depth) :
      |direction i - correction i / ‖toEuclidean_fromVec (fun j => (correction j : ℂ))‖| ≤ 0 := by
    change |direction i - direction i| ≤ 0
    simp
  have hBasis := (P.basis_shot_tv_le direction hDirection).trans hState
  have hInterference (b : Fin shots → Address depth) (hne : List.ofFn b ≠ []) :=
    (P.interference_shot_tv_le q hq direction hDirection (List.ofFn b) hne).trans
      (add_le_add hState (mul_le_mul_of_nonneg_left hCal (by norm_num : (0 : ℝ) ≤ 2)))
  have hBound := physical_tomography_writeback_failure_le_of_shot_tv geometry localRhs snapshot
    correction direction hDirection estimatedNorm scaleError 0 tolerance failure hTolerance hFailure
    hNorm hScale hExact P.basisShot (fun b => P.interferenceShot q hq (List.ofFn b)) stateError
    (stateError + 2 * calibrationError) hBasis hInterference
  unfold TomographyPreparation.transcript
  refine (@eventMass_mono _ _ _ _ _ _ _ ?_).trans hBound
  rintro records ⟨i, hi⟩
  refine ⟨i, ?_⟩
  simpa only [add_zero, budget, toEuclidean_fromVec, Qatlib.Concepts.BlockEncoding.Postselection.stateVector] using hi

/-- An event's mass is independent of which decision procedure supplies its
finite filter. -/
private theorem event_mass_decision_eq {R : Type} [Fintype R] (law : FinDist R) (event : R → Prop)
    (x y : DecidablePred event) : @eventMass R _ law event x = @eventMass R _ law event y :=
  congrArg (@eventMass R _ law event) (Subsingleton.elim x y)

set_option maxHeartbeats 1200000 in
/-- Before taking tomography shots, sample the norm and calibration estimates.
Their two failure probabilities add to the conditional bound on physical
writeback. The estimates may be dependent. Every calibration used for the
interference is in the probability interval. -/
theorem calibrated_physical_writeback_with_estimates_failure_le
    {I E : Type} [Fintype I] [DecidableEq I] [Fintype E]
    (P : TomographyPreparation depth I) (geometry : Geometry depth)
    (localRhs : Address depth → (Fin geometry.stencilSize → ℝ) → ℝ)
    (snapshot : Snapshot depth) (correction : Address depth → ℝ)
    (estimateLaw : FinDist E) (normEstimate calibration : E → ℝ)
    (hCalibration : ∀ e, calibration e ∈ Set.Icc 0 1)
    (scaleError stateError calibrationError tolerance failure scaleFailure calibrationFailure : ℝ)
    (hTolerance : 0 < tolerance) (hFailure : 0 < failure) (hCalError : 0 ≤ calibrationError)
    (hNorm : 0 < ‖toEuclidean_fromVec (fun i => (correction i : ℂ))‖)
    (hState : ‖toEuclidean_fromVec
      (P.decodedState - embeddedDirection P.place (normalizedStencilCorrection correction))‖ ≤ stateError)
    (hScaleFailure : eventMass estimateLaw (fun e =>
      scaleError < |normEstimate e - ‖toEuclidean_fromVec (fun i => (correction i : ℂ))‖|) ≤ scaleFailure)
    (hCalibrationFailure : eventMass estimateLaw (fun e => calibrationError <
      |P.successProbability - calibration e| / (P.successProbability + calibration e)) ≤ calibrationFailure) :
    let shots := tomographyShots depth tolerance failure
    let budget := scaleError + ‖toEuclidean_fromVec (fun i => (correction i : ℂ))‖ *
      ((1 + Real.sqrt 2) * tolerance)
    let law := jointLaw estimateLaw (fun e => P.transcript (calibration e) (hCalibration e).1 shots shots)
    eventMass law (fun record =>
      physicalTomographyFailure geometry localRhs snapshot correction (normEstimate record.1) budget
        (List.ofFn record.2.1) (List.ofFn record.2.2)) ≤
      scaleFailure + calibrationFailure +
        (failure + shots * stateError + shots * (stateError + 2 * calibrationError)) := by
  intro shots budget law
  let scaleBad (e : E) := scaleError < |normEstimate e - ‖toEuclidean_fromVec (fun i => (correction i : ℂ))‖|
  let calibrationBad (e : E) :=
    calibrationError < |P.successProbability - calibration e| / (P.successProbability + calibration e)
  let fiber (e : E) := P.transcript (calibration e) (hCalibration e).1 shots shots
  let bad (z : E × ((Fin shots → Address depth) × (Fin shots → Bool × Address depth))) :=
    physicalTomographyFailure geometry localRhs snapshot correction (normEstimate z.1) budget
      (List.ofFn z.2.1) (List.ofFn z.2.2)
  let allowance := failure + shots * stateError + shots * (stateError + 2 * calibrationError)
  have hNonneg : 0 ≤ allowance := by
    have hErr := (norm_nonneg _).trans hState
    dsimp only [allowance]
    positivity
  have hOr := @eventMass_or_le E _ estimateLaw scaleBad calibrationBad
    (fun e => Classical.propDecidable (scaleBad e)) (fun e => Classical.propDecidable (calibrationBad e))
  have hUnion : @eventMass _ _ estimateLaw (fun e => scaleBad e ∨ calibrationBad e)
      (fun e => Classical.propDecidable (scaleBad e ∨ calibrationBad e)) ≤
      scaleFailure + calibrationFailure :=
    (event_mass_decision_eq _ _ _ _).trans_le (hOr.trans (add_le_add
      ((event_mass_decision_eq estimateLaw scaleBad _ _).trans_le hScaleFailure)
      ((event_mass_decision_eq estimateLaw calibrationBad _ _).trans_le hCalibrationFailure)))
  have hEach (e : E) (he : ¬ (scaleBad e ∨ calibrationBad e)) :
      @eventMass _ _ (fiber e) (fun b => bad (e, b)) (fun b => Classical.propDecidable (bad (e, b))) ≤ allowance := by
    have hScale : |normEstimate e - ‖toEuclidean_fromVec (fun i => (correction i : ℂ))‖| ≤ scaleError :=
      le_of_not_gt (fun h => he (Or.inl h))
    have hCal : |P.successProbability - calibration e| / (P.successProbability + calibration e) ≤
        calibrationError := le_of_not_gt (fun h => he (Or.inr h))
    exact (event_mass_decision_eq _ _ _ _).trans_le
      (calibrated_physical_writeback_failure_le P geometry localRhs snapshot correction
        (calibration e) (hCalibration e).1 (normEstimate e) scaleError stateError calibrationError
        tolerance failure hTolerance hFailure hNorm hScale hState hCal)
  have hJoint := joint_event_le estimateLaw fiber (fun e => scaleBad e ∨ calibrationBad e) bad
    allowance hNonneg hEach
  change eventMass (jointLaw estimateLaw fiber) bad ≤ _
  exact (event_mass_decision_eq _ _ _ _).trans_le
    (hJoint.trans (add_le_add hUnion le_rfl))

end Qatlib.Papers.QFVMChen22.TimeStep
