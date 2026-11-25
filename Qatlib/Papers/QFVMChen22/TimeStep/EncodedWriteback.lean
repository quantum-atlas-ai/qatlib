/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Papers.QFVMChen22.TimeStep.PhysicalTomography

@[expose] public section

/-!
# Implicit writeback from a block-encoded linear solve

[ChenXueChenEtAl2022], Section 3.3, reconstructs a physical correction
from its scale and a signed tomography record. A backend that prepares
only the normalized solution, as in [CostaEtAl2022], Theorem 19, can use a
fresh forward application of the block-encoded stencil to estimate the
scale. This file composes the forward success amplitude and the decoded
solution with the writeback probability bound. It assumes the solver's
state accuracy and the accuracy of the two scalar readouts.

[Published paper](https://doi.org/10.1007/s11128-022-03478-w)
-/

set_option autoImplicit false

noncomputable section

namespace Qatlib.Papers.QFVMChen22.TimeStep

open Matrix
open Qatlib.Concepts.BlockEncoding (BlockEncoding)
open Qatlib.Concepts.BlockEncoding.Postselection
open Qatlib.Concepts.BlockEncoding.Postselection.Encoding (postselectionOutput postselectionProbability)
open Qatlib.Concepts.ProbabilityCore.Concentration (eventMass)
open Qatlib.Foundations.PureStateMath (Normalized QState)
open Qatlib.Foundations.PureStateMath.BornBridge (toEuclidean_fromVec)
open Qatlib.Concepts.QRAM.AmplitudeAccess (path_amplitude_eq)
open Qatlib.Concepts.QRAM.SignedReadout
open Qatlib.Foundations.QramData.SquaredNormTree (Address Tree Valid mass read)
open Qatlib.Papers.QFVMChen22.QramStorage (Geometry Snapshot)
open scoped Classical Matrix.Norms.L2Operator

variable {depth columns : ℕ}

set_option maxHeartbeats 900000 in
/-- The fixed-length Chebyshev backend of [ChildsKothariSomma2017],
Theorem 4, supplies both the physical direction and the success amplitude
needed by the writeback of [ChenXueChenEtAl2022], Section 3.3. Its spectral
assumption bounds the distance from zero. -/
theorem cks_stencil_direction_and_scale (geometry : Geometry depth)
    (linearize : Address depth → (Fin geometry.stencilSize → ℝ) → Fin geometry.stencilSize → ℝ)
    (snapshot : Snapshot depth) (correction : Address depth → ℝ)
    (entryScale condition precision estimate readError : ℝ)
    (rowScratch : Fin geometry.stencilSize) (columnScratch : Fin columns)
    (hValid : Valid snapshot.residual) (hMass : 0 < mass snapshot.residual) (hScale : 0 < entryScale)
    (hEntry : ∀ row column,
      |stencilMatrix geometry (rowCoefficient geometry linearize snapshot) row column| ≤ entryScale)
    (hColumns : ∀ column, (geometry.affected column).dedup.length ≤ columns)
    (hEquation : stencilMatrix geometry (rowCoefficient geometry linearize snapshot) *ᵥ correction =
      read snapshot.residual)
    (hCondition : 1 < condition) (hPrecision : 0 < precision) (hHalf : precision < 1 / 2)
    (hGap : ∀ j, |(stencil_signal_hermitian geometry (rowCoefficient geometry linearize snapshot)
      (entryScale * Qatlib.Concepts.QsvtCore.PhaseExistence.sparseAlpha geometry.stencilSize columns)).eigenvalues j|
      ∈ Set.Icc condition⁻¹ 1) :
    let coefficients := rowCoefficient geometry linearize snapshot
    let scale := entryScale * Qatlib.Concepts.QsvtCore.PhaseExistence.sparseAlpha geometry.stencilSize columns
    let ψ := liftedResidual snapshot.residual
    let X := stencilSpectralInverse geometry coefficients scale
    let circuit := stencilReciprocalCircuit geometry coefficients entryScale condition precision rowScratch columnScratch
    let frame := stencilSuccessFrame condition precision depth rowScratch columnScratch
    let p := postselectionProbability circuit frame frame ψ
    let direction : QState (Address depth ⊕ Address depth) :=
      Sum.elim 0 (fun i => (normalizedStencilCorrection correction i : ℂ))
    0 < p ∧ (∃ φ, postselectionOutput circuit frame frame ψ = some φ ∧ Normalized φ ∧
      ‖stateVector φ - stateVector direction‖ ≤ 2 * (2 * precision) / ‖stateVector (X *ᵥ ψ)‖) ∧
    (|estimate - Real.sqrt p| ≤ readError →
      |solutionScale (Real.sqrt (mass snapshot.residual)) (reciprocalMass condition precision)
          scale estimate - ‖stateVector (fun i => (correction i : ℂ))‖| ≤
        (Real.sqrt (mass snapshot.residual) / scale) *
          (2 * precision + reciprocalMass condition precision * readError)) := by
  intro coefficients scale ψ X circuit frame p direction
  obtain ⟨hp, φ, hOutput, _, hNormalized, hDirection⟩ :=
    stencil_reciprocal_residual_readout geometry linearize snapshot entryScale condition precision rowScratch
      columnScratch hValid hMass hScale hEntry hColumns hCondition hPrecision hHalf hGap
  have hScale' : 0 < scale := mul_pos hScale
    (Qatlib.Concepts.QsvtCore.PhaseExistence.sparseAlpha_pos
      (Nat.zero_lt_of_lt rowScratch.isLt) (Nat.zero_lt_of_lt columnScratch.isLt))
  let x : QState (Address depth ⊕ Address depth) := Sum.elim 0 (fun i => (correction i : ℂ))
  have hExact : X *ᵥ ψ = ((scale / Real.sqrt (mass snapshot.residual) : ℝ) : ℂ) • x :=
    stencil_inverse_residual_eq_correction geometry coefficients scale condition snapshot.residual correction
      hValid hMass hScale' hEquation hCondition hGap
  have hx : ‖stateVector x‖ = ‖stateVector (fun i => (correction i : ℂ))‖ := by
    apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
    simp [x, stateVector_norm_sq, Qatlib.Foundations.PureStateMath.MeasureProb,
      Qatlib.Foundations.PureStateMath.BornProb, Fintype.sum_sum_type]
  have hIdeal : NormedSpace.normalize (stateVector (X *ᵥ ψ)) = stateVector direction := by
    let factor := scale / Real.sqrt (mass snapshot.residual)
    have hFactor : 0 < factor := div_pos hScale' (Real.sqrt_pos.2 hMass)
    have hScaled : X *ᵥ ψ = factor • x :=
      hExact.trans (RCLike.real_smul_eq_coe_smul (K := ℂ) factor x).symm
    rw [hScaled]
    change NormedSpace.normalize (factor • stateVector x) = stateVector direction
    rw [NormedSpace.normalize_smul_of_pos hFactor]
    rw [NormedSpace.normalize, hx]
    change _ = WithLp.toLp 2 direction
    rw [← WithLp.toLp_smul]
    congr 1
    funext i
    cases i <;> simp [x, direction, normalizedStencilCorrection, stateVector, toEuclidean_fromVec,
      Pi.smul_apply, RCLike.real_smul_eq_coe_smul (K := ℂ), smul_eq_mul, div_eq_inv_mul]
  refine ⟨hp, ⟨φ, hOutput, hNormalized, ?_⟩, ?_⟩
  · change ‖stateVector φ - NormedSpace.normalize (stateVector (X *ᵥ ψ))‖ ≤
      2 * (2 * precision) / ‖stateVector (X *ᵥ ψ)‖ at hDirection
    simpa only [hIdeal] using hDirection
  · intro hRead
    exact stencil_solution_scale_error geometry coefficients snapshot.residual correction
      entryScale condition precision estimate readError rowScratch columnScratch hValid hMass
      hEquation hScale hEntry hColumns hCondition hPrecision hHalf.le hGap hRead

/-- Forward application to the unit physical correction produces the
signed residual with norm equal to the residual norm divided by both scales. -/
theorem stencil_normalized_correction_forward_norm (geometry : Geometry depth)
    (coefficients : Address depth → Fin geometry.stencilSize → ℝ) (scale : ℝ)
    (residual : Tree ℝ depth) (correction : Address depth → ℝ)
    (hValid : Valid residual) (hMass : 0 < mass residual) (hScale : 0 < scale)
    (hEquation : stencilMatrix geometry coefficients *ᵥ correction = read residual)
    (hNorm : 0 < ‖stateVector (fun i => (correction i : ℂ))‖) :
    let direction : QState (Address depth ⊕ Address depth) :=
      Sum.elim 0 (fun i => (normalizedStencilCorrection correction i : ℂ))
    ‖stateVector (stencilSignal geometry coefficients scale *ᵥ direction)‖ =
      Real.sqrt (mass residual) / (scale * ‖stateVector (fun i => (correction i : ℂ))‖) := by
  intro direction
  let m := ‖stateVector (fun i => (correction i : ℂ))‖
  let r := Real.sqrt (mass residual)
  have hr : 0 < r := Real.sqrt_pos.2 hMass
  have hm : 0 < m := hNorm
  have hDirection : direction = ((m⁻¹ : ℝ) : ℂ) •
      Sum.elim (0 : Address depth → ℂ) (fun i => (correction i : ℂ)) := by
    funext i
    cases i <;> simp [direction, m, normalizedStencilCorrection, stateVector, toEuclidean_fromVec,
      Pi.smul_apply, smul_eq_mul, div_eq_inv_mul]
  have hApply : stencilSignal geometry coefficients scale *ᵥ direction =
      ((r / (scale * m) : ℝ) : ℂ) • liftedResidual residual := by
    rw [hDirection, Matrix.mulVec_smul,
      stencil_mulVec_correction geometry coefficients scale residual correction hEquation]
    funext i
    cases i with
    | inl i =>
      change ((m⁻¹ : ℝ) : ℂ) * ((read residual i / scale : ℝ) : ℂ) =
        ((r / (scale * m) : ℝ) : ℂ) *
          (Qatlib.Concepts.QRAM.AmplitudeAccess.pathAmplitude residual i : ℂ)
      rw [path_amplitude_eq residual hValid]
      have hScalar : m⁻¹ * (read residual i / scale) = r / (scale * m) * (read residual i / r) := by
        field_simp [hm.ne', hScale.ne', hr.ne']
      exact (Complex.ofReal_mul _ _).symm.trans
        ((congrArg Complex.ofReal hScalar).trans (Complex.ofReal_mul _ _))
    | inr i => simp [liftedResidual]
  rw [hApply, stateVector, WithLp.toLp_smul, norm_smul, Complex.norm_real,
    Real.norm_of_nonneg (div_nonneg hr.le (mul_nonneg hScale.le hm.le))]
  change r / (scale * m) * ‖stateVector (liftedResidual residual)‖ = _
  rw [(normalized_iff_stateVector_norm _).mp (lifted_residual_normalized residual hValid hMass), mul_one]

/-- The scaled forward success amplitude differs from the ideal output norm by
at most the encoding error and the solver's input-state error after application
of the stencil. This bound also gives positive success when the error is smaller
than the ideal output norm. -/
theorem encoded_forward_amplitude_error {H I : Type} [Fintype H] [Fintype I]
    [DecidableEq H] [DecidableEq I] {A : Matrix I I ℂ} {U : Matrix H H ℂ}
    {L R : Matrix H I ℂ} {α encodingError : ℝ}
    (encoding : BlockEncoding A U L R α encodingError) (actual ideal : QState I)
    (hActual : Normalized actual) (stateError : ℝ)
    (hState : ‖stateVector (actual - ideal)‖ ≤ stateError) :
    |α * Real.sqrt (postselectionProbability U L R actual) - ‖stateVector (A *ᵥ ideal)‖| ≤
      encodingError + ‖A‖ * stateError := by
  let a := Real.sqrt (postselectionProbability U L R actual)
  have hBlock := success_amplitude_norm_error encoding hActual
  have hStateNorm : |‖stateVector (A *ᵥ actual)‖ - ‖stateVector (A *ᵥ ideal)‖| ≤ ‖A‖ * stateError := by
    refine (abs_norm_sub_norm_le _ _).trans ?_
    have hApply := stateVector_mulVec_norm_le A (actual - ideal)
    simpa only [Matrix.mulVec_sub, stateVector, WithLp.toLp_sub] using
      hApply.trans (mul_le_mul_of_nonneg_left hState (norm_nonneg _))
  calc
    _ = |(α * a - ‖stateVector (A *ᵥ actual)‖) +
        (‖stateVector (A *ᵥ actual)‖ - ‖stateVector (A *ᵥ ideal)‖)| := by congr 1; ring
    _ ≤ _ := (abs_add_le _ _).trans (add_le_add hBlock hStateNorm)

/-- An estimated forward success amplitude controls the error of the reciprocal
scale estimate. The error includes both encoding and input-state approximation. -/
theorem encoded_forward_scale_error {H I : Type} [Fintype H] [Fintype I]
    [DecidableEq H] [DecidableEq I] {A : Matrix I I ℂ} {U : Matrix H H ℂ}
    {L R : Matrix H I ℂ} {α encodingError : ℝ}
    (encoding : BlockEncoding A U L R α encodingError) (actual ideal : QState I)
    (hActual : Normalized actual) (r m estimate stateError readError : ℝ)
    (hm : 0 < m) (hEstimate : 0 < estimate)
    (hImage : ‖stateVector (A *ᵥ ideal)‖ = r / m)
    (hState : ‖stateVector (actual - ideal)‖ ≤ stateError)
    (hRead : |estimate - Real.sqrt (postselectionProbability U L R actual)| ≤ readError) :
    |r / (α * estimate) - m| ≤ m / (α * estimate) *
      (α * readError + encodingError + ‖A‖ * stateError) := by
  let a := Real.sqrt (postselectionProbability U L R actual)
  have hMeasurement : |α * estimate - α * a| ≤ α * readError := by
    rw [← mul_sub, abs_mul, abs_of_pos encoding.normalization_pos]
    exact mul_le_mul_of_nonneg_left hRead encoding.normalization_pos.le
  have hAmplitude := encoded_forward_amplitude_error encoding actual ideal hActual stateError hState
  rw [hImage] at hAmplitude
  have he : |α * estimate - r / m| ≤ α * readError + encodingError + ‖A‖ * stateError := by
    calc
      _ = |(α * estimate - α * a) + (α * a - r / m)| := by congr 1; ring
      _ ≤ _ := (abs_add_le _ _).trans ((add_le_add hMeasurement hAmplitude).trans_eq (add_assoc _ _ _).symm)
  have hp := mul_pos encoding.normalization_pos hEstimate
  calc
    _ = |(m / (α * estimate)) * (r / m - α * estimate)| := by
      congr 1
      field_simp [hm.ne', encoding.normalization_pos.ne', hEstimate.ne']
    _ = (m / (α * estimate)) * |α * estimate - r / m| := by
      rw [abs_mul, abs_of_pos (div_pos hm hp), abs_sub_comm]
    _ ≤ _ := mul_le_mul_of_nonneg_left he (div_nonneg hm.le hp.le)

set_option maxHeartbeats 1000000 in
/-- A normalized solution backend for the encoded stencil gives a physical
step using the forward amplitude for scale and a separate calibrated
signed tomography transcript for the direction. -/
theorem encoded_stencil_writeback_failure_le {H I : Type} [Fintype H] [Fintype I]
    [DecidableEq H] [DecidableEq I]
    (P : TomographyPreparation depth I) (geometry : Geometry depth)
    (localRhs : Address depth → (Fin geometry.stencilSize → ℝ) → ℝ) (snapshot : Snapshot depth)
    (coefficients : Address depth → Fin geometry.stencilSize → ℝ) (scale : ℝ)
    (correction : Address depth → ℝ)
    (hValid : Valid snapshot.residual) (hMass : 0 < mass snapshot.residual) (hScale : 0 < scale)
    (hEquation : stencilMatrix geometry coefficients *ᵥ correction = read snapshot.residual)
    (hNorm : 0 < ‖stateVector (fun i => (correction i : ℂ))‖)
    {U : Matrix H H ℂ} {L R : Matrix H (Address depth ⊕ Address depth) ℂ}
    {α encodingError : ℝ} (encoding : BlockEncoding (stencilSignal geometry coefficients scale) U L R α encodingError)
    (ψ : QState (Address depth ⊕ Address depth)) (hψ : Normalized ψ)
    (estimate calibration stateError readError calibrationError tolerance failure : ℝ)
    (hEstimate : 0 < estimate) (hCalibration : 0 ≤ calibration)
    (hTolerance : 0 < tolerance) (hFailure : 0 < failure)
    (hRead : |estimate - Real.sqrt (postselectionProbability U L R ψ)| ≤ readError)
    (hForwardState : ‖stateVector (ψ - Sum.elim (0 : Address depth → ℂ)
      (fun i => (normalizedStencilCorrection correction i : ℂ)))‖ ≤ stateError)
    (hTomographyState : ‖toEuclidean_fromVec
      (P.decodedState - embeddedDirection P.place (normalizedStencilCorrection correction))‖ ≤ stateError)
    (hCalibrationError : |P.successProbability - calibration| /
      (P.successProbability + calibration) ≤ calibrationError) :
    let m := ‖stateVector (fun i => (correction i : ℂ))‖
    let estimateNorm := (Real.sqrt (mass snapshot.residual) / scale) / (α * estimate)
    let scaleError := m / (α * estimate) * (α * readError + encodingError +
      ‖stencilSignal geometry coefficients scale‖ * stateError)
    let shots := tomographyShots depth tolerance failure
    let budget := scaleError + m * ((1 + Real.sqrt 2) * tolerance)
    eventMass (P.transcript calibration hCalibration shots shots) (fun record =>
      physicalTomographyFailure geometry localRhs snapshot correction estimateNorm budget
        (List.ofFn record.1) (List.ofFn record.2)) ≤
      failure + shots * stateError + shots * (stateError + 2 * calibrationError) := by
  intro m estimateNorm scaleError shots budget
  have hImage := stencil_normalized_correction_forward_norm geometry coefficients scale snapshot.residual
    correction hValid hMass hScale hEquation hNorm
  have hImage' : ‖stateVector ((stencilSignal geometry coefficients scale) *ᵥ
      Sum.elim (0 : Address depth → ℂ) (fun i => (normalizedStencilCorrection correction i : ℂ)))‖ =
        (Real.sqrt (mass snapshot.residual) / scale) / m := by
    rw [div_div]
    exact hImage
  have hEst := encoded_forward_scale_error encoding ψ _ hψ (Real.sqrt (mass snapshot.residual) / scale)
    m estimate stateError readError hNorm hEstimate hImage' hForwardState hRead
  exact calibrated_physical_writeback_failure_le P geometry localRhs snapshot correction
    calibration hCalibration estimateNorm scaleError stateError calibrationError tolerance failure
    hTolerance hFailure hNorm hEst hTomographyState hCalibrationError

end Qatlib.Papers.QFVMChen22.TimeStep
