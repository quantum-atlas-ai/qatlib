/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Papers.QFVMChen22.TimeStep.ReciprocalReadout
public import Qatlib.Concepts.QRAM.SignedReadout.JointError
public import Qatlib.Concepts.QRAM.SignedReadout.TranscriptStability

@[expose] public section

/-!
# Physical solution scale and sparse writeback

[ChenXueChenEtAl2022], Section 3.3, recovers a physical correction by
estimating the success amplitude and the direction of the solution.
The inverse of the lifted stencil acts on the unit residual as the
physical correction in the opposite register, with the known stencil
and residual scaling. The pre-amplification branch of the fixed-length
reciprocal circuit then gives a quantitative estimate of the physical
norm. Given a coordinate error from tomography, the same estimate
controls the error of a sparse physical writeback. The amplitude and
tomography estimates enter with their own error bounds.

[Published paper](https://doi.org/10.1007/s11128-022-03478-w)
-/

set_option autoImplicit false

noncomputable section

namespace Qatlib.Papers.QFVMChen22.TimeStep

open Matrix
open Qatlib.Concepts.BlockEncoding (BlockEncoding)
open Qatlib.Concepts.BlockEncoding.Postselection (stateVector stateVector_norm_sq)
open Qatlib.Concepts.BlockEncoding.Postselection.Encoding
open Qatlib.Concepts.MonteCarloMean.FinDistBounds (FinDist independentSampleLaw tvDist)
open Qatlib.Concepts.QsvtCore.PhaseExistence (sparseAlpha sparseAlpha_pos)
open Qatlib.Concepts.ProbabilityCore.Concentration (eventMass)
open Qatlib.Concepts.ProbabilityCore.Concentration.ProbabilityInterfaces (eventMass_mono)
open Qatlib.Concepts.QueryComplexity.AdaptiveQuery.FiniteSupport.JointTranscript (jointLaw)
open Qatlib.Foundations.PureStateMath (BornProb MeasureProb Normalized QState)
open Qatlib.Concepts.QRAM.AmplitudeAccess (path_amplitude_eq)
open Qatlib.Concepts.QRAM.SignedReadout (rescale_error signedCoordinate signedEstimates
  signedTomographyLaw tomographyShots tomography_shots_pos signed_tomography_failure_le_budget
  signed_coordinate_abs_le_one signed_estimates_length_le sum_signed_estimates_at
  basisSampleLaw interferenceSampleLaw event_mass_le_add_tv signed_tomography_transcript_tv_le)
open Qatlib.Foundations.QramData.SquaredNormTree (Address Tree Valid mass read)
open Qatlib.Papers.QFVMChen22.QramStorage (Geometry Snapshot)
open scoped BigOperators Classical

variable {depth columnSlots : ℕ}

/-- A real correction satisfying the stencil equations is mapped into the left residual block
by the scaled Hermitian stencil. -/
theorem stencil_mulVec_correction (geometry : Geometry depth)
    (coefficients : Address depth → Fin geometry.stencilSize → ℝ) (scale : ℝ)
    (residual : Tree ℝ depth) (correction : Address depth → ℝ)
    (hEquation : stencilMatrix geometry coefficients *ᵥ correction = read residual) :
    stencilSignal geometry coefficients scale *ᵥ Sum.elim 0 (fun i => (correction i : ℂ)) =
      Sum.elim (fun i => ((read residual i / scale : ℝ) : ℂ)) 0 := by
  unfold stencilSignal
  apply lift_solution_mulVec
  funext i
  change (((scale⁻¹ • stencilMatrix geometry coefficients).map Complex.ofRealHom) *ᵥ
    (Complex.ofRealHom ∘ correction)) i = _
  rw [← RingHom.map_mulVec Complex.ofRealHom]
  change (((scale⁻¹ • stencilMatrix geometry coefficients) *ᵥ correction) i : ℂ) =
    ((read residual i / scale : ℝ) : ℂ)
  rw [Matrix.smul_mulVec, hEquation, Pi.smul_apply, smul_eq_mul, div_eq_inv_mul]

/-- The lifted inverse applied to the normalized residual recovers the actual solution of the
stencil equations in the right register, with scale equal to matrix scale over residual norm. -/
theorem stencil_inverse_residual_eq_correction (geometry : Geometry depth)
    (coefficients : Address depth → Fin geometry.stencilSize → ℝ) (scale condition : ℝ)
    (residual : Tree ℝ depth) (correction : Address depth → ℝ)
    (hValid : Valid residual) (hMass : 0 < mass residual) (hScale : 0 < scale)
    (hEquation : stencilMatrix geometry coefficients *ᵥ correction = read residual)
    (hCondition : 1 < condition)
    (hGap : ∀ j, |(stencil_signal_hermitian geometry coefficients scale).eigenvalues j| ∈
      Set.Icc condition⁻¹ 1) :
    stencilSpectralInverse geometry coefficients scale *ᵥ liftedResidual residual =
      ((scale / Real.sqrt (mass residual) : ℝ) : ℂ) •
        Sum.elim (0 : Address depth → ℂ) (fun i => (correction i : ℂ)) := by
  let r := Real.sqrt (mass residual)
  let T := stencilSignal geometry coefficients scale
  let X := stencilSpectralInverse geometry coefficients scale
  let x : QState (Address depth ⊕ Address depth) :=
    Sum.elim (0 : Address depth → ℂ) (fun i => (correction i : ℂ))
  have hr : 0 < r := Real.sqrt_pos.2 hMass
  have hLoaded : T *ᵥ (((scale / r : ℝ) : ℂ) • x) = liftedResidual residual := by
    rw [Matrix.mulVec_smul,
      stencil_mulVec_correction geometry coefficients scale residual correction hEquation]
    funext i
    cases i with
    | inl i =>
      change ((scale / r : ℝ) : ℂ) • ((read residual i / scale : ℝ) : ℂ) =
        (Qatlib.Concepts.QRAM.AmplitudeAccess.pathAmplitude residual i : ℂ)
      rw [smul_eq_mul, path_amplitude_eq residual hValid i]
      change ((scale / r : ℝ) : ℂ) * ((read residual i / scale : ℝ) : ℂ) =
        ((read residual i / r : ℝ) : ℂ)
      rw [← Complex.ofReal_mul]
      congr 1
      field_simp [hScale.ne', hr.ne']
    | inr i =>
      change ((scale / r : ℝ) : ℂ) • (0 : ℂ) = 0
      exact smul_zero _
  have hInverse := (stencil_spectral_inverse_mul geometry coefficients scale condition hCondition hGap).1
  change X *ᵥ liftedResidual residual = ((scale / r : ℝ) : ℂ) • x
  rw [← hLoaded, Matrix.mulVec_mulVec, hInverse, Matrix.one_mulVec]

/-- Embedding a state in the right summand preserves its Euclidean norm. -/
private theorem norm_right_state {I : Type*} [Fintype I] (x : QState I) :
    ‖stateVector (Sum.elim (0 : I → ℂ) x)‖ = ‖stateVector x‖ := by
  apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  simp [stateVector_norm_sq, MeasureProb, BornProb, Fintype.sum_sum_type]

/-- Taking a state-vector norm after complex scaling multiplies by the scalar norm. -/
private theorem norm_smul_state {I : Type*} [Fintype I] (c : ℂ) (x : QState I) :
    ‖stateVector (c • x)‖ = ‖c‖ * ‖stateVector x‖ := by
  change ‖WithLp.toLp 2 (c • x)‖ = _
  rw [WithLp.toLp_smul, norm_smul]

/-- The pre-amplification success amplitude times a block encoding's mass approximates the
norm of the target matrix applied to the normalized input. -/
theorem success_amplitude_norm_error {H I O : Type*}
    [Fintype H] [Fintype I] [Fintype O] [DecidableEq H] [DecidableEq I] [DecidableEq O]
    {A : Matrix O I ℂ} {U : Matrix H H ℂ} {L : Matrix H O ℂ} {R : Matrix H I ℂ}
    {α ε : ℝ} (h : BlockEncoding A U L R α ε) {ψ : QState I} (hψ : Normalized ψ) :
    |α * Real.sqrt (postselectionProbability U L R ψ) - ‖stateVector (A *ᵥ ψ)‖| ≤ ε := by
  have hError := BlockEncoding.postselection_error h hψ
  have hb := (abs_norm_sub_norm_le _ _).trans hError
  rw [norm_smul, Real.norm_eq_abs, abs_of_pos h.normalization_pos] at hb
  rw [postselectionProbability_eq_norm_sq h.left_isometry,
    Real.sqrt_sq (norm_nonneg _), abs_sub_comm]
  exact hb

/-- The residual norm, matrix scale and coefficient mass convert an estimate of the
unamplified success amplitude into a physical solution norm. The error includes both Chebyshev
approximation and amplitude estimation. -/
theorem stencil_solution_scale_error (geometry : Geometry depth)
    (coefficients : Address depth → Fin geometry.stencilSize → ℝ)
    (residual : Tree ℝ depth) (correction : Address depth → ℝ)
    (entryScale condition precision estimate readError : ℝ)
    (rowScratch : Fin geometry.stencilSize) (columnScratch : Fin columnSlots)
    (hValid : Valid residual) (hMass : 0 < mass residual)
    (hEquation : stencilMatrix geometry coefficients *ᵥ correction = read residual)
    (hScale : 0 < entryScale)
    (hEntry : ∀ row column, |stencilMatrix geometry coefficients row column| ≤ entryScale)
    (hColumns : ∀ column, (geometry.affected column).dedup.length ≤ columnSlots)
    (hCondition : 1 < condition) (hPrecision : 0 < precision) (hHalf : precision ≤ 1 / 2)
    (hGap : ∀ j, |(stencil_signal_hermitian geometry coefficients
      (entryScale * sparseAlpha geometry.stencilSize columnSlots)).eigenvalues j| ∈
        Set.Icc condition⁻¹ 1)
    (hRead : let U := stencilReciprocalCircuit geometry coefficients entryScale condition precision
                  rowScratch columnScratch
             let L := stencilSuccessFrame condition precision depth rowScratch columnScratch
             |estimate - Real.sqrt (postselectionProbability U L L (liftedResidual residual))| ≤
               readError) :
    let r := Real.sqrt (mass residual)
    let α := reciprocalMass condition precision
    let scale := entryScale * sparseAlpha geometry.stencilSize columnSlots
    |solutionScale r α scale estimate - ‖stateVector (fun i => (correction i : ℂ))‖| ≤
      (r / scale) * (2 * precision + α * readError) := by
  let r := Real.sqrt (mass residual)
  let α := reciprocalMass condition precision
  let scale := entryScale * sparseAlpha geometry.stencilSize columnSlots
  let U := stencilReciprocalCircuit geometry coefficients entryScale condition precision rowScratch columnScratch
  let L := stencilSuccessFrame condition precision depth rowScratch columnScratch
  let amplitude := Real.sqrt (postselectionProbability U L L (liftedResidual residual))
  let x : QState (Address depth) := fun i => (correction i : ℂ)
  let targetNorm := ‖stateVector x‖
  have hr : 0 < r := Real.sqrt_pos.2 hMass
  have hβ : 0 < scale := mul_pos hScale
    (sparseAlpha_pos (Nat.zero_lt_of_lt rowScratch.isLt) (Nat.zero_lt_of_lt columnScratch.isLt))
  have hEncoding := stencil_reciprocal_block_encoding geometry coefficients entryScale condition precision
    rowScratch columnScratch hScale hEntry hColumns hCondition hPrecision hHalf hGap
  have hRaw := success_amplitude_norm_error hEncoding (lifted_residual_normalized residual hValid hMass)
  change |α * amplitude - ‖stateVector (stencilSpectralInverse geometry coefficients scale *ᵥ
    liftedResidual residual)‖| ≤ 2 * precision at hRaw
  rw [stencil_inverse_residual_eq_correction geometry coefficients scale condition residual correction
    hValid hMass hβ hEquation hCondition hGap, norm_smul_state, Complex.norm_real,
    Real.norm_eq_abs, abs_of_pos (div_pos hβ hr), norm_right_state] at hRaw
  have hReadScaled : |α * estimate - α * amplitude| ≤ α * readError := by
    rw [← mul_sub, abs_mul, abs_of_pos hEncoding.normalization_pos]
    exact mul_le_mul_of_nonneg_left hRead hEncoding.normalization_pos.le
  have hDiff : solutionScale r α scale estimate - targetNorm =
      (r / scale) * (α * estimate - (scale / r) * targetNorm) := by
    unfold solutionScale
    field_simp [hr.ne', hβ.ne']
  change |solutionScale r α scale estimate - targetNorm| ≤ _
  rw [hDiff, abs_mul, abs_of_pos (div_pos hr hβ)]
  apply mul_le_mul_of_nonneg_left _ (div_nonneg hr.le hβ.le)
  calc
    _ = |(α * estimate - α * amplitude) + (α * amplitude - (scale / r) * targetNorm)| := by
      congr 1
      ring
    _ ≤ |α * estimate - α * amplitude| + |α * amplitude - (scale / r) * targetNorm| :=
      abs_add_le _ _
    _ ≤ α * readError + 2 * precision := add_le_add hReadScaled hRaw
    _ = _ := add_comm _ _

/-- Given bounds on the norm estimate and the tomography coordinate, sparse writeback stays
within the corresponding combined error of the ideal physical correction. -/
theorem physical_writeback_error (geometry : Geometry depth)
    (localRhs : Address depth → (Fin geometry.stencilSize → ℝ) → ℝ)
    (snapshot : Snapshot depth) (correction : Address depth → ℝ)
    (updates : List (Address depth × ℝ)) (address : Address depth)
    (estimatedNorm scaleError directionError : ℝ)
    (hNorm : 0 < ‖stateVector (fun i => (correction i : ℂ))‖)
    (hScale : |estimatedNorm - ‖stateVector (fun i => (correction i : ℂ))‖| ≤ scaleError)
    (hEstimate : |correctionAt updates address| ≤ 1)
    (hDirection : |correctionAt updates address -
      correction address / ‖stateVector (fun i => (correction i : ℂ))‖| ≤ directionError) :
    |(applyCorrection geometry localRhs estimatedNorm updates snapshot).physical address -
      (snapshot.physical address + correction address)| ≤
      scaleError + ‖stateVector (fun i => (correction i : ℂ))‖ * directionError := by
  let r := ‖stateVector (fun i => (correction i : ℂ))‖
  change _ ≤ scaleError + r * directionError
  rw [physical_eq_add_correction, add_sub_add_left_eq_sub]
  have hCancel : r * (correction address / r) = correction address := by
    rw [mul_comm, div_mul_cancel₀ _ hNorm.ne']
  calc
    _ = |estimatedNorm * correctionAt updates address - r * (correction address / r)| := by
      rw [hCancel]
    _ ≤ |estimatedNorm - r| + r * |correctionAt updates address - correction address / r| :=
      rescale_error _ _ _ _ hNorm.le hEstimate
    _ ≤ _ := add_le_add hScale (mul_le_mul_of_nonneg_left hDirection hNorm.le)

/-- For the actual signed tomography record, the sparse physical update inherits the
scale and coordinate error bounds, including at addresses omitted by the estimator. -/
theorem physical_signed_writeback_error (geometry : Geometry depth)
    (localRhs : Address depth → (Fin geometry.stencilSize → ℝ) → ℝ)
    (snapshot : Snapshot depth) (correction : Address depth → ℝ)
    (basis : List (Address depth)) (interference : List (Bool × Address depth))
    (address : Address depth) (estimatedNorm scaleError directionError : ℝ)
    (hNorm : 0 < ‖stateVector (fun i => (correction i : ℂ))‖)
    (hScale : |estimatedNorm - ‖stateVector (fun i => (correction i : ℂ))‖| ≤ scaleError)
    (hDirection : |signedCoordinate basis interference address -
      correction address / ‖stateVector (fun i => (correction i : ℂ))‖| ≤ directionError) :
    |(applyCorrection geometry localRhs estimatedNorm (signedEstimates basis interference) snapshot).physical address -
      (snapshot.physical address + correction address)| ≤
      scaleError + ‖stateVector (fun i => (correction i : ℂ))‖ * directionError := by
  have hAt : correctionAt (signedEstimates basis interference) address =
      signedCoordinate basis interference address :=
    sum_signed_estimates_at basis interference address
  apply physical_writeback_error geometry localRhs snapshot correction _ address
    estimatedNorm scaleError directionError hNorm hScale
  · rw [hAt]
    exact signed_coordinate_abs_le_one basis interference address
  · rw [hAt]
    exact hDirection

/-- A signed tomography record incurs at most one sparse physical update per basis shot.
Its residual maintenance charge uses the same reverse stencil as the actual writeback. -/
theorem physical_signed_writeback_cost_le (geometry : Geometry depth)
    (localRhs : Address depth → (Fin geometry.stencilSize → ℝ) → ℝ)
    (snapshot : Snapshot depth) (basis : List (Address depth)) (interference : List (Bool × Address depth))
    (estimatedNorm : ℝ) (rhsPrice degree : ℕ) (hDegree : ∀ address, (geometry.affected address).length ≤ degree) :
    (applyCorrectionWithCost geometry localRhs estimatedNorm rhsPrice
      (signedEstimates basis interference) snapshot).2 ≤
      basis.length * (1 + degree * (rhsPrice + (depth + 1))) :=
  (apply_correction_cost_le geometry localRhs estimatedNorm rhsPrice degree hDegree _ snapshot).trans
    (Nat.mul_le_mul_right _ (signed_estimates_length_le basis interference))

/-- A simultaneous writeback bound under the two-batch tomography law for a normalized
real readout. The coordinate error of the supplied solver direction adds to the sampling
tolerance, and the scale error is charged independently. -/
theorem physical_tomography_writeback_failure_le (geometry : Geometry depth)
    (localRhs : Address depth → (Fin geometry.stencilSize → ℝ) → ℝ)
    (snapshot : Snapshot depth) (correction direction : Address depth → ℝ)
    (hDirection : ∑ i, direction i ^ 2 = 1)
    (estimatedNorm scaleError solverError tolerance failure : ℝ) (hTolerance : 0 < tolerance) (hFailure : 0 < failure)
    (hNorm : 0 < ‖stateVector (fun i => (correction i : ℂ))‖)
    (hScale : |estimatedNorm - ‖stateVector (fun i => (correction i : ℂ))‖| ≤ scaleError)
    (hSolver : ∀ i, |direction i - correction i / ‖stateVector (fun j => (correction j : ℂ))‖| ≤ solverError) :
    let n := tomographyShots depth tolerance failure
    let law := signedTomographyLaw direction hDirection n n (tomography_shots_pos depth tolerance failure)
    eventMass law (fun pair => ∃ i,
      scaleError + ‖stateVector (fun j => (correction j : ℂ))‖ * ((1 + Real.sqrt 2) * tolerance + solverError) <
      |(applyCorrection geometry localRhs estimatedNorm
          (signedEstimates (List.ofFn pair.1) (List.ofFn pair.2)) snapshot).physical i -
        (snapshot.physical i + correction i)|) ≤ failure := by
  intro n law
  refine le_trans (eventMass_mono law _ (fun pair => ∃ i, (1 + Real.sqrt 2) * tolerance <
    |signedCoordinate (List.ofFn pair.1) (List.ofFn pair.2) i - direction i|) ?_)
    (signed_tomography_failure_le_budget direction hDirection tolerance failure hTolerance hFailure)
  rintro pair ⟨i, hi⟩
  refine ⟨i, ?_⟩
  by_contra! hSampling
  let estimate := signedCoordinate (List.ofFn pair.1) (List.ofFn pair.2) i
  let value := correction i / ‖stateVector (fun j => (correction j : ℂ))‖
  have hCoordinate : |estimate - value| ≤ (1 + Real.sqrt 2) * tolerance + solverError := by
    calc
      |estimate - value| = |(estimate - direction i) + (direction i - value)| := by congr 1; ring
      _ ≤ |estimate - direction i| + |direction i - value| := abs_add_le _ _
      _ ≤ _ := add_le_add hSampling (hSolver i)
  exact (not_lt_of_ge (physical_signed_writeback_error geometry localRhs snapshot correction
    (List.ofFn pair.1) (List.ofFn pair.2) i estimatedNorm scaleError _ hNorm hScale hCoordinate)) hi

set_option maxHeartbeats 1000000 in
/-- Independent basis shots followed by independent interference shots for the
chosen reference satisfy the physical writeback bound with an additional failure
allowance for the total variation errors of the shot laws. -/
theorem physical_tomography_writeback_failure_le_of_shot_tv (geometry : Geometry depth)
    (localRhs : Address depth → (Fin geometry.stencilSize → ℝ) → ℝ)
    (snapshot : Snapshot depth) (correction direction : Address depth → ℝ)
    (hDirection : ∑ i, direction i ^ 2 = 1)
    (estimatedNorm scaleError solverError tolerance failure : ℝ)
    (hTolerance : 0 < tolerance) (hFailure : 0 < failure)
    (hNorm : 0 < ‖stateVector (fun i => (correction i : ℂ))‖)
    (hScale : |estimatedNorm - ‖stateVector (fun i => (correction i : ℂ))‖| ≤ scaleError)
    (hSolver : ∀ i, |direction i -
      correction i / ‖stateVector (fun j => (correction j : ℂ))‖| ≤ solverError)
    (basisLaw : FinDist (Address depth))
    (interferenceLaw : (Fin (tomographyShots depth tolerance failure) → Address depth) →
      FinDist (Bool × Address depth))
    (basisError interferenceError : ℝ)
    (hBasisError : tvDist basisLaw (basisSampleLaw direction hDirection) ≤ basisError)
    (hInterferenceError : ∀ b (hne : List.ofFn b ≠ []), tvDist (interferenceLaw b)
      (interferenceSampleLaw direction hDirection (List.ofFn b) hne) ≤ interferenceError) :
    let n := tomographyShots depth tolerance failure
    let law := jointLaw (independentSampleLaw fun _ : Fin n => basisLaw)
      (fun b => independentSampleLaw fun _ : Fin n => interferenceLaw b)
    let bad (pair : (Fin n → Address depth) × (Fin n → Bool × Address depth)) := ∃ i,
      scaleError + ‖stateVector (fun j => (correction j : ℂ))‖ *
        ((1 + Real.sqrt 2) * tolerance + solverError) <
      |(applyCorrection geometry localRhs estimatedNorm
          (signedEstimates (List.ofFn pair.1) (List.ofFn pair.2)) snapshot).physical i -
        (snapshot.physical i + correction i)|
    eventMass law bad ≤ failure + n * basisError + n * interferenceError := by
  intro n law bad
  let ideal := signedTomographyLaw direction hDirection n n
    (tomography_shots_pos depth tolerance failure)
  have hTV : tvDist law ideal ≤ n * basisError + n * interferenceError :=
    signed_tomography_transcript_tv_le direction hDirection
      (tomography_shots_pos depth tolerance failure) basisLaw interferenceLaw basisError
      interferenceError hBasisError hInterferenceError
  have hIdeal : eventMass ideal bad ≤ failure :=
    physical_tomography_writeback_failure_le geometry localRhs snapshot
    correction direction hDirection estimatedNorm scaleError solverError tolerance failure
    hTolerance hFailure hNorm hScale hSolver
  calc
    eventMass law bad ≤ eventMass ideal bad + tvDist law ideal := event_mass_le_add_tv law ideal bad
    _ ≤ failure + (n * basisError + n * interferenceError) := add_le_add hIdeal hTV
    _ = _ := (add_assoc failure (n * basisError) (n * interferenceError)).symm

end Qatlib.Papers.QFVMChen22.TimeStep
