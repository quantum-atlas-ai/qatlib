/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Papers.QFVMChen22.TimeStep.BinSpectralReadout

@[expose] public section

/-!
# Unamplified success of the staged stencil solver

For the variable-time solve in [ChenXueChenEtAl2022], Appendix C.3,
the phase classification and reciprocal errors both reduce the
unamplified success amplitude. A gap separating the cumulative
classification error from the inverse response ensures there is
positive probability on the physical output event.

[Published paper](https://doi.org/10.1007/s11128-022-03478-w)
-/

set_option autoImplicit false

noncomputable section

namespace Qatlib.Papers.QFVMChen22.TimeStep

open Matrix
open Qatlib.Foundations.PureStateMath (Inner MeasureProb QState)
open Qatlib.Foundations.PureStateMath.BornBridge (normalized_iff_norm_toEuclidean_fromVec toEuclidean_fromVec)
open Qatlib.Foundations.InstrumentCore.Measurement (Collapse)
open Qatlib.Concepts.PolynomialCalc.QubitizedPower (signal walk)
open Qatlib.Concepts.QsvtCore.PhaseExistence (sparseAlpha)
open Qatlib.Concepts.SketchArith.GramAction (norm_toEuclidean_collapse_eq_sqrt_measureProb norm_toEuclidean_collapse_sub_le)
open Qatlib.Foundations.QramData.SquaredNormTree (Address Tree Valid mass)
open Qatlib.Papers.QFVMChen22.QramStorage (Geometry)
open scoped BigOperators Classical

variable {n : ℕ} {J : Type} [Fintype J] [DecidableEq J]

set_option maxHeartbeats 1400000 in
/-- The executable QRAM-initialized staged solve has a lower bound on its raw success
amplitude. It is positive when the common coefficient mass times the accumulated
classification error is smaller than one minus twice the reciprocal precision. -/
theorem stencil_bin_success_amplitude_lower {depth columns : ℕ} (geometry : Geometry depth)
    (coefficients : Address depth → Fin geometry.stencilSize → ℝ) (entryScale : ℝ)
    (rowScratch : Fin geometry.stencilSize) (columnScratch : Fin columns) (residual : Tree ℝ depth)
    (hValid : Valid residual) (hResidual : 0 < mass residual)
    (hScale : 0 < entryScale)
    (hEntry : ∀ row column, |stencilMatrix geometry coefficients row column| ≤ entryScale)
    (hColumns : ∀ column, (geometry.affected column).dedup.length ≤ columns)
    (width : Fin n → ℕ) (hWidth : ∀ t, 2 ≤ width t) (condition threshold : Fin n → ℝ) (precision : ℝ)
    (hCondition : ∀ t, 1 < condition t) (hPrecision : 0 < precision) (hHalf : precision ≤ 1 / 2)
    (hCutoff : ∀ t, (condition t)⁻¹ ≤ threshold t)
    (conditionBound : ℝ) (hConditionBound : 1 < conditionBound)
    (hGap : ∀ i, |(stencil_signal_hermitian geometry coefficients
      (entryScale * sparseAlpha geometry.stencilSize columns)).eigenvalues i| ∈ Set.Icc conditionBound⁻¹ 1)
    (hSignalCovered : ∀ i, ∃ t, threshold t ≤ |(stencil_signal_hermitian geometry coefficients
      (entryScale * sparseAlpha geometry.stencilSize columns)).eigenvalues i|)
    (v : J → QState (StencilWorkspace depth geometry.stencilSize columns)) (c : J → ℂ)
    (phase μ : J → ℝ) (η : Fin n → ℝ)
    (hη : ∀ t, 0 < η t) (hEtaHalf : ∀ t, η t ≤ 1 / 2)
    (hCos : ∀ j, Real.cos (2 * Real.pi * phase j) = μ j)
    (hMargin : ∀ t j, 2 * Real.pi * η t < abs (|μ j| - threshold t))
    (hOrthogonal : ∀ j l, Inner (v j) (v l) = if j = l then 1 else 0)
    (hWalk : ∀ j, walk (stencilWalkFrame depth rowScratch columnScratch)
      (stencilWalkInvolution geometry coefficients entryScale rowScratch columnScratch) *ᵥ v j =
        Complex.exp (2 * Real.pi * Complex.I * (phase j : ℂ)) • v j)
    (hWalkCovered : ∀ j, ∃ t, threshold t ≤ |μ j|)
    (hInput : (∑ j, c j • v j) = stencilWalkFrame depth rowScratch columnScratch *ᵥ liftedResidual residual) :
    let pos : ∀ t, 0 < width t := fun t => by have := hWidth t; omega
    let mass := commonBinMass condition precision
    let output := stencilBinOutput geometry coefficients entryScale rowScratch columnScratch
      residual width pos condition threshold precision
    let success := stencilBinSuccess rowScratch columnScratch width condition precision
    let error := ∑ t, Real.sqrt 2 * (Real.sqrt (∑ j, ‖runningBinWeight threshold μ c t.val j‖ ^ 2) *
      (1 / (2 * Real.sqrt (width t) * η t)))
    1 - 2 * precision - mass * error ≤ mass * Real.sqrt (MeasureProb output success) ∧
      (mass * error < 1 - 2 * precision → 0 < MeasureProb output success) := by
  intro pos α output success error
  let C := stencilWalkFrame depth rowScratch columnScratch
  let U := stencilWalkInvolution geometry coefficients entryScale rowScratch columnScratch
  let b := liftedResidual residual
  let scale := entryScale * sparseAlpha geometry.stencilSize columns
  let A := (((scale⁻¹ : ℝ) • stencilMatrix geometry coefficients).map Complex.ofReal)
  let h := stencil_signal_hermitian geometry coefficients scale
  let reference := idealBinReference width pos condition threshold precision C U v c μ (Fin.last n)
  let P t := Qatlib.Concepts.WalkSearch.Spectral.spectralDiagonal h.eigenvectorBasis
    (fun i => binSpectralMask threshold t (h.eigenvalues i))
  let z t := compressedBinReciprocal (condition t) precision α C U *ᵥ (P t *ᵥ b)
  obtain ⟨hC, hU, hSq, hEnc⟩ :=
    stencil_walk_encoding geometry coefficients entryScale rowScratch columnScratch hScale hEntry hColumns
  have hLift : signal C U = Qatlib.Foundations.MatrixAlgebra.HermitianLift.lift A := hEnc
  have hBasis (i : Address depth ⊕ Address depth) :
      (Qatlib.Foundations.MatrixAlgebra.HermitianLift.lift A).toEuclideanLin (h.eigenvectorBasis i) =
        (h.eigenvalues i : ℂ) • h.eigenvectorBasis i :=
    stencil_eigenbasis_action geometry coefficients scale i
  have hSignal i : (signal C U).toEuclideanLin (h.eigenvectorBasis i) =
      (h.eigenvalues i : ℂ) • h.eigenvectorBasis i := by rw [hLift]; exact hBasis i
  have hRefMass : MeasureProb reference success = ∑ t, ∑ col : Address depth, ‖z t (Sum.inr col)‖ ^ 2 :=
    stencil_bin_reference_success_mass rowScratch columnScratch U hC hU hSq h.eigenvectorBasis h.eigenvalues
      hSignal v c phase μ b hInput hCos hWalk width pos condition threshold precision hWalkCovered
  have hIdeal : ‖toEuclidean_fromVec (stencilSpectralInverse geometry coefficients scale *ᵥ b)‖ -
      (2 * precision) * ‖toEuclidean_fromVec b‖ ≤ α * Real.sqrt (MeasureProb reference success) := by
    rw [hRefMass]
    exact decoded_bin_right_amplitude_lower A C U hC hSq hLift h.eigenvectorBasis h.eigenvalues hBasis
      condition threshold precision hCondition hPrecision hHalf hSignalCovered (fun i => (hGap i).2)
      hCutoff b (fun _ => rfl)
  have hNormalized := lifted_residual_normalized residual hValid hResidual
  rw [(normalized_iff_norm_toEuclidean_fromVec b).1 hNormalized, mul_one] at hIdeal
  have hInverse := stencil_inverse_output_norm_ge_one geometry coefficients scale conditionBound hConditionBound hGap
    b hNormalized
  change 1 ≤ ‖toEuclidean_fromVec (stencilSpectralInverse geometry coefficients scale *ᵥ b)‖ at hInverse
  have hClose : ‖toEuclidean_fromVec (output - reference)‖ ≤ error :=
    stencil_bin_spectral_reference_error geometry coefficients entryScale rowScratch columnScratch residual
      width hWidth condition threshold precision hScale hEntry hColumns v c phase μ η hη hEtaHalf
      hCos hMargin hOrthogonal hWalk hInput
  have hGapAmplitude : Real.sqrt (MeasureProb reference success) - Real.sqrt (MeasureProb output success) ≤ error := by
    rw [← norm_toEuclidean_collapse_eq_sqrt_measureProb, ← norm_toEuclidean_collapse_eq_sqrt_measureProb]
    refine (norm_sub_norm_le _ _).trans ?_
    rw [norm_sub_rev]
    change ‖toEuclidean_fromVec (Collapse output success - Collapse reference success)‖ ≤ error
    exact (norm_toEuclidean_collapse_sub_le reference output success).trans hClose
  have hMassPos : 0 < α := (common_bin_mass_bounds condition precision).1
  have hScaled := mul_le_mul_of_nonneg_left hGapAmplitude hMassPos.le
  rw [mul_sub] at hScaled
  have hLower : 1 - 2 * precision - α * error ≤ α * Real.sqrt (MeasureProb output success) := by
    linarith
  refine ⟨hLower, fun hError => ?_⟩
  have hAmplitude : 0 < α * Real.sqrt (MeasureProb output success) := (sub_pos.mpr hError).trans_le hLower
  rw [mul_comm] at hAmplitude
  exact Real.sqrt_pos.mp (pos_of_mul_pos_left hAmplitude hMassPos.le)

end Qatlib.Papers.QFVMChen22.TimeStep
