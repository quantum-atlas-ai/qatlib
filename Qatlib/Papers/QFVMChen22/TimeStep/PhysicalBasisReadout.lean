/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Papers.QFVMChen22.TimeStep.SolutionScale
public import Qatlib.Papers.QFVMChen22.TimeStep.SolverTomography
public import Mathlib.Analysis.Normed.Module.Normalize

@[expose] public section

/-!
# Basis readout of the physical stencil correction

The ideal staged target for [ChenXueChenEtAl2022], Section 3.3, is the
inverse stencil acting on the normalized residual, carried in the right
stencil frame with both tapes clean. The normalized target is therefore
the signed physical correction divided by its Euclidean norm and embedded
at the physical addresses. A decoded success state close to this target
gives a basis measurement law close to that of the physical correction.

[Published paper](https://doi.org/10.1007/s11128-022-03478-w)
-/

set_option autoImplicit false
set_option synthInstance.maxSize 512

noncomputable section

namespace Qatlib.Papers.QFVMChen22.TimeStep

open Matrix
open Qatlib.Concepts.MonteCarloMean.FinDistBounds (tvDist)
open Qatlib.Concepts.QsvtCore.PhaseExistence (leftFrame_isIsometry rightFrame_isIsometry)
open Qatlib.Foundations.InstrumentCore.Measurement (PostMeasure)
open Qatlib.Foundations.MatrixAlgebra.HermitianLift (nativeEmbedding_gram)
open Qatlib.Foundations.PureStateMath (MeasureProb Normalized QState TensorState ket_apply)
open Qatlib.Foundations.PureStateMath.BornBridge
  (normalized_iff_norm_toEuclidean_fromVec toEuclidean_fromVec)
open Qatlib.Foundations.QueryWordCore.Circuit (Run)
open Qatlib.Concepts.QRAM.SignedReadout
open Qatlib.Foundations.QramData.SquaredNormTree (Address Tree Valid mass read)
open Qatlib.Papers.QFVMChen22.QramStorage (Geometry)
open scoped BigOperators Classical

variable {n depth rows columns : ℕ}

/-- The physical correction is placed on precisely the right-frame labels
with clean phase and coefficient tapes. -/
theorem seeded_stencil_correction_eq_embedded (rowScratch : Fin rows) (columnScratch : Fin columns)
    (width : Fin n → ℕ) (pos : ∀ t, 0 < width t) (condition : Fin n → ℝ) (precision : ℝ)
    (direction : Address depth → ℝ) :
    seededBinState width condition precision (cleanPhaseTape width pos)
        (stencilWalkFrame depth rowScratch columnScratch *ᵥ
          Sum.elim 0 (fun a => (direction a : ℂ))) =
      embeddedDirection (stencilSolutionAddress rowScratch columnScratch width pos condition precision)
        direction := by
  funext p
  rw [embedded_direction_apply]
  rcases p with ⟨phase, tape, signal⟩
  simp only [seededBinState, TensorState, ket_apply, Matrix.mulVec, dotProduct, Fintype.sum_sum_type,
    Sum.elim_inl, Sum.elim_inr, Pi.zero_apply, mul_zero, Finset.sum_const_zero, zero_add]
  simp_rw [stencil_walk_frame_apply]
  by_cases hPhase : phase = cleanPhaseTape width pos <;>
    by_cases hTape : tape = cleanReciprocalTape condition precision <;>
    simp [stencilSolutionAddress, hPhase, hTape, ite_mul]

/-- The signed direction associated with a real stencil correction. -/
def normalizedStencilCorrection (correction : Address depth → ℝ) : Address depth → ℝ :=
  fun a => correction a / ‖toEuclidean_fromVec (fun i => (correction i : ℂ))‖

/-- A nonzero correction gives a unit real direction. -/
theorem normalized_stencil_correction_sum_sq (correction : Address depth → ℝ)
    (hNorm : 0 < ‖toEuclidean_fromVec (fun i => (correction i : ℂ))‖) :
    ∑ a, normalizedStencilCorrection correction a ^ 2 = 1 := by
  let x := toEuclidean_fromVec (fun i => (correction i : ℂ))
  have hSq := EuclideanSpace.norm_sq_eq x
  change ‖x‖ ^ 2 = ∑ a, ‖(correction a : ℂ)‖ ^ 2 at hSq
  simp only [Complex.norm_real, Real.norm_eq_abs, sq_abs] at hSq
  change (∑ a, (correction a / ‖x‖) ^ 2) = 1
  rw [show (∑ a, (correction a / ‖x‖) ^ 2) = (∑ a, correction a ^ 2) / ‖x‖ ^ 2 by
    simp only [div_pow, Finset.sum_div], ← hSq, div_self (pow_ne_zero _ hNorm.ne')]

set_option maxHeartbeats 700000 in
/-- The ideal inverse target is a positive real multiple of the unit
physical correction, with its exact Euclidean norm given by that multiple. -/
theorem stencil_bin_inverse_target_scale (geometry : Geometry depth)
    (coefficients : Address depth → Fin geometry.stencilSize → ℝ) (scale κ : ℝ)
    (rowScratch : Fin geometry.stencilSize) (columnScratch : Fin columns)
    (residual : Tree ℝ depth) (correction : Address depth → ℝ)
    (hValid : Valid residual) (hMass : 0 < mass residual) (hScale : 0 < scale)
    (hEquation : stencilMatrix geometry coefficients *ᵥ correction = read residual)
    (hCondition : 1 < κ)
    (hGap : ∀ j, |(stencil_signal_hermitian geometry coefficients scale).eigenvalues j| ∈ Set.Icc κ⁻¹ 1)
    (hNorm : 0 < ‖toEuclidean_fromVec (fun i => (correction i : ℂ))‖)
    (width : Fin n → ℕ) (pos : ∀ t, 0 < width t) (condition : Fin n → ℝ) (precision : ℝ) :
    let place := stencilSolutionAddress (depth := depth) rowScratch columnScratch width pos condition precision
    let target := seededBinState width condition precision (cleanPhaseTape width pos)
      (stencilWalkFrame depth rowScratch columnScratch *ᵥ ((commonBinMass condition precision : ℂ)⁻¹ •
        (stencilSpectralInverse geometry coefficients scale *ᵥ liftedResidual residual)))
    let factor := (commonBinMass condition precision)⁻¹ * (scale / Real.sqrt (mass residual)) *
      ‖toEuclidean_fromVec (fun i => (correction i : ℂ))‖
    0 < factor ∧
      toEuclidean_fromVec target =
        factor • toEuclidean_fromVec (embeddedDirection place (normalizedStencilCorrection correction)) ∧
      ‖toEuclidean_fromVec target‖ = factor := by
  intro place target factor
  let r := ‖toEuclidean_fromVec (fun i => (correction i : ℂ))‖
  let α := commonBinMass condition precision
  let direction := normalizedStencilCorrection correction
  let clean := embeddedDirection place direction
  have hr : r ≠ 0 := hNorm.ne'
  have hFactor : 0 < factor := by
    exact mul_pos (mul_pos (inv_pos.mpr (common_bin_mass_bounds condition precision).1)
      (div_pos hScale (Real.sqrt_pos.2 hMass))) hNorm
  have hUnit : ‖toEuclidean_fromVec clean‖ = 1 :=
    (normalized_iff_norm_toEuclidean_fromVec clean).1
      (embedded_direction_normalized place direction (normalized_stencil_correction_sum_sq correction hNorm))
  have hCorrection :
      (Sum.elim 0 (fun a => (correction a : ℂ)) : QState (Address depth ⊕ Address depth)) =
        (r : ℂ) • Sum.elim (0 : Address depth → ℂ) (fun a => (direction a : ℂ)) := by
    funext j
    cases j with
    | inl a => simp
    | inr a =>
        change (correction a : ℂ) = (r : ℂ) * ((correction a / r : ℝ) : ℂ)
        rw [← Complex.ofReal_mul]
        exact congrArg Complex.ofReal (by rw [mul_comm r, div_mul_cancel₀ _ hr])
  have hVector : target = (factor : ℂ) • clean := by
    change seededBinState width condition precision (cleanPhaseTape width pos)
      (stencilWalkFrame depth rowScratch columnScratch *ᵥ ((α : ℂ)⁻¹ •
        (stencilSpectralInverse geometry coefficients scale *ᵥ liftedResidual residual))) =
          (factor : ℂ) • embeddedDirection place direction
    rw [stencil_inverse_residual_eq_correction geometry coefficients scale κ residual correction
      hValid hMass hScale hEquation hCondition hGap, hCorrection, smul_smul, smul_smul,
      Matrix.mulVec_smul]
    rw [← seeded_stencil_correction_eq_embedded rowScratch columnScratch width pos condition precision direction]
    funext i
    simp only [factor, Complex.ofReal_mul, Complex.ofReal_inv, seededBinState, TensorState, Pi.smul_apply,
      smul_eq_mul]
    ring
  have hReal : toEuclidean_fromVec target = factor • toEuclidean_fromVec clean := by
    change WithLp.toLp 2 target = factor • WithLp.toLp 2 clean
    exact (congrArg (WithLp.toLp 2) hVector).trans
      ((WithLp.toLp_smul (p := 2) (factor : ℂ) clean).trans
        (RCLike.real_smul_eq_coe_smul (K := ℂ) factor (WithLp.toLp 2 clean)).symm)
  refine ⟨hFactor, hReal, ?_⟩
  rw [hReal, norm_smul, Real.norm_eq_abs, abs_of_pos hFactor, hUnit, mul_one]

set_option maxHeartbeats 700000 in
/-- For a nonzero solution of the physical stencil equations, the normalized
ideal bin target is the normalized correction on the clean physical addresses. -/
theorem stencil_bin_inverse_target_normalize (geometry : Geometry depth)
    (coefficients : Address depth → Fin geometry.stencilSize → ℝ) (scale κ : ℝ)
    (rowScratch : Fin geometry.stencilSize) (columnScratch : Fin columns)
    (residual : Tree ℝ depth) (correction : Address depth → ℝ)
    (hValid : Valid residual) (hMass : 0 < mass residual) (hScale : 0 < scale)
    (hEquation : stencilMatrix geometry coefficients *ᵥ correction = read residual)
    (hCondition : 1 < κ)
    (hGap : ∀ j, |(stencil_signal_hermitian geometry coefficients scale).eigenvalues j| ∈ Set.Icc κ⁻¹ 1)
    (hNorm : 0 < ‖toEuclidean_fromVec (fun i => (correction i : ℂ))‖)
    (width : Fin n → ℕ) (pos : ∀ t, 0 < width t) (condition : Fin n → ℝ) (precision : ℝ) :
    let place := stencilSolutionAddress (depth := depth) rowScratch columnScratch width pos condition precision
    let target := seededBinState width condition precision (cleanPhaseTape width pos)
      (stencilWalkFrame depth rowScratch columnScratch *ᵥ ((commonBinMass condition precision : ℂ)⁻¹ •
        (stencilSpectralInverse geometry coefficients scale *ᵥ liftedResidual residual)))
    NormedSpace.normalize (toEuclidean_fromVec target) =
      toEuclidean_fromVec (embeddedDirection place (normalizedStencilCorrection correction)) := by
  intro place target
  obtain ⟨hFactor, hScaled, _⟩ := stencil_bin_inverse_target_scale geometry coefficients scale κ
    rowScratch columnScratch residual correction hValid hMass hScale hEquation hCondition hGap hNorm
    width pos condition precision
  have hUnit : ‖toEuclidean_fromVec (embeddedDirection place (normalizedStencilCorrection correction))‖ = 1 :=
    (normalized_iff_norm_toEuclidean_fromVec _).1
      (embedded_direction_normalized place _ (normalized_stencil_correction_sum_sq correction hNorm))
  rw [show toEuclidean_fromVec target = _ from hScaled,
    NormedSpace.normalize_smul_of_pos hFactor, NormedSpace.normalize_eq_self_of_norm_eq_one hUnit]

set_option maxHeartbeats 800000 in
/-- The actual basis measurement of any decoded success branch obeys the
physical correction's Born-law bound from the normalized inverse-target
error. The raw and amplified solver outputs use the same clean target. -/
theorem stencil_bin_basis_shot_le_of_inverse_error (geometry : Geometry depth)
    (coefficients : Address depth → Fin geometry.stencilSize → ℝ) (scale κ : ℝ)
    (rowScratch : Fin geometry.stencilSize) (columnScratch : Fin columns)
    (residual : Tree ℝ depth) (correction : Address depth → ℝ)
    (hValid : Valid residual) (hMass : 0 < mass residual) (hScale : 0 < scale)
    (hEquation : stencilMatrix geometry coefficients *ᵥ correction = read residual)
    (hCondition : 1 < κ)
    (hGap : ∀ j, |(stencil_signal_hermitian geometry coefficients scale).eigenvalues j| ∈ Set.Icc κ⁻¹ 1)
    (hNorm : 0 < ‖toEuclidean_fromVec (fun i => (correction i : ℂ))‖)
    (width : Fin n → ℕ) (pos : ∀ t, 0 < width t)
    (condition threshold : Fin n → ℝ) (precision : ℝ)
    (U : Matrix (StencilWorkspace depth geometry.stencilSize columns)
      (StencilWorkspace depth geometry.stencilSize columns) ℂ)
    (hU : Uᴴ = U) (hSq : U * U = 1)
    (raw : QState (BinStageWorkspace width condition precision (StencilWorkspace depth geometry.stencilSize columns)))
    (hp : 0 < MeasureProb raw (stencilBinSuccess rowScratch columnScratch width condition precision))
    (fallback : Address depth) (ε : ℝ) :
    let place := stencilSolutionAddress (depth := depth) rowScratch columnScratch width pos condition precision
    let C := stencilWalkFrame depth rowScratch columnScratch
    let S := stencilBinSuccess rowScratch columnScratch width condition precision
    let ψ := Run 1 (stencilBinHistoryUncompute width condition threshold precision C U) (PostMeasure raw S)
    let target := seededBinState width condition precision (cleanPhaseTape width pos)
      (C *ᵥ ((commonBinMass condition precision : ℂ)⁻¹ •
        (stencilSpectralInverse geometry coefficients scale *ᵥ liftedResidual residual)))
    ‖toEuclidean_fromVec ψ - NormedSpace.normalize (toEuclidean_fromVec target)‖ ≤ ε →
      ∃ hψ, tvDist (bornReadoutLaw ψ hψ (readPlacedAddress place fallback))
        (basisSampleLaw (normalizedStencilCorrection correction)
          (normalized_stencil_correction_sum_sq correction hNorm)) ≤ ε := by
  intro place C S ψ target hError
  have hC : Cᴴ * C = 1 := by
    dsimp only [C, stencilWalkFrame]
    exact nativeEmbedding_gram _ _ (leftFrame_isIsometry (Sum.inr rowScratch))
      (rightFrame_isIsometry (Sum.inr columnScratch))
  have hψ : Normalized ψ :=
    stencil_bin_decoded_success_normalized rowScratch columnScratch width condition threshold precision
      pos C U hC hU hSq raw hp
  have hTarget : NormedSpace.normalize (toEuclidean_fromVec target) =
      toEuclidean_fromVec (embeddedDirection place (normalizedStencilCorrection correction)) :=
    stencil_bin_inverse_target_normalize geometry coefficients scale κ rowScratch columnScratch
      residual correction hValid hMass hScale hEquation hCondition hGap hNorm width pos condition precision
  refine ⟨hψ, (measured_basis_shot_tv_le place ψ hψ _ (normalized_stencil_correction_sum_sq correction hNorm)
    (readPlacedAddress place fallback) (read_placed_address place fallback)).trans ?_⟩
  change ‖toEuclidean_fromVec ψ - toEuclidean_fromVec
    (embeddedDirection place (normalizedStencilCorrection correction))‖ ≤ ε
  rwa [hTarget] at hError

end Qatlib.Papers.QFVMChen22.TimeStep
