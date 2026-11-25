/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Concepts.QRAM.AmplitudeAccess.MatrixProduct
public import Qatlib.Concepts.AEMeanReadout.LocalAEBackend.RelativeAeStopping
public import Qatlib.Concepts.LchsSimulation.StaticLchs.PreparedAmplitudeAmplification

@[expose] public section

/-!
# Norm estimation from the QRAM product flag

Apply the fresh-block relative amplitude estimator from [BrassardEtAl2002] to the
unamplified QRAM matrix-product flag. The first ready median estimates the marked
probability. Its square root times the known operand scale estimates the product
norm. The guarantees concern positive product norms and count forward invocations
of the exact preparation unitary. The positive-readiness rule requires a separate
zero-product path when the probability is zero.
-/

set_option autoImplicit false

noncomputable section

namespace Qatlib.Concepts.QRAM.AmplitudeAccess

open Qatlib.Foundations.QramData.SquaredNormTree
open Qatlib.Concepts.AEMeanReadout.LocalAEBackend
open Qatlib.Concepts.AEMeanReadout.LocalAEBackend.PreparedRelativeAeAdaptiveLaw (adaptiveGrid)
open Qatlib.Concepts.LchsSimulation.StaticLchs (preparedAAState)
open Qatlib.Concepts.ProbabilityCore.Concentration (eventMass)
open Qatlib.Concepts.ProbabilityCore.Concentration.ProbabilityInterfaces (eventMass_mono)
open Qatlib.Foundations.BornMetrics.EventProbability (measureProb_le_one)
open Qatlib.Foundations.PureStateMath (MeasureProb normalized_applyGate normalized_ket)
open scoped Classical

variable {rows inner columns : ℕ}

/-- Rescale the square root of the estimated product success probability by the cached operand norms. -/
def matrixProductNormEstimate (left : Tree ℝ (inner + rows)) (right : Tree ℝ (inner + columns))
    (probabilityEstimate : ℝ) : ℝ :=
  matrixProductScale left right * Real.sqrt (max 0 probabilityEstimate)

/-- The square-root transformation preserves a relative error bound on the positive product flag. -/
theorem matrix_product_norm_estimate_error (left : Tree ℝ (inner + rows)) (right : Tree ℝ (inner + columns))
    (hLeftMass : 0 < mass left) (hRightMass : 0 < mass right) (hNorm : 0 < cachedProductNorm left right)
    (eps probabilityEstimate : ℝ)
    (hEstimate : |probabilityEstimate - (cachedProductNorm left right / matrixProductScale left right) ^ 2| ≤
      eps * (cachedProductNorm left right / matrixProductScale left right) ^ 2) :
    |matrixProductNormEstimate left right probabilityEstimate - cachedProductNorm left right| ≤
      eps * cachedProductNorm left right := by
  let scale := matrixProductScale left right
  let norm := cachedProductNorm left right
  let q := norm / scale
  let root := Real.sqrt (max 0 probabilityEstimate)
  have hScale : 0 < scale := mul_pos (Real.sqrt_pos.2 hLeftMass) (Real.sqrt_pos.2 hRightMass)
  have hq : 0 < q := div_pos hNorm hScale
  have hRoot : 0 ≤ root := Real.sqrt_nonneg _
  have hRootSq : root ^ 2 = max 0 probabilityEstimate := Real.sq_sqrt (le_max_left _ _)
  have hRescale : scale * q = norm := by
    change scale * (norm / scale) = norm
    rw [mul_comm, div_mul_cancel₀ _ hScale.ne']
  have hClip : |max 0 probabilityEstimate - q ^ 2| ≤ |probabilityEstimate - q ^ 2| := by
    by_cases hp : 0 ≤ probabilityEstimate
    · rw [max_eq_right hp]
    · have hNeg := le_of_not_ge hp
      rw [max_eq_left hNeg, abs_of_nonpos (sub_nonpos.mpr (sq_nonneg q)),
        abs_of_nonpos (sub_nonpos.mpr (hNeg.trans (sq_nonneg q)))]
      linarith
  have hFactor : |root - q| * (root + q) = |max 0 probabilityEstimate - q ^ 2| := by
    rw [← abs_of_nonneg (add_nonneg hRoot hq.le), ← abs_mul]
    congr 1
    calc
      (root - q) * (root + q) = root ^ 2 - q ^ 2 := by ring
      _ = _ := by rw [hRootSq]
  have hError : |root - q| ≤ eps * q := by
    apply (mul_le_mul_iff_of_pos_right hq).mp
    calc
      |root - q| * q ≤ |root - q| * (root + q) :=
        mul_le_mul_of_nonneg_left (le_add_of_nonneg_left hRoot) (abs_nonneg _)
      _ = |max 0 probabilityEstimate - q ^ 2| := hFactor
      _ ≤ eps * q ^ 2 := hClip.trans hEstimate
      _ = (eps * q) * q := by ring
  change |scale * root - norm| ≤ eps * norm
  rw [← hRescale, ← mul_sub, abs_mul, abs_of_pos hScale]
  calc
    scale * |root - q| ≤ scale * (eps * q) := mul_le_mul_of_nonneg_left hError hScale.le
    _ = eps * (scale * q) := by ring

/-- The history mass that stops and reports a norm outside the relative tolerance. The probability
estimate at that stopping stage is its fresh median of measured phase labels. -/
def matrixProductNormFailureMass (left : Tree ℝ (inner + rows)) (right : Tree ℝ (inner + columns))
    (hLeft : Valid left) (hRight : Valid right) (eps : ℝ) (r : ℕ → ℕ) (N : ℕ) : ℝ :=
  eventMass (freshHistoryLaw r N (matrixProductPreparation left right) (matrixProductSeed rows inner columns)
    (matrixProductSuccess rows inner columns) (matrix_product_preparation_unitary left right hLeft hRight)) (fun ω =>
      ∃ k, freshHistoryFirstStop eps r ω k ∧
        eps * cachedProductNorm left right < |matrixProductNormEstimate left right
          (freshMedianEstimate (adaptiveGrid k.val) (r k.val) (ω k)) - cachedProductNorm left right|)

/-- At every horizon the calibrated schedule has bounded norm-estimation failure mass and
expected forward accesses. Its pending mass tends to zero. The access bound is proportional
to the operand scale divided by the product norm and relative tolerance. -/
theorem exists_matrix_product_norm_schedule (left : Tree ℝ (inner + rows)) (right : Tree ℝ (inner + columns))
    (hLeft : Valid left) (hRight : Valid right) (hLeftMass : 0 < mass left) (hRightMass : 0 < mass right)
    (hNorm : 0 < cachedProductNorm left right) (eps δ : ℝ) (heps : 0 < eps) (heps1 : eps ≤ 1) (hδ : 0 < δ) :
    let A := matrixProductPreparation left right
    let j := matrixProductSeed rows inner columns
    let S := matrixProductSuccess rows inner columns
    let hA := matrix_product_preparation_unitary left right hLeft hRight
    ∃ r0 : ℕ,
      (∀ N, matrixProductNormFailureMass left right hLeft hRight eps (fun _ => r0) N ≤ δ) ∧
      (∀ N, freshHistoryExpectedForward eps (fun _ => r0) N A j S hA ≤
        (192 * Real.pi * (2 * (r0 : ℝ) + 1)) / (eps * (cachedProductNorm left right / matrixProductScale left right))) ∧
      (∀ η : ℝ, 0 < η → ∃ B : ℕ, ∀ N, B < N →
        freshHistoryPendingMass eps (fun _ => r0) N A j S hA < η) := by
  intro A j S hA
  let q := cachedProductNorm left right / matrixProductScale left right
  have hq : 0 < q := div_pos hNorm (mul_pos (Real.sqrt_pos.2 hLeftMass) (Real.sqrt_pos.2 hRightMass))
  have hProb : MeasureProb (preparedAAState A j) S = q ^ 2 :=
    matrix_product_success_probability left right hLeft hRight hLeftMass hRightMass
  have ha : q ^ 2 ≤ 1 := by
    rw [← hProb]
    exact measureProb_le_one (normalized_applyGate hA (normalized_ket j)) S
  obtain ⟨r0, hFailure, hCost, hPending⟩ := exists_fixedFreshSchedule_failure_expected_tail
    eps δ heps heps1 hδ A j S hA (q ^ 2) (pow_pos hq _) ha hProb
  refine ⟨r0, ?_, ?_, hPending⟩
  · intro N
    refine le_trans ?_ (hFailure N)
    unfold matrixProductNormFailureMass freshHistoryFailureMass
    apply eventMass_mono
    rintro ω ⟨k, hk, hBad⟩
    refine ⟨k, hk, ?_⟩
    unfold freshHistoryRelativeBad
    rw [hProb]
    by_contra! hEstimate
    exact (not_lt_of_ge (matrix_product_norm_estimate_error left right hLeftMass hRightMass hNorm eps _ hEstimate)) hBad
  · intro N
    simpa only [Real.sqrt_sq hq.le] using hCost N

end Qatlib.Concepts.QRAM.AmplitudeAccess
