/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Papers.QCNN20.Backprop.QramProducts
public import Qatlib.Concepts.QRAM.AmplitudeAccess.MatrixProductNorm

@[expose] public section

/-!
# Error propagated to the convolution filter writes

[KerenidisLandmanPrakash2020], Appendix E.4, rescales signed gradient coordinates
by the estimated Frobenius norm. The shared norm estimator obtains that scale
from the corresponding QRAM product event. Given an accurate norm estimate and
a bounded signed coordinate estimate, a selected write has error at most twice
the coordinate tolerance times the true gradient norm and the absolute learning
rate. The signed coordinate estimates are inputs to this bound.

[ICLR paper](https://openreview.net/forum?id=Hygab1rKDS)
-/

set_option autoImplicit false

noncomputable section

namespace Qatlib.Papers.QCNN20.Backprop

open Matrix
open Qatlib.Foundations.QramData
open Qatlib.Foundations.QramData.SquaredNormTree
open Qatlib.Concepts.QRAM.AmplitudeAccess
open scoped BigOperators

variable {positions slots filters : ℕ}

/-- A selected filter write differs from the exact old-snapshot gradient step by at most
`2 * |learningRate| * eps` times the Frobenius norm of the filter gradient. The norm estimate
is the square-root rescaling of the product probability estimate, and the coordinate
tolerance is relative to the actual normalized signed QRAM product readout. -/
theorem filter_gradient_write_error (memory : GradientMemory positions slots filters) (h : memory.Valid)
    (addresses : List (Address (filters + slots))) (learningRate eps probabilityEstimate : ℝ)
    (estimate : Matrix (Address slots) (Address filters) ℝ) (r : Address slots) (q : Address filters)
    (hSelected : joinAddress slots r q ∈ addresses)
    (hNorm : 0 < cachedProductNorm memory.patchColumns memory.upstreamColumns)
    (hScale : |matrixProductNormEstimate memory.patchColumns memory.upstreamColumns probabilityEstimate -
        cachedProductNorm memory.patchColumns memory.upstreamColumns| ≤
      eps * cachedProductNorm memory.patchColumns memory.upstreamColumns)
    (hEstimate : |estimate r q| ≤ 1)
    (hCoord : |estimate r q - (matrixProductReadout memory.patchColumns memory.upstreamColumns (r, q)).re| ≤ eps) :
    let G := filterGradient (cachedMatrix slots memory.patchColumns)ᵀ (cachedMatrix positions memory.upstreamRows)
    let normEstimate := matrixProductNormEstimate memory.patchColumns memory.upstreamColumns probabilityEstimate
    |cachedMatrix slots (writeFilterGradient memory addresses learningRate (normEstimate • estimate)) r q -
        gradientStep learningRate (cachedMatrix slots memory.filterRows) G r q| ≤
      2 * |learningRate| * eps * Real.sqrt (∑ i, ∑ j, G i j ^ 2) := by
  intro G normEstimate
  let norm := cachedProductNorm memory.patchColumns memory.upstreamColumns
  have hG : cachedMatrixProduct memory.patchColumns memory.upstreamColumns = G := (qram_gradient_products memory h).1
  have hNormG : norm = Real.sqrt (∑ i, ∑ j, G i j ^ 2) := by
    dsimp [norm, cachedProductNorm]
    rw [hG]
  have hValue : (matrixProductReadout memory.patchColumns memory.upstreamColumns (r, q)).re = G r q / norm := by
    rw [matrix_product_readout_entry _ _ h.patchColumns h.upstreamColumns, Complex.ofReal_re, hG]
  have hEntry : |normEstimate * estimate r q - G r q| ≤ 2 * eps * norm := by
    rw [hValue] at hCoord
    have hRescale : norm * (G r q / norm) = G r q := by
      rw [mul_comm, div_mul_cancel₀ _ hNorm.ne']
    simpa only [hRescale] using
      gradient_readout_error normEstimate norm (estimate r q) (G r q / norm) eps hNorm.le hEstimate hScale hCoord
  rw [read_write_filter_gradient memory addresses learningRate _ r q hSelected, ← hNormG]
  simp only [gradientStep, Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul]
  have hStep : cachedMatrix slots memory.filterRows r q - learningRate * (normEstimate * estimate r q) -
      (cachedMatrix slots memory.filterRows r q - learningRate * G r q) =
        -learningRate * (normEstimate * estimate r q - G r q) := by ring
  rw [hStep, abs_mul, abs_neg]
  calc
    _ ≤ |learningRate| * (2 * eps * norm) := mul_le_mul_of_nonneg_left hEntry (abs_nonneg _)
    _ = _ := by ring

end Qatlib.Papers.QCNN20.Backprop
