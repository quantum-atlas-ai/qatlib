/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Papers.QCNN20.PatchMemory.Im2col
public import Qatlib.Concepts.QRAM.SignedReadout.Tomography
public import Mathlib.Data.Matrix.Mul

@[expose] public section

/-!
# Backpropagation through an im2col convolution

[KerenidisLandmanPrakash2020], Appendix E, uses ordinary matrix products for
the filter and patch adjoints. The pixel adjoint adds contributions from
all copies of each pixel introduced by im2col. The sampled rule uses the
forward observation mask for the derivative. The error bound for rescaled
entries assumes the norm and normalized gradient estimates are given.

[ICLR paper](https://openreview.net/forum?id=Hygab1rKDS)
-/

set_option autoImplicit false

namespace Qatlib.Papers.QCNN20.Backprop

open Matrix
open scoped BigOperators

variable {Position Slot Filter Pixel : Type*}
variable [Fintype Position] [Fintype Slot] [Fintype Filter]

/-- The filter gradient is the transpose of the im2col input times the upstream gradient. -/
def filterGradient (patches : Matrix Position Slot ℝ) (upstream : Matrix Position Filter ℝ) :
    Matrix Slot Filter ℝ :=
  patchesᵀ * upstream

/-- The gradient on the duplicated patch matrix is the upstream gradient times the filter transpose. -/
def patchGradient (filters : Matrix Slot Filter ℝ) (upstream : Matrix Position Filter ℝ) :
    Matrix Position Slot ℝ :=
  upstream * filtersᵀ

/-- Add the gradients of all patch slots originating at the same pixel. -/
def pixelGradient [DecidableEq Pixel] (source : Position → Slot → Pixel)
    (gradient : Matrix Position Slot ℝ) (pixel : Pixel) : ℝ :=
  ∑ position, ∑ slot, if source position slot = pixel then gradient position slot else 0

/-- With finite images, scattering is the adjoint of gathering pixels into patches. -/
theorem scatter_is_adjoint [Fintype Pixel] [DecidableEq Pixel] (source : Position → Slot → Pixel)
    (gradient : Matrix Position Slot ℝ) (direction : Pixel → ℝ) :
    ∑ pixel, pixelGradient source gradient pixel * direction pixel =
      ∑ position, ∑ slot, gradient position slot * direction (source position slot) := by
  simp only [pixelGradient, Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro position _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro slot _
  simp only [ite_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, ite_true]

/-- Update the filter coefficients by a step in the negative gradient direction. -/
def gradientStep (learningRate : ℝ) (filters estimate : Matrix Slot Filter ℝ) :
    Matrix Slot Filter ℝ :=
  filters - learningRate • estimate

/-- Propagate the derivative through point selection and the linear region of capped ReLU. -/
noncomputable def gateGradient (cap : ℝ) (observed retained : Bool)
    (preactivation upstream : ℝ) : ℝ :=
  if observed && retained then
    if 0 < preactivation ∧ preactivation < cap then upstream else 0
  else 0

/-- A value omitted by measurement contributes zero to the backpropagated derivative. -/
theorem gate_gradient_unobserved (cap value upstream : ℝ) (retained : Bool) :
    gateGradient cap false retained value upstream = 0 := by
  simp [gateGradient]

/-- The quantum backpropagation rule in Appendix E.2.2 uses the forward observation mask as
a surrogate activation derivative and the pooling mask to route the upstream gradient. -/
def sampledGradient (observed retained : Bool) (upstream : ℝ) : ℝ :=
  if observed && retained then upstream else 0

/-- The surrogate passes the upstream gradient at an observed position retained by pooling. -/
theorem sampled_gradient_observed_retained (upstream : ℝ) :
    sampledGradient true true upstream = upstream := rfl

/-- Any missing observation or unretained pooling entry contributes zero. -/
theorem sampled_gradient_zero (observed retained : Bool) (upstream : ℝ)
    (h : (observed && retained) = false) : sampledGradient observed retained upstream = 0 := by
  simp [sampledGradient, h]

/-- The coordinate error in Appendix E.4 follows when the relative norm error and the total
normalized coordinate error each satisfy the same tolerance. -/
theorem gradient_readout_error (estimatedNorm trueNorm estimate value tolerance : ℝ)
    (hNorm : 0 ≤ trueNorm) (hEstimate : |estimate| ≤ 1)
    (hRel : |estimatedNorm - trueNorm| ≤ tolerance * trueNorm)
    (hCoord : |estimate - value| ≤ tolerance) :
    |estimatedNorm * estimate - trueNorm * value| ≤ 2 * tolerance * trueNorm := by
  calc
    _ ≤ |estimatedNorm - trueNorm| + trueNorm * |estimate - value| :=
      Qatlib.Concepts.QRAM.SignedReadout.rescale_error _ _ _ _ hNorm hEstimate
    _ ≤ tolerance * trueNorm + trueNorm * tolerance :=
      add_le_add hRel (mul_le_mul_of_nonneg_left hCoord hNorm)
    _ = _ := by ring

open Qatlib.Foundations.QramData.SquaredNormTree

/-- Apply classical gradient corrections by writing the selected filter coefficients to QRAM. -/
def updateKernel {depth : ℕ} (kernel : Tree ℝ depth) (addresses : List (Address depth))
    (learningRate : ℝ) (gradient : Address depth → ℝ) : Tree ℝ depth :=
  refresh kernel addresses (fun address => read kernel address - learningRate * gradient address)

/-- Filter writes update exactly the selected coefficients, using the old snapshot at each address. -/
theorem read_update_kernel {depth : ℕ} (kernel : Tree ℝ depth) (addresses : List (Address depth))
    (learningRate : ℝ) (gradient : Address depth → ℝ) (address : Address depth) :
    read (updateKernel kernel addresses learningRate gradient) address =
      if address ∈ addresses then read kernel address - learningRate * gradient address
      else read kernel address :=
  read_refresh _ _ _ _

end Qatlib.Papers.QCNN20.Backprop
