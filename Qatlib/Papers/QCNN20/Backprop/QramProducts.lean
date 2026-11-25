/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Papers.QCNN20.Backprop.Gradients
public import Qatlib.Concepts.QRAM.AmplitudeAccess.MatrixProduct

@[expose] public section

/-!
# QRAM product states for convolution backpropagation

[KerenidisLandmanPrakash2020], Algorithm 2 and Appendix E, form
the products `Aᵀ Δ` and `Δ Fᵀ` from the same snapshot. The first
product reads patch columns and upstream columns. The second reads
upstream rows and filter rows. The successful Frobenius-scaled
preparations give normalized signed gradient entries. An exact write
of a supplied gradient estimate implements the selected old-snapshot
updates. Controlled output preparation for signed tomography and the
finite-word complexity analysis are separate from these identities.

[ICLR paper](https://openreview.net/forum?id=Hygab1rKDS)
-/

set_option autoImplicit false

noncomputable section

namespace Qatlib.Papers.QCNN20.Backprop

open Matrix
open Qatlib.Foundations.PureStateMath (QState)
open Qatlib.Foundations.QramData
open Qatlib.Foundations.QramData.SquaredNormTree
open Qatlib.Concepts.QRAM.AmplitudeAccess
open scoped BigOperators

variable {positions slots filters : ℕ}

/-- The matrix orientations read by the backpropagation products in a single layer snapshot. -/
structure GradientMemory (positions slots filters : ℕ) where
  patchColumns : Tree ℝ (positions + slots)
  upstreamColumns : Tree ℝ (positions + filters)
  upstreamRows : Tree ℝ (filters + positions)
  filterRows : Tree ℝ (filters + slots)

/-- All caches are valid and the two upstream orientations store the same gradient. -/
structure GradientMemory.Valid (memory : GradientMemory positions slots filters) : Prop where
  patchColumns : SquaredNormTree.Valid memory.patchColumns
  upstreamColumns : SquaredNormTree.Valid memory.upstreamColumns
  upstreamRows : SquaredNormTree.Valid memory.upstreamRows
  filterRows : SquaredNormTree.Valid memory.filterRows
  upstreamAgreement : (cachedMatrix filters memory.upstreamColumns)ᵀ = cachedMatrix positions memory.upstreamRows

/-- Initialize the reverse access orientations from the im2col input, filter matrix, and masked
upstream gradient. -/
def gradientMemoryOf (patches : Matrix (Address positions) (Address slots) ℝ)
    (weights : Matrix (Address slots) (Address filters) ℝ)
    (upstream : Matrix (Address positions) (Address filters) ℝ) : GradientMemory positions slots filters :=
  ⟨matrixTree patchesᵀ, matrixTree upstreamᵀ, matrixTree upstream, matrixTree weights⟩

/-- Initializing both upstream orientations from one input makes the backpropagation cache valid. -/
theorem gradient_memory_of_valid (patches : Matrix (Address positions) (Address slots) ℝ)
    (weights : Matrix (Address slots) (Address filters) ℝ)
    (upstream : Matrix (Address positions) (Address filters) ℝ) :
    (gradientMemoryOf patches weights upstream).Valid := by
  refine ⟨valid_matrix_tree _, valid_matrix_tree _, valid_matrix_tree _, valid_matrix_tree _, ?_⟩
  simp [gradientMemoryOf, cached_matrix_tree]

/-- The same upstream data appears in both QRAM gradient products, with the filter matrix
taken from the original snapshot. -/
theorem qram_gradient_products (memory : GradientMemory positions slots filters) (h : memory.Valid) :
    let patches := (cachedMatrix slots memory.patchColumns)ᵀ
    let upstream := cachedMatrix positions memory.upstreamRows
    let weights := cachedMatrix slots memory.filterRows
    cachedMatrixProduct memory.patchColumns memory.upstreamColumns = filterGradient patches upstream ∧
      cachedMatrixProduct memory.upstreamRows memory.filterRows = patchGradient weights upstream := by
  intro patches upstream weights
  refine ⟨?_, rfl⟩
  unfold cachedMatrixProduct filterGradient patches upstream
  rw [Matrix.transpose_transpose, h.upstreamAgreement]

/-- Conditioning the two real QRAM preparations gives the signed normalized filter and
patch gradients. The zero convention also covers zero operands and zero products. -/
theorem qram_gradient_readout (memory : GradientMemory positions slots filters) (h : memory.Valid) :
    let patches := (cachedMatrix slots memory.patchColumns)ᵀ
    let upstream := cachedMatrix positions memory.upstreamRows
    let weights := cachedMatrix slots memory.filterRows
    let G := filterGradient patches upstream
    let H := patchGradient weights upstream
    (∀ r q, matrixProductReadout memory.patchColumns memory.upstreamColumns (r, q) =
      (G r q / Real.sqrt (∑ i, ∑ j, G i j ^ 2) : ℝ)) ∧
    (∀ p r, matrixProductReadout memory.upstreamRows memory.filterRows (p, r) =
      (H p r / Real.sqrt (∑ i, ∑ j, H i j ^ 2) : ℝ)) := by
  intro patches upstream weights G H
  obtain ⟨hG, hH⟩ := qram_gradient_products memory h
  constructor
  · intro r q
    rw [matrix_product_readout_entry _ _ h.patchColumns h.upstreamColumns, cachedProductNorm, hG]
  · intro p r
    rw [matrix_product_readout_entry _ _ h.upstreamRows h.filterRows, cachedProductNorm, hH]

/-- Write the supplied filter estimates at the selected coefficients using the old filter tree. -/
def writeFilterGradient (memory : GradientMemory positions slots filters) (addresses : List (Address (filters + slots)))
    (learningRate : ℝ) (estimate : Matrix (Address slots) (Address filters) ℝ) : Tree ℝ (filters + slots) :=
  updateKernel memory.filterRows addresses learningRate
    (fun address => estimate ((joinAddressEquiv slots).symm address).1 ((joinAddressEquiv slots).symm address).2)

/-- The selected filter writes preserve the cached masses. -/
theorem valid_write_filter_gradient (memory : GradientMemory positions slots filters) (h : memory.Valid)
    (addresses : List (Address (filters + slots))) (learningRate : ℝ)
    (estimate : Matrix (Address slots) (Address filters) ℝ) :
    SquaredNormTree.Valid (writeFilterGradient memory addresses learningRate estimate) :=
  valid_refresh _ h.filterRows _ _

/-- A selected filter coordinate receives the gradient step evaluated on the original snapshot. -/
theorem read_write_filter_gradient (memory : GradientMemory positions slots filters)
    (addresses : List (Address (filters + slots))) (learningRate : ℝ)
    (estimate : Matrix (Address slots) (Address filters) ℝ) (r : Address slots) (q : Address filters)
    (hSelected : joinAddress slots r q ∈ addresses) :
    cachedMatrix slots (writeFilterGradient memory addresses learningRate estimate) r q =
      gradientStep learningRate (cachedMatrix slots memory.filterRows) estimate r q := by
  have hAddress : (joinAddressEquiv slots).symm (joinAddress slots r q) = (r, q) := by
    rw [← join_address_equiv_apply, Equiv.symm_apply_apply]
  change read (subtree slots (writeFilterGradient memory addresses learningRate estimate) r) q = _
  rw [read_subtree, writeFilterGradient, read_update_kernel, ite_eq_left hSelected, hAddress, ← read_subtree,
    gradientStep, Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul, cachedMatrix, Matrix.of_apply]

end Qatlib.Papers.QCNN20.Backprop
