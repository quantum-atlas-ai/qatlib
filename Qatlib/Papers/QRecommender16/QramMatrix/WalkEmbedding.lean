/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Papers.QRecommender16.QramMatrix.MatrixStorage
public import Qatlib.Concepts.QRAM.AmplitudeAccess.UnitaryPreparation
public import Qatlib.Concepts.AEMeanReadout.LocalAEBackend.LocalQFTReadout
public import Qatlib.Concepts.GateVocabulary.GateVocab.CircuitRelabel
public import Qatlib.Papers.QRecommender16.MainResults.SpectralEstimation.BireflectionFactorization
public import Qatlib.Foundations.InstrumentCore.Measurement.MeasurementLaws
public import Qatlib.Foundations.PureStateMath.Tensor

@[expose] public section

/-!
# Embedding QRAM user rows into the recommendation walk

[KerenidisPrakash2017], Theorem 5.1 and Algorithms 5.2 and 6.1, prepare a
signed user row and prepend the state of normalized row norms. This tensor
state is the image of the user row under the second walk isometry. A
nonzero retained vector in the image has a column marginal given by its
normalized squared amplitudes. The address conversion here is exact for
the finite matrix represented by the tree.

[Fixed source](https://arxiv.org/abs/1603.08675v3)
-/

set_option autoImplicit false

noncomputable section

namespace Qatlib.Papers.QRecommender16.QramMatrix

open Matrix
open Qatlib.Foundations.QramData.SquaredNormTree
open Qatlib.Concepts.QRAM.AmplitudeAccess
open Qatlib.Papers.QRecommender16.MainResults.SpectralEstimation
open Qatlib.Foundations.PureStateMath
open Qatlib.Foundations.PureStateMath.BornBridge (applyGate_relabelGate relabelGate relabelState relabelState_apply)
open Qatlib.Foundations.InstrumentCore.Measurement
open Qatlib.Concepts.AEMeanReadout.LocalAEBackend (relabelState_ket)
open Qatlib.Concepts.GateVocabulary.GateVocab (relabelGate_mem_unitaryGroup)
open scoped BigOperators Matrix.Norms.Frobenius

variable {rows columns : ℕ}

/-- Read the matrix from the QRAM tree using finite integer row and column indices. -/
def storedMatrix (storage : MatrixStorage rows columns) :
    Matrix (Fin (2 ^ rows)) (Fin (2 ^ columns)) ℝ :=
  fun i j => entry storage ((bitVecEquiv rows).symm i) ((bitVecEquiv columns).symm j)

/-- The cached mass of the indexed row is its squared Euclidean norm in the walk matrix. -/
theorem stored_matrix_row_norm_sq (storage : MatrixStorage rows columns) (h : Valid storage)
    (i : Fin (2 ^ rows)) :
    rowNormSq (storedMatrix storage) i = mass (rowTree storage ((bitVecEquiv rows).symm i)) := by
  rw [row_mass_eq storage h]
  exact Equiv.sum_comp (bitVecEquiv columns).symm (fun j => entry storage ((bitVecEquiv rows).symm i) j ^ 2)

/-- The Frobenius norm in the walk is the square root of the QRAM root mass. -/
theorem stored_matrix_frobenius_norm (storage : MatrixStorage rows columns) (h : Valid storage) :
    ‖storedMatrix storage‖ = Real.sqrt (mass storage) := by
  have hMass : ‖storedMatrix storage‖ ^ 2 = mass storage := by
    rw [← sum_rowNormSq]
    simp_rw [stored_matrix_row_norm_sq storage h]
    rw [Equiv.sum_comp (bitVecEquiv rows).symm (fun address => mass (rowTree storage address))]
    exact (mass_eq_sum_subtrees rows storage h).symm
  rw [← hMass, Real.sqrt_sq (norm_nonneg _)]

/-- The signed amplitudes of one QRAM-prepared user row in integer column order. -/
def storedUserAmplitudes (storage : MatrixStorage rows columns) (user : Address rows) :
    Fin (2 ^ columns) → ℝ :=
  fun j => pathAmplitude (rowTree storage user) ((bitVecEquiv columns).symm j)

/-- For a nonzero stored row the exact QRAM read produces a unit vector. -/
theorem stored_user_amplitudes_normalized (storage : MatrixStorage rows columns) (h : Valid storage)
    (user : Address rows) (hRow : 0 < mass (rowTree storage user)) :
    Normalized (fun j => (storedUserAmplitudes storage user j : ℂ)) := by
  unfold Normalized storedUserAmplitudes
  simp only [Complex.norm_real, Real.norm_eq_abs, sq_abs]
  rw [Equiv.sum_comp (bitVecEquiv columns).symm (fun address => pathAmplitude (rowTree storage user) address ^ 2)]
  exact sum_path_amplitude_sq _ (valid_subtree rows storage user h) hRow

/-- The top-level QRAM preparation expressed in integer row order. -/
def storedRowNormAmplitudes (storage : MatrixStorage rows columns) : Fin (2 ^ rows) → ℝ :=
  fun i => prefixAmplitude rows storage ((bitVecEquiv rows).symm i)

/-- Each stored row-norm amplitude agrees with the scalar in the second walk isometry. -/
theorem stored_row_norm_amplitude (storage : MatrixStorage rows columns) (h : Valid storage)
    (hPos : 0 < mass storage) (i : Fin (2 ^ rows)) :
    storedRowNormAmplitudes storage i = Real.sqrt (rowNormSq (storedMatrix storage) i) / ‖storedMatrix storage‖ := by
  rw [storedRowNormAmplitudes, row_norm_preparation storage h hPos, ← row_mass_eq storage h,
    ← stored_matrix_row_norm_sq storage h, stored_matrix_frobenius_norm storage h]

/-- The prepared row-norm state is normalized when the matrix has positive total mass. -/
theorem stored_row_norm_amplitudes_normalized (storage : MatrixStorage rows columns) (h : Valid storage)
    (hPos : 0 < mass storage) : Normalized (fun i => (storedRowNormAmplitudes storage i : ℂ)) := by
  have hNorm : 0 < ‖storedMatrix storage‖ := by
    rw [stored_matrix_frobenius_norm storage h]
    exact Real.sqrt_pos_of_pos hPos
  unfold Normalized
  simp only [Complex.norm_real, Real.norm_eq_abs, sq_abs]
  simp_rw [stored_row_norm_amplitude storage h hPos, div_pow, Real.sq_sqrt (rowNormSq_nonneg _ _)]
  rw [← Finset.sum_div, sum_rowNormSq, div_self (pow_ne_zero _ hNorm.ne')]

/-- The QRAM row-norm preparation prepended to any column vector implements its image under
the second walk isometry. In particular the vector may be the QRAM-prepared user row. -/
theorem stored_walk_embedding (storage : MatrixStorage rows columns) (h : Valid storage)
    (hPos : 0 < mass storage) (x : Fin (2 ^ columns) → ℝ) :
    TensorState (fun i => (storedRowNormAmplitudes storage i : ℂ)) (fun j => (x j : ℂ)) =
      fun p => ((isometryQ (storedMatrix storage) *ᵥ x) p : ℂ) := by
  funext p
  simp only [TensorState, stored_row_norm_amplitude storage h hPos, isometryQ,
    Matrix.mulVec, dotProduct, ite_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ, ite_true,
    Complex.ofReal_mul]

/-- The two QRAM preparations give the normalized walk input on every nonzero stored user row. -/
theorem stored_walk_user_normalized (storage : MatrixStorage rows columns) (h : Valid storage)
    (hPos : 0 < mass storage) (user : Address rows) (hRow : 0 < mass (rowTree storage user)) :
    Normalized (fun p => ((isometryQ (storedMatrix storage) *ᵥ storedUserAmplitudes storage user) p : ℂ)) := by
  rw [← stored_walk_embedding storage h hPos]
  exact normalized_tensorState (stored_row_norm_amplitudes_normalized storage h hPos)
    (stored_user_amplitudes_normalized storage h user hRow)

/-- Prepare the walk input by executing the row-norm prefix and signed user-row loaders. -/
def storedWalkUserInput (storage : MatrixStorage rows columns) (user : Address rows) :
    QState (Fin (2 ^ rows) × Fin (2 ^ columns)) :=
  TensorState
    (relabelState (bitVecEquiv rows) (ApplyGate (prefixPreparation rows storage) (Ket (ZeroStr rows))))
    (relabelState (bitVecEquiv columns)
      (ApplyGate (signedTreePreparation (rowTree storage user)) (Ket (ZeroStr columns))))

/-- The integer labels of the zero row and column addresses used by the QRAM loaders. -/
def storedWalkUserSeed (rows columns : ℕ) : Fin (2 ^ rows) × Fin (2 ^ columns) :=
  (bitVecEquiv rows (ZeroStr rows), bitVecEquiv columns (ZeroStr columns))

/-- The reversible row-norm prefix and signed user-row loaders on the walk basis. -/
def storedWalkUserLoader (storage : MatrixStorage rows columns) (user : Address rows) :
    Matrix (Fin (2 ^ rows) × Fin (2 ^ columns)) (Fin (2 ^ rows) × Fin (2 ^ columns)) ℂ :=
  TensorGate (relabelGate (bitVecEquiv rows) (prefixPreparation rows storage))
    (relabelGate (bitVecEquiv columns) (signedTreePreparation (rowTree storage user)))

/-- Combining the two valid cached-tree preparations gives a unitary on the walk basis. -/
theorem stored_walk_user_loader_unitary (storage : MatrixStorage rows columns) (h : Valid storage)
    (user : Address rows) : storedWalkUserLoader storage user ∈ Matrix.unitaryGroup _ ℂ :=
  tensorGate_unitary ((relabelGate_mem_unitaryGroup _ _).2 (prefix_preparation_unitary rows storage h))
    ((relabelGate_mem_unitaryGroup _ _).2 (signed_tree_preparation_unitary _ (valid_subtree rows storage user h)))

/-- Running the combined reversible loader on the seed gives exactly the walk input. -/
theorem stored_walk_user_loader_apply (storage : MatrixStorage rows columns) (user : Address rows) :
    ApplyGate (storedWalkUserLoader storage user) (Ket (storedWalkUserSeed rows columns)) =
      storedWalkUserInput storage user := by
  rw [storedWalkUserLoader, storedWalkUserSeed, ← tensorState_ket_ket, applyGate_tensorGate]
  rw [← relabelState_ket (bitVecEquiv rows) (ZeroStr rows),
    ← relabelState_ket (bitVecEquiv columns) (ZeroStr columns), applyGate_relabelGate, applyGate_relabelGate,
    storedWalkUserInput]

/-- Executing the prefix and signed row preparations gives the actual input to the walk. -/
theorem stored_walk_user_preparation (storage : MatrixStorage rows columns) (h : Valid storage)
    (hPos : 0 < mass storage) (user : Address rows) (hRow : 0 < mass (rowTree storage user)) :
    storedWalkUserInput storage user =
      fun p => ((isometryQ (storedMatrix storage) *ᵥ storedUserAmplitudes storage user) p : ℂ) := by
  have hPrefix : relabelState (bitVecEquiv rows)
      (ApplyGate (prefixPreparation rows storage) (Ket (ZeroStr rows))) =
      fun i => (storedRowNormAmplitudes storage i : ℂ) := by
    funext i
    rw [relabelState_apply]
    exact prefix_preparation_apply rows storage h hPos _
  have hUser : relabelState (bitVecEquiv columns)
      (ApplyGate (signedTreePreparation (rowTree storage user)) (Ket (ZeroStr columns))) =
      fun j => (storedUserAmplitudes storage user j : ℂ) := by
    funext j
    rw [relabelState_apply]
    exact signed_tree_preparation_apply _ (valid_subtree rows storage user h) hRow _
  rw [storedWalkUserInput, hPrefix, hUser]
  exact stored_walk_embedding storage h hPos (storedUserAmplitudes storage user)

/-- The second walk isometry preserves the total Born weight of the input column vector. -/
theorem stored_walk_image_mass (storage : MatrixStorage rows columns) (h : Valid storage)
    (hPos : 0 < mass storage) (x : Fin (2 ^ columns) → ℝ) :
    MeasureProb (fun p => ((isometryQ (storedMatrix storage) *ᵥ x) p : ℂ)) Finset.univ =
      ∑ j, x j ^ 2 := by
  rw [← stored_walk_embedding storage h hPos, ← Finset.univ_product_univ,
    measureProb_tensorState_right (stored_row_norm_amplitudes_normalized storage h hPos)]
  simp [MeasureProb, BornProb, Complex.norm_real, Real.norm_eq_abs, sq_abs]

/-- A nonzero real column vector in the walk image has the normalized squared-amplitude
product law after conditioning and ignoring the row-norm register. -/
theorem stored_walk_product_event (storage : MatrixStorage rows columns) (h : Valid storage)
    (hPos : 0 < mass storage) (x : Fin (2 ^ columns) → ℝ) (hX : 0 < ∑ j, x j ^ 2)
    (products : Finset (Fin (2 ^ columns))) :
    let ψ := fun p => ((isometryQ (storedMatrix storage) *ᵥ x) p : ℂ)
    MeasureProb (PostMeasure ψ Finset.univ) (Finset.univ ×ˢ products) =
      (∑ j ∈ products, x j ^ 2) / ∑ j, x j ^ 2 := by
  intro ψ
  let first := fun i => (storedRowNormAmplitudes storage i : ℂ)
  let second := fun j => (x j : ℂ)
  have hEq : TensorState first second = ψ := stored_walk_embedding storage h hPos x
  have hFirst : Normalized first := stored_row_norm_amplitudes_normalized storage h hPos
  have hTotal : MeasureProb ψ Finset.univ = ∑ j, x j ^ 2 := stored_walk_image_mass storage h hPos x
  have hMeasure : 0 < MeasureProb ψ Finset.univ := by rwa [hTotal]
  rw [measureProb_postMeasure hMeasure, Finset.univ_inter, hTotal, ← hEq,
    measureProb_tensorState_right hFirst]
  simp [second, MeasureProb, BornProb, Complex.norm_real, Real.norm_eq_abs, sq_abs]

end Qatlib.Papers.QRecommender16.QramMatrix
