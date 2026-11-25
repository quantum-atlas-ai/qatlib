/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Concepts.QRAM.AmplitudeAccess.UnitaryPreparation
public import Qatlib.Concepts.AEMeanReadout.LocalAEBackend.LocalQFTReadout
public import Qatlib.Concepts.BlockEncoding.Postselection

@[expose] public section

/-!
# Matrix products from signed QRAM preparations

The left matrix is stored in row order and the right matrix in column order.
Load the left row norms and the entire signed right matrix, and then apply the
adjoint of each left row loader controlled by its row address. The zero inner
register compresses this operation to the matrix product divided by the two
Frobenius norms. This gives an exact Frobenius-scaled realization of the
matrix application used in [KerenidisLandmanPrakash2020], Appendix F.7.

[ICLR paper](https://openreview.net/forum?id=Hygab1rKDS)
-/

set_option autoImplicit false

noncomputable section

namespace Qatlib.Concepts.QRAM.AmplitudeAccess

open Matrix
open Qatlib.Foundations.QramData.SquaredNormTree
open Qatlib.Concepts.AEMeanReadout.LocalAEBackend (relabelState_ket)
open Qatlib.Concepts.BlockEncoding.EncodingCore (relabelGate_mem_unitary)
open Qatlib.Concepts.QsvtCore.PhaseExistence (blockDiagFirst blockDiagFirst_unitary)
open Qatlib.Foundations.PureStateMath
open Qatlib.Foundations.PureStateMath.BornBridge (applyGate_relabelGate relabelGate relabelState relabelState_apply)
open Qatlib.Foundations.InstrumentCore.Measurement (PostMeasure collapse_apply postMeasure_eq_zero_of_measureProb_eq_zero)
open scoped BigOperators Classical

variable {rows inner columns : ℕ}

/-- Read a row-indexed matrix from the signed leaves of its cached tree. -/
def cachedMatrix (rows : ℕ) (memory : Tree ℝ (inner + rows)) : Matrix (Address rows) (Address inner) ℝ :=
  Matrix.of fun i k => read (subtree rows memory i) k

/-- Initialize an operand tree by enumerating its matrix entries in row order. -/
def matrixTree (A : Matrix (Address rows) (Address inner) ℝ) : Tree ℝ (inner + rows) :=
  ofFn _ fun address => A ((joinAddressEquiv rows).symm address).1 ((joinAddressEquiv rows).symm address).2

/-- Building an operand tree preserves its cached mass invariant. -/
theorem valid_matrix_tree (A : Matrix (Address rows) (Address inner) ℝ) : Valid (matrixTree A) :=
  valid_ofFn _ _

/-- Reading the initialized tree recovers the exact input matrix. -/
theorem cached_matrix_tree (A : Matrix (Address rows) (Address inner) ℝ) : cachedMatrix rows (matrixTree A) = A := by
  ext i k
  rw [cachedMatrix, Matrix.of_apply, read_subtree, matrixTree, read_ofFn, ← join_address_equiv_apply,
    Equiv.symm_apply_apply]

/-- A valid zero-mass cache represents the zero matrix. -/
theorem cached_matrix_eq_zero_of_mass_zero (memory : Tree ℝ (inner + rows))
    (hValid : Valid memory) (hZero : mass memory = 0) : cachedMatrix rows memory = 0 := by
  ext i k
  change read (subtree rows memory i) k = 0
  rw [read_subtree]
  exact read_eq_zero_of_mass_eq_zero memory hValid hZero _

/-- Multiply the row-indexed left operand by the column-indexed right operand. -/
def cachedMatrixProduct (left : Tree ℝ (inner + rows)) (right : Tree ℝ (inner + columns)) :
    Matrix (Address rows) (Address columns) ℝ :=
  cachedMatrix rows left * (cachedMatrix columns right)ᵀ

/-- The product of the cached entry norms, which equals the product of Frobenius norms
for valid operand caches. -/
def matrixProductScale (left : Tree ℝ (inner + rows)) (right : Tree ℝ (inner + columns)) : ℝ :=
  Real.sqrt (mass left) * Real.sqrt (mass right)

/-- The Euclidean norm of the entries of the product. -/
def cachedProductNorm (left : Tree ℝ (inner + rows)) (right : Tree ℝ (inner + columns)) : ℝ :=
  Real.sqrt (∑ i, ∑ j, cachedMatrixProduct left right i j ^ 2)

/-- Row and column output addresses with the contraction register last. -/
abbrev MatrixProductBasis (rows inner columns : ℕ) := Address rows × (Address columns × Address inner)

/-- Start the row and flattened right operand loaders in their respective zero kets. -/
def matrixProductSeed (rows inner columns : ℕ) : MatrixProductBasis rows inner columns :=
  (ZeroStr rows, (joinAddressEquiv columns).symm (ZeroStr (inner + columns)))

/-- Load row norms and the column-indexed right matrix and contract with the left row loaders. -/
def matrixProductPreparation (left : Tree ℝ (inner + rows)) (right : Tree ℝ (inner + columns)) :
    Matrix (MatrixProductBasis rows inner columns) (MatrixProductBasis rows inner columns) ℂ :=
  blockDiagFirst (fun i => TensorGate 1 (signedTreePreparation (subtree rows left i))ᴴ) *
    TensorGate (prefixPreparation rows left)
      (relabelGate (joinAddressEquiv columns).symm (signedTreePreparation right))

/-- The product circuit is unitary on the whole workspace, including zero left rows. -/
theorem matrix_product_preparation_unitary (left : Tree ℝ (inner + rows)) (right : Tree ℝ (inner + columns))
    (hLeft : Valid left) (hRight : Valid right) :
    matrixProductPreparation left right ∈ Matrix.unitaryGroup (MatrixProductBasis rows inner columns) ℂ := by
  apply (Matrix.unitaryGroup _ ℂ).mul_mem
  · apply blockDiagFirst_unitary
    intro i
    apply tensorGate_unitary (Matrix.unitaryGroup (Address columns) ℂ).one_mem
    rw [← Matrix.star_eq_conjTranspose]
    exact Unitary.star_mem (signed_tree_preparation_unitary _ (valid_subtree rows left i hLeft))
  · exact tensorGate_unitary (prefix_preparation_unitary rows left hLeft)
      (relabelGate_mem_unitary (signed_tree_preparation_unitary right hRight) (joinAddressEquiv columns).symm)

/-- A cached root mass equals the squared Frobenius norm of the addressed entries. -/
theorem cached_matrix_mass (memory : Tree ℝ (inner + rows)) (hValid : Valid memory) :
    mass memory = ∑ i, ∑ k, cachedMatrix rows memory i k ^ 2 := by
  rw [mass_eq_sum_subtrees rows memory hValid]
  exact Finset.sum_congr rfl fun i _ => mass_eq_sum _ (valid_subtree rows memory i hValid)

/-- Row-norm weighting cancels the normalization of the row loader, with zero rows giving
zero even though the row loader itself is still unitary. -/
private theorem weighted_left_row_adjoint (left : Tree ℝ (inner + rows)) (hLeft : Valid left)
    (hMass : 0 < mass left) (i : Address rows) (k : Address inner) :
    (signedTreePreparation (subtree rows left i))ᴴ (ZeroStr inner) k * (prefixAmplitude rows left i : ℂ) =
      (cachedMatrix rows left i k / Real.sqrt (mass left) : ℝ) := by
  let row := subtree rows left i
  have hRow : Valid row := valid_subtree rows left i hLeft
  rw [prefix_amplitude_eq rows left hLeft hMass]
  by_cases hRowMass : 0 < mass row
  · have hEntry : signedTreePreparation row k (ZeroStr inner) =
        (read row k / Real.sqrt (mass row) : ℝ) :=
      (applyGate_eq_mulVec_ket (signedTreePreparation row) (ZeroStr inner) k).symm.trans
        (signed_tree_preparation_entries row hRow hRowMass k)
    change (signedTreePreparation row)ᴴ (ZeroStr inner) k *
      ((Real.sqrt (mass row) / Real.sqrt (mass left) : ℝ) : ℂ) = _
    rw [Matrix.conjTranspose_apply, hEntry, Complex.star_def, Complex.conj_ofReal, ← Complex.ofReal_mul]
    have hReal : (read row k / Real.sqrt (mass row)) * (Real.sqrt (mass row) / Real.sqrt (mass left)) =
        read row k / Real.sqrt (mass left) := by
      field_simp [(Real.sqrt_pos.mpr hRowMass).ne', (Real.sqrt_pos.mpr hMass).ne']
    exact congrArg (fun a : ℝ => (a : ℂ)) hReal
  · have hZero : mass row = 0 := le_antisymm (le_of_not_gt hRowMass) (mass_nonneg row hRow)
    change _ * ((Real.sqrt (mass row) / Real.sqrt (mass left) : ℝ) : ℂ) =
      (read row k / Real.sqrt (mass left) : ℝ)
    simp [hZero, read_eq_zero_of_mass_eq_zero row hRow hZero k]

set_option maxHeartbeats 1200000 in
/-- The zero contraction register gives the actual product entry scaled by the two cached
operand norms. Both operands can contain zero rows or columns. -/
theorem matrix_product_preparation_entry (left : Tree ℝ (inner + rows)) (right : Tree ℝ (inner + columns))
    (hLeft : Valid left) (hRight : Valid right) (hLeftMass : 0 < mass left) (hRightMass : 0 < mass right)
    (i : Address rows) (j : Address columns) :
    ApplyGate (matrixProductPreparation left right) (Ket (matrixProductSeed rows inner columns))
        (i, j, ZeroStr inner) = (cachedMatrixProduct left right i j / matrixProductScale left right : ℝ) := by
  let e : (Address columns × Address inner) ≃ Address (inner + columns) := joinAddressEquiv columns
  let loaded := ApplyGate (TensorGate (prefixPreparation rows left) (relabelGate e.symm (signedTreePreparation right)))
    (Ket (matrixProductSeed rows inner columns))
  have hLoaded : loaded = TensorState (ApplyGate (prefixPreparation rows left) (Ket (ZeroStr rows)))
      (relabelState e.symm (ApplyGate (signedTreePreparation right) (Ket (ZeroStr (inner + columns))))) := by
    unfold loaded matrixProductSeed
    rw [← tensorState_ket_ket, applyGate_tensorGate,
      ← relabelState_ket e.symm (ZeroStr (inner + columns)), applyGate_relabelGate]
  have hLoadedEntry (k : Address inner) : loaded (i, j, k) =
      (prefixAmplitude rows left i : ℂ) * (cachedMatrix columns right j k / Real.sqrt (mass right) : ℝ) := by
    rw [hLoaded, TensorState, prefix_preparation_apply rows left hLeft hLeftMass, relabelState_apply,
      Equiv.symm_symm, signed_tree_preparation_entries right hRight hRightMass]
    rw [show e (j, k) = joinAddress columns j k from join_address_equiv_apply columns j k, ← read_subtree,
      cachedMatrix, Matrix.of_apply]
  let L := signedTreePreparation (subtree rows left i)
  rw [matrixProductPreparation, applyGate_mul, applyGate_blockDiagFirst_slice]
  change ApplyGate (TensorGate (1 : Matrix (Address columns) (Address columns) ℂ) Lᴴ)
    (fun q => loaded (i, q)) (j, ZeroStr inner) = _
  have hContract : ApplyGate (TensorGate (1 : Matrix (Address columns) (Address columns) ℂ) Lᴴ)
      (fun q => loaded (i, q)) (j, ZeroStr inner) = ∑ k, Lᴴ (ZeroStr inner) k * loaded (i, j, k) := by
    simp only [ApplyGate, Matrix.mulVec, dotProduct, Fintype.sum_prod_type, tensorGate_apply,
      Matrix.one_apply, ite_mul, one_mul, zero_mul, Finset.sum_ite_irrel, Finset.sum_const_zero,
      Finset.sum_ite_eq, Finset.mem_univ, ite_true]
  calc
    _ = ∑ k, Lᴴ (ZeroStr inner) k * loaded (i, j, k) := hContract
    _ = ((∑ k, (cachedMatrix rows left i k / Real.sqrt (mass left)) *
        (cachedMatrix columns right j k / Real.sqrt (mass right)) : ℝ) : ℂ) := by
      rw [Complex.ofReal_sum]
      apply Finset.sum_congr rfl
      intro k _
      have hWeight : Lᴴ (ZeroStr inner) k * (prefixAmplitude rows left i : ℂ) =
          (cachedMatrix rows left i k / Real.sqrt (mass left) : ℝ) :=
        weighted_left_row_adjoint left hLeft hLeftMass i k
      rw [hLoadedEntry k, ← mul_assoc, hWeight, Complex.ofReal_mul]
    _ = _ := by
      congr 1
      rw [cachedMatrixProduct, Matrix.mul_apply, Finset.sum_div]
      apply Finset.sum_congr rfl
      intro k _
      rw [div_mul_div_comm, matrixProductScale, Matrix.transpose_apply]

/-- The product is selected when the contraction register has returned to its zero label. -/
def matrixProductSuccess (rows inner columns : ℕ) : Finset (MatrixProductBasis rows inner columns) :=
  Finset.univ ×ˢ (Finset.univ ×ˢ {ZeroStr inner})

/-- The original success probability equals the squared ratio of the product norm to
the product of the operand norms. In particular a zero product has zero success mass. -/
theorem matrix_product_success_probability (left : Tree ℝ (inner + rows)) (right : Tree ℝ (inner + columns))
    (hLeft : Valid left) (hRight : Valid right) (hLeftMass : 0 < mass left) (hRightMass : 0 < mass right) :
    MeasureProb (ApplyGate (matrixProductPreparation left right) (Ket (matrixProductSeed rows inner columns)))
        (matrixProductSuccess rows inner columns) = (cachedProductNorm left right / matrixProductScale left right) ^ 2 := by
  have hNonneg : 0 ≤ ∑ i : Address rows, ∑ j : Address columns, cachedMatrixProduct left right i j ^ 2 :=
    Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => sq_nonneg _
  have hNorm : cachedProductNorm left right ^ 2 = ∑ i, ∑ j, cachedMatrixProduct left right i j ^ 2 :=
    Real.sq_sqrt hNonneg
  simp only [matrixProductSuccess, MeasureProb, Finset.sum_product, Finset.sum_singleton, BornProb]
  simp_rw [matrix_product_preparation_entry left right hLeft hRight hLeftMass hRightMass,
    Complex.norm_real, Real.norm_eq_abs, sq_abs, div_pow, ← Finset.sum_div]
  rw [hNorm]

/-- Upon success the row and column amplitudes are the normalized signed entries of the
matrix product, with clean contraction workspace. -/
theorem matrix_product_postmeasure_entry (left : Tree ℝ (inner + rows)) (right : Tree ℝ (inner + columns))
    (hLeft : Valid left) (hRight : Valid right) (hLeftMass : 0 < mass left) (hRightMass : 0 < mass right)
    (hProduct : 0 < cachedProductNorm left right) (i : Address rows) (j : Address columns) :
    PostMeasure (ApplyGate (matrixProductPreparation left right) (Ket (matrixProductSeed rows inner columns)))
        (matrixProductSuccess rows inner columns) (i, j, ZeroStr inner) =
      (cachedMatrixProduct left right i j / cachedProductNorm left right : ℝ) := by
  let out := ApplyGate (matrixProductPreparation left right) (Ket (matrixProductSeed rows inner columns))
  let good := matrixProductSuccess rows inner columns
  have hScale : 0 < matrixProductScale left right := mul_pos (Real.sqrt_pos.mpr hLeftMass) (Real.sqrt_pos.mpr hRightMass)
  have hMass : Real.sqrt (MeasureProb out good) = cachedProductNorm left right / matrixProductScale left right := by
    rw [matrix_product_success_probability left right hLeft hRight hLeftMass hRightMass,
      Real.sqrt_sq (div_nonneg hProduct.le hScale.le)]
  have hGood : (i, j, ZeroStr inner) ∈ good := by simp [good, matrixProductSuccess]
  have hRaw : out (i, j, ZeroStr inner) = (cachedMatrixProduct left right i j / matrixProductScale left right : ℝ) :=
    matrix_product_preparation_entry left right hLeft hRight hLeftMass hRightMass i j
  change PostMeasure out good (i, j, ZeroStr inner) = _
  rw [PostMeasure, collapse_apply, ite_eq_left hGood, hMass, hRaw, ← Complex.ofReal_inv, ← Complex.ofReal_mul]
  congr 1
  field_simp [hScale.ne', hProduct.ne']

/-- Apply the product preparation and take its normalized successful output. A zero root
mass is detected in the cache, so the algorithm returns zero without loading that operand. -/
def matrixProductReadout (left : Tree ℝ (inner + rows)) (right : Tree ℝ (inner + columns)) :
    QState (Address rows × Address columns) :=
  if 0 < mass left ∧ 0 < mass right then
    fun ij => PostMeasure (ApplyGate (matrixProductPreparation left right) (Ket (matrixProductSeed rows inner columns)))
      (matrixProductSuccess rows inner columns) (ij.1, ij.2, ZeroStr inner)
  else 0

/-- The signed readout gives the product divided by its norm. The zero-product convention
also describes the output when the cache skips a zero operand or when the circuit has no success mass. -/
theorem matrix_product_readout_entry (left : Tree ℝ (inner + rows)) (right : Tree ℝ (inner + columns))
    (hLeft : Valid left) (hRight : Valid right) (i : Address rows) (j : Address columns) :
    matrixProductReadout left right (i, j) = (cachedMatrixProduct left right i j / cachedProductNorm left right : ℝ) := by
  unfold matrixProductReadout
  split_ifs with hMasses
  · by_cases hProduct : 0 < cachedProductNorm left right
    · exact matrix_product_postmeasure_entry left right hLeft hRight hMasses.1 hMasses.2 hProduct i j
    · have hZero : cachedProductNorm left right = 0 :=
        le_antisymm (le_of_not_gt hProduct) (Real.sqrt_nonneg _)
      have hProb := matrix_product_success_probability left right hLeft hRight hMasses.1 hMasses.2
      rw [hZero, zero_div, zero_pow (by decide : 2 ≠ 0)] at hProb
      simp only [postMeasure_eq_zero_of_measureProb_eq_zero hProb, hZero, div_zero, Complex.ofReal_zero, Pi.zero_apply]
  · have hZero : cachedMatrixProduct left right = 0 := by
      by_cases hPos : 0 < mass left
      · have hRightZero := le_antisymm (le_of_not_gt fun hp => hMasses ⟨hPos, hp⟩) (mass_nonneg right hRight)
        rw [cachedMatrixProduct, cached_matrix_eq_zero_of_mass_zero right hRight hRightZero,
          Matrix.transpose_zero, Matrix.mul_zero]
      · have hLeftZero := le_antisymm (le_of_not_gt hPos) (mass_nonneg left hLeft)
        rw [cachedMatrixProduct, cached_matrix_eq_zero_of_mass_zero left hLeft hLeftZero, Matrix.zero_mul]
    simp [hZero]

end Qatlib.Concepts.QRAM.AmplitudeAccess
