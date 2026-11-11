/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Data.Matrix.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Tactic

/-!
# Definitions for sparse graph mixing reductions

The block encoding `gammaBlock` replaces signed entries by nonnegative two-by-two matrices, and
`blockConvert` applies it entrywise. The vectors `phiMinus`, `phiPlus`, and their localized
lifts describe the two sectors used in the sparse graph reductions of [JanzingWocjan2006].

The module also defines the real dot product, a regular-graph Laplacian expression, and
diagonal-minus-off-diagonal observables. Its block identities identify signed entries with
expectations in the antisymmetric state.

## Main statements

* `gammaBlock_mulVec_phiMinus`: the antisymmetric vector has eigenvalue equal to the encoded
  signed entry.
* `phiMinus_expectation_gammaBlock`: the antisymmetric expectation recovers that entry.
* `phiMinus_bilinear_eq`: a symmetric two-point block with equal diagonals gives a
  diagonal-minus-off-diagonal expectation.

## References

* [Janzing and Wocjan, 2006][JanzingWocjan2006]
-/

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.BQPMixSparse06.MainResults

open Finset Matrix

/-- The two-by-two block encoding: zero for `a = 0`, identity for `a = 1`, and the swap matrix
for all other integers. -/
def gammaBlock (a : ℤ) : Matrix (Fin 2) (Fin 2) ℝ :=
  if a = 0 then 0 else if a = 1 then 1 else !![0, 1; 1, 0]

/-- The normalized symmetric two-point vector with both coordinates equal to `1 / √2`. -/
def phiPlus : Fin 2 → ℝ := fun _ => 1 / Real.sqrt 2

/-- The normalized antisymmetric two-point vector with coordinates `1 / √2` and `-1 / √2`. -/
def phiMinus : Fin 2 → ℝ := fun s => if s = 0 then 1 / Real.sqrt 2 else -(1 / Real.sqrt 2)

/-- Lifts a vector `v` to the doubled index set by setting its `(s, i)` coordinate to `v i * φ
s`. -/
def liftVec {N : ℕ} (φ : Fin 2 → ℝ) (v : Fin N → ℝ) : Fin 2 × Fin N → ℝ :=
  fun p => v p.2 * φ p.1

/-- The antisymmetric unit vector supported on the two copies of vertex `j`. -/
def psiMinus {N : ℕ} (j : Fin N) : Fin 2 × Fin N → ℝ := liftVec phiMinus (Pi.single j 1)

/-- The symmetric unit vector supported on the two copies of vertex `j`. -/
def psiPlus {N : ℕ} (j : Fin N) : Fin 2 × Fin N → ℝ := liftVec phiPlus (Pi.single j 1)

/-- The real matrix obtained by casting every integer entry of `A` to a real number. -/
def realCast {N : ℕ} (A : Matrix (Fin N) (Fin N) ℤ) : Matrix (Fin N) (Fin N) ℝ :=
  A.map (Int.cast)

/-- The doubled real matrix obtained by replacing each integer entry of `A` with its block
`gammaBlock`. -/
def blockConvert {N : ℕ} (A : Matrix (Fin N) (Fin N) ℤ) :
    Matrix (Fin 2 × Fin N) (Fin 2 × Fin N) ℝ :=
  fun p q => gammaBlock (A p.2 q.2) p.1 q.1

/-- The real dot product of two vectors indexed by a finite type. -/
def dot {ι : Type*} [Fintype ι] (u v : ι → ℝ) : ℝ := ∑ i, u i * v i

/-- The matrix expression `d • 1 - A` for a regular-graph Laplacian. -/
def laplacian {N : ℕ} (A : Matrix (Fin N) (Fin N) ℝ) (d : ℝ) :
    Matrix (Fin N) (Fin N) ℝ := d • (1 : Matrix (Fin N) (Fin N) ℝ) - A

/-- The difference `M q q - M q r` between a diagonal entry and the indicated off-diagonal
entry. -/
def cqr {N : ℕ} (M : Matrix (Fin N) (Fin N) ℝ) (q r : Fin N) : ℝ :=
  M q q - M q r

/-- The diagonal-minus-off-diagonal quantity `M q q - M q r` used for path differences. -/
def deltaPath {N : ℕ} (M : Matrix (Fin N) (Fin N) ℝ) (q r : Fin N) : ℝ :=
  M q q - M q r

/-- The block encoding of zero is the zero matrix. -/
@[simp] lemma gammaBlock_zero : gammaBlock 0 = 0 := by
  simp [gammaBlock]

/-- The block encoding of one is the identity matrix. -/
@[simp] lemma gammaBlock_one : gammaBlock 1 = 1 := by
  simp [gammaBlock]

/-- The block encoding of minus one is the two-point swap matrix. -/
lemma gammaBlock_neg_one : gammaBlock (-1) = !![0, 1; 1, 0] := by
  simp [gammaBlock]

/-- Every entry of the block encoding of zero vanishes. -/
lemma gammaBlock_zero_apply (s t : Fin 2) : gammaBlock 0 s t = 0 := by
  simp [gammaBlock]

/-- The entries of `gammaBlock 1` are one on the diagonal and zero elsewhere. -/
lemma gammaBlock_one_apply (s t : Fin 2) : gammaBlock 1 s t = if s = t then 1 else 0 := by
  simp [gammaBlock, Matrix.one_apply]

/-- The entries of `gammaBlock (-1)` are one exactly at the two off-diagonal positions. -/
lemma gammaBlock_neg_one_apply (s t : Fin 2) :
    gammaBlock (-1) s t = if s = 0 ∧ t = 1 then 1 else if s = 1 ∧ t = 0 then 1 else 0 := by
  fin_cases s <;> fin_cases t <;> simp [gammaBlock]

/-- For `a` in `{-1, 0, 1}`, a row of `gammaBlock a` contains no nonzero entries if `a = 0`, and
one otherwise. -/
lemma gammaBlock_row_nz (a : ℤ) (ha : a = 0 ∨ a = 1 ∨ a = -1) (s : Fin 2) :
    (univ.filter (fun t : Fin 2 => gammaBlock a s t ≠ 0)).card =
      if a = 0 then 0 else 1 := by
  have hs : s = 0 ∨ s = 1 := by fin_cases s <;> simp
  rcases ha with rfl | rfl | rfl
  · simp [gammaBlock]
  · rcases hs with rfl | rfl
    · rw [show (univ.filter (fun t : Fin 2 => gammaBlock 1 (0:Fin 2) t ≠ 0)) = {0} by
        ext t; fin_cases t <;> simp [gammaBlock, Matrix.one_apply]]
      simp
    · rw [show (univ.filter (fun t : Fin 2 => gammaBlock 1 (1:Fin 2) t ≠ 0)) = {1} by
        ext t; fin_cases t <;> simp [gammaBlock, Matrix.one_apply]]
      simp
  · rcases hs with rfl | rfl
    · rw [show (univ.filter (fun t : Fin 2 => gammaBlock (-1) (0:Fin 2) t ≠ 0)) = {1} by
        ext t; fin_cases t <;> simp [gammaBlock]]
      simp
    · rw [show (univ.filter (fun t : Fin 2 => gammaBlock (-1) (1:Fin 2) t ≠ 0)) = {0} by
        ext t; fin_cases t <;> simp [gammaBlock]]
      simp

/-- For `a` in `{-1, 0, 1}`, multiplication by `gammaBlock a` scales `phiMinus` by `a`. -/
lemma gammaBlock_mulVec_phiMinus (a : ℤ) (ha : a = 0 ∨ a = 1 ∨ a = -1) (s : Fin 2) :
    (∑ t : Fin 2, gammaBlock a s t * phiMinus t) = (a : ℝ) * phiMinus s := by
  rcases ha with rfl | rfl | rfl
  · simp [gammaBlock, phiMinus]
  · fin_cases s <;> simp [gammaBlock, phiMinus, Matrix.one_apply]
  · fin_cases s <;> simp [gammaBlock, phiMinus]

/-- For `a` in `{-1, 0, 1}`, multiplication by `gammaBlock a` scales `phiPlus` by `a ^ 2`. -/
lemma gammaBlock_mulVec_phiPlus (a : ℤ) (ha : a = 0 ∨ a = 1 ∨ a = -1) (s : Fin 2) :
    (∑ t : Fin 2, gammaBlock a s t * phiPlus t) = ((a : ℝ) ^ 2) * phiPlus s := by
  rcases ha with rfl | rfl | rfl
  · simp [gammaBlock, phiPlus]
  · fin_cases s <;> simp [gammaBlock, phiPlus, Matrix.one_apply]
  · fin_cases s <;> simp [gammaBlock, phiPlus]

/-- The product of two copies of the reciprocal of `√2` is `1 / 2`. -/
lemma hsq_sqrt_two : (Real.sqrt 2)⁻¹ * (Real.sqrt 2)⁻¹ = 1 / 2 := by
  have h2 : Real.sqrt 2 * Real.sqrt 2 = 2 := by
    rw [← sq, Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 2)]
  rw [← mul_inv, h2]
  norm_num

/-- The expectation of `gammaBlock a` in the antisymmetric vector is `a` when `a` belongs to
`{-1, 0, 1}`. -/
theorem phiMinus_expectation_gammaBlock (a : ℤ) (ha : a = 0 ∨ a = 1 ∨ a = -1) :
    (∑ s : Fin 2, ∑ t : Fin 2, phiMinus s * gammaBlock a s t * phiMinus t) = (a : ℝ) := by
  rcases ha with rfl | rfl | rfl <;>
    simp [gammaBlock, phiMinus, Fin.sum_univ_two, Matrix.one_apply] <;>
    nlinarith [hsq_sqrt_two]

/-- The product of two coordinates of `phiMinus` is `1 / 2` when their indices agree and `-1 /
2` otherwise. -/
lemma phiMinus_product (s t : Fin 2) :
    phiMinus s * phiMinus t = if s = t then (1/2 : ℝ) else (-1/2 : ℝ) := by
  fin_cases s <;> fin_cases t <;> simp [phiMinus, hsq_sqrt_two] <;> norm_num

/-- Expands the expectation in `psiMinus j` as a sum over the two-by-two block at vertex `j`. -/
lemma dot_psiMinus_expand {N : ℕ} (M : Matrix (Fin 2 × Fin N) (Fin 2 × Fin N) ℝ)
    (j : Fin N) :
    dot (psiMinus j) (M *ᵥ psiMinus j) =
      ∑ s : Fin 2, ∑ t : Fin 2, phiMinus s * M (s, j) (t, j) * phiMinus t := by
  classical
  have hinner : ∀ p : Fin 2 × Fin N,
      (∑ q, M p q * psiMinus j q) = ∑ t : Fin 2, M p (t, j) * phiMinus t := by
    intro p
    rw [Fintype.sum_prod_type]
    have hx : ∀ x : Fin 2, (∑ y, M p (x, y) * psiMinus j (x, y)) =
        M p (x, j) * phiMinus x := by
      intro x
      rw [Finset.sum_eq_single j]
      · simp [psiMinus, liftVec, Pi.single_eq_same]
      · intro k _ hk
        simp [psiMinus, liftVec, Pi.single_eq_of_ne hk]
      · intro h
        exact absurd (Finset.mem_univ j) h
    simp only [hx]
  unfold dot Matrix.mulVec
  simp only [dotProduct, hinner]
  have houter : ∀ s : Fin 2,
      (∑ i, psiMinus j (s, i) * (∑ t, M (s, i) (t, j) * phiMinus t)) =
        ∑ t, phiMinus s * M (s, j) (t, j) * phiMinus t := by
    intro s
    rw [Finset.sum_eq_single j]
    · simp only [psiMinus, liftVec, Pi.single_eq_same]
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun t _ => by ring
    · intro i _ hi
      simp [psiMinus, liftVec, Pi.single_eq_of_ne hi]
    · intro h
      exact absurd (Finset.mem_univ j) h
  rw [Fintype.sum_prod_type]
  exact Finset.sum_congr rfl fun s _ => houter s

/-- If the two-point block at `j` has equal diagonal entries and equal off-diagonal entries, its
antisymmetric expectation is `M (0, j) (0, j) - M (0, j) (1, j)`. -/
theorem phiMinus_bilinear_eq {N : ℕ} (M : Matrix (Fin 2 × Fin N) (Fin 2 × Fin N) ℝ)
    (j : Fin N)
    (hsym : M (0, j) (1, j) = M (1, j) (0, j))
    (hdiag : M (0, j) (0, j) = M (1, j) (1, j)) :
    dot (psiMinus j) (M *ᵥ psiMinus j) = M (0, j) (0, j) - M (0, j) (1, j) := by
  rw [dot_psiMinus_expand]
  have hrew : ∀ s t : Fin 2, phiMinus s * M (s, j) (t, j) * phiMinus t =
      (if s = t then (1/2:ℝ) else (-1/2:ℝ)) * M (s, j) (t, j) := by
    intro s t
    rw [show phiMinus s * M (s, j) (t, j) * phiMinus t =
        (phiMinus s * phiMinus t) * M (s, j) (t, j) by ring]
    rw [phiMinus_product]
  simp only [hrew, Fin.sum_univ_two]
  norm_num
  linarith [hsym, hdiag]

end Qatlib.Papers.BQPMixSparse06.MainResults
