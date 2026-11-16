/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Papers.BoolEquation17.MainResults.Support
public import Mathlib.Algebra.BigOperators.Fin

@[expose] public section


/-!
# Zero-equation, zero-right-hand-side padding of least-squares residuals

This proves the old Lean Lemma 2.8 contract, which appends `0x = 0`. The pinned
paper's Lemma 2.8 instead appends `0x = 1` and compares normalized HHL solution
states; that state and singular-value bridge is outside the theorem below.
-/
set_option autoImplicit false
noncomputable section
open scoped BigOperators
namespace Qatlib.Papers.BoolEquation17.MainResults.Padding

/-- Pad a complex matrix with zero rows. -/
def padRows {M N : ℕ} (A : Matrix (Fin M) (Fin N) ℂ) (k : ℕ) :
    Matrix (Fin (M + k)) (Fin N) ℂ :=
  fun i j => if h : (i : ℕ) < M then A ⟨(i : ℕ), h⟩ j else 0

/-- Pad a complex vector with zero entries. -/
def padVec {M : ℕ} (b : CVec M) (k : ℕ) : CVec (M + k) :=
  fun i => if h : (i : ℕ) < M then b ⟨(i : ℕ), h⟩ else 0

/-- Zero padding preserves the explicitly defined Euclidean norm. -/
theorem l2_padVec {M : ℕ} (b : CVec M) (k : ℕ) :
    l2Norm (padVec b k) = l2Norm b := by
  unfold l2Norm
  congr 1
  rw [Fin.sum_univ_add]
  have hfirst : (∑ i : Fin M, Complex.normSq (padVec b k (Fin.castAdd k i))) =
      ∑ i : Fin M, Complex.normSq (b i) := by
    apply Finset.sum_congr rfl
    intro i _
    simp [padVec, i.isLt]
  have hlast : (∑ i : Fin k, Complex.normSq (padVec b k (Fin.natAdd M i))) = 0 := by
    apply Finset.sum_eq_zero
    intro i _
    have hnot : ¬ M + (i : ℕ) < M := by omega
    simp [padVec, hnot]
  rw [hfirst, hlast, add_zero]

/-- The residual of the padded system is the zero-padded original residual. -/
theorem pad_residual {M N : ℕ} (A : Matrix (Fin M) (Fin N) ℂ) (b : CVec M)
    (x : CVec N) (k : ℕ) :
    (padRows A k).mulVec x - padVec b k = padVec (A.mulVec x - b) k := by
  funext i
  by_cases hi : (i : ℕ) < M
  · simp [padRows, padVec, Matrix.mulVec, dotProduct, hi]
  · simp [padRows, padVec, Matrix.mulVec, dotProduct, hi]

/-- Zero matrix rows and zero right-hand-side entries preserve the Euclidean residual norm. -/
theorem pad_res_norm {M N : ℕ} (A : Matrix (Fin M) (Fin N) ℂ) (b : CVec M)
    (x : CVec N) (k : ℕ) :
    l2Norm ((padRows A k).mulVec x - padVec b k) = l2Norm (A.mulVec x - b) := by
  rw [pad_residual, l2_padVec]

/-- The old zero-equation-padding Lemma 2.8 preserves precisely the least-squares minimizers. -/
theorem lemma_2_8 (M N k : ℕ) (A : Matrix (Fin M) (Fin N) ℂ) (b : CVec M) :
    ∀ x : CVec N,
      IsLeastSquaresSolution (padRows A k) (padVec b k) x ↔ IsLeastSquaresSolution A b x := by
  intro x
  unfold IsLeastSquaresSolution
  simp only [pad_res_norm]

end Qatlib.Papers.BoolEquation17.MainResults.Padding
