/-
Copyright (c) 2026 Quantum Atlas Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quantum Atlas Contributors
-/

module

public import Qatlib.Concepts.GramQueryCore.QfiCompletion.MqfiSeparabilityDefs
public import Mathlib.Data.Fin.Basic

@[expose] public section

set_option autoImplicit false
set_option maxHeartbeats 1800000
noncomputable section
namespace Qatlib.Concepts.GramQueryCore.QfiCompletion
open scoped Classical BigOperators Matrix

/-- Padding both matrices with zero columns preserves their product with the second transpose. -/
theorem mqfiPadCols_mul_transpose {r q n : ℕ} (A B : Matrix (Fin r) (Fin q) ℝ) :
    mqfiPadCols (n := n) A*(mqfiPadCols (n := n) B).transpose=A*B.transpose := by
  ext s t
  simp only [Matrix.mul_apply,Matrix.transpose_apply]
  rw [Fin.sum_univ_add]
  simp [mqfiPadCols,Fin.val_castAdd,Fin.val_natAdd]

/-- The MQFI completion is Hermitian whenever each auxiliary matrix `K a` is Hermitian. -/
theorem mqfiCompletion_isHermitian {p r q n : ℕ}
    (B : Fin p → Matrix (Fin r) (Fin q) ℝ)
    (K : Fin p → Matrix (Fin (q+n)) (Fin (q+n)) ℂ) (hK : ∀ a,(K a).IsHermitian) (a : Fin p) :
    (mqfiCompletion B K a).IsHermitian := by
  unfold mqfiCompletion
  apply Matrix.IsHermitian.fromBlocks
  · exact Matrix.isHermitian_zero
  · rfl
  · exact hK a

/-- The upper-left block of a product of MQFI completions equals the corresponding MQFI block. -/
theorem mqfiCompletion_product_top {p r q n : ℕ}
    (B : Fin p → Matrix (Fin r) (Fin q) ℝ)
    (K : Fin p → Matrix (Fin (q+n)) (Fin (q+n)) ℂ)
    (a b : Fin p) (s t : Fin r) :
    (mqfiCompletion B K a*mqfiCompletion B K b) (Sum.inl s) (Sum.inl t)=
      (mqfiBlocks B (a,s) (b,t) : ℂ) := by
  have hpad := congrFun (congrFun (mqfiPadCols_mul_transpose (n := n) (B a) (B b)) s) t
  simp only [Matrix.mul_apply,Matrix.transpose_apply] at hpad
  simp only [mqfiCompletion,Matrix.mul_apply,Fintype.sum_sum_type,
    Matrix.fromBlocks_apply₁₁,Matrix.fromBlocks_apply₁₂,Matrix.fromBlocks_apply₂₁,
    Matrix.zero_apply,zero_mul,Finset.sum_const_zero,zero_add,Matrix.map_apply,Matrix.conjTranspose_apply]
  change (∑ j : Fin (q+n),(mqfiPadCols (B a) s j : ℂ)*star (mqfiPadCols (B b) t j : ℂ))=_
  simp only [Complex.star_def,Complex.conj_ofReal,← Complex.ofReal_mul,← Complex.ofReal_sum]
  rw [hpad]
  rfl
end Qatlib.Concepts.GramQueryCore.QfiCompletion

set_option autoImplicit false
set_option maxHeartbeats 2400000
open scoped Classical BigOperators Matrix
namespace Qatlib.Concepts.GramQueryCore.QfiCompletion.MqfiNPHard2026
noncomputable section

/-- Matrices with a common orthonormal-column spectral representation multiply by multiplying
their diagonal weights. -/
theorem mqfi_spectral_product {J L : Type*} [Fintype J] [Fintype L] [DecidableEq L]
    (U : Matrix J L ℂ) (hU : U.conjTranspose*U=1) (d e : L → ℝ) :
    (U*Matrix.diagonal (fun j => (d j : ℂ))*U.conjTranspose)*
      (U*Matrix.diagonal (fun j => (e j : ℂ))*U.conjTranspose)=
      U*Matrix.diagonal (fun j => ((d j*e j : ℝ) : ℂ))*U.conjTranspose := by
  simp only [Matrix.mul_assoc]
  rw [← Matrix.mul_assoc U.conjTranspose U (Matrix.diagonal (fun j => (e j : ℂ))*U.conjTranspose),
    hU,Matrix.one_mul,← Matrix.mul_assoc (Matrix.diagonal (fun j => (d j : ℂ)))
      (Matrix.diagonal (fun j => (e j : ℂ))) U.conjTranspose,Matrix.diagonal_mul_diagonal]
  simp only [Complex.ofReal_mul]
end
noncomputable section

/-- Each entry of the spectral product is the sum of products of the diagonal weights and the
corresponding conjugate matrix entries. -/
theorem mqfi_spectral_product_entry {J L : Type*} [Fintype J] [Fintype L] [DecidableEq L]
    (U : Matrix J L ℂ) (hU : U.conjTranspose*U=1) (d e : L → ℝ) (s t : J) :
    ((U*Matrix.diagonal (fun j => (d j : ℂ))*U.conjTranspose)*
      (U*Matrix.diagonal (fun j => (e j : ℂ))*U.conjTranspose)) s t=
      ∑ j : L,U s j*((d j*e j : ℝ) : ℂ)*star (U t j) := by
  rw [mqfi_spectral_product U hU d e,Matrix.mul_apply]
  apply Finset.sum_congr rfl
  intro j _
  rw [Matrix.mul_diagonal,Matrix.conjTranspose_apply]
end
end Qatlib.Concepts.GramQueryCore.QfiCompletion.MqfiNPHard2026
