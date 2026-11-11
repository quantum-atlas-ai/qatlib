/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.GramQueryCore.GramRealization.GramQueryRealization
import Qatlib.Concepts.BlockEncoding.EncodingCore.AncillaErrorLaws
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Order
import Mathlib.Analysis.Matrix.Order

/-!
# Contractions from Gram matrix domination

This module proves a finite-dimensional contraction factorization from positive semidefinite
domination of Gram matrices. `gram_dominated_contraction` constructs a matrix `V` with operator
norm at most 1 and `V * X = Y` when `Xᴴ * X - Yᴴ * Y` is positive semidefinite. The matrix
positivity and operator norm framework is standard in [Bhatia1997].

When `Xᴴ * X` is invertible, `gram_full_rank_transfer` verifies the explicit transfer matrix `Y
* (Xᴴ * X)⁻¹ * Xᴴ`.

## Main statements

* `gram_dominated_contraction`: existence of a contraction realizing the prescribed matrix
  transfer.
* `gram_full_rank_transfer`: the explicit transfer formula in the full column rank case.

## References

* [Bhatia, 1997][Bhatia1997]
-/

set_option backward.isDefEq.respectTransparency false
set_option warningAsError false

namespace Qatlib.Concepts.MpsAdaptation.MpsTransfer
open Matrix
open scoped Matrix.Norms.L2Operator MatrixOrder ComplexOrder
noncomputable local instance {I : Type} [Fintype I] [DecidableEq I] :
    CStarAlgebra (Matrix I I ℂ) where
variable {I O C : Type} [Fintype I] [DecidableEq I]
  [Fintype O] [DecidableEq O] [Fintype C] [DecidableEq C]

omit [DecidableEq O] in

/-- If `1 - Vᴴ * V` is positive semidefinite, then the operator norm of `V` is at most 1. -/
private theorem norm_le_one_of_defect (V : Matrix O I ℂ)
    (h : (1-Vᴴ*V).PosSemidef) : ‖V‖ ≤ 1 := by
  have hb : Vᴴ*V ≤ 1 := sub_nonneg.mp h.nonneg
  have hn := (CStarAlgebra.norm_le_one_iff_of_nonneg (Vᴴ*V)
    (Matrix.posSemidef_conjTranspose_mul_self V).nonneg).mpr hb
  rw [Matrix.l2_opNorm_conjTranspose_mul_self] at hn
  nlinarith [norm_nonneg V]

/-- If the Gram matrix of `X` dominates that of `Y`, there exists a contraction `V` satisfying
`V * X = Y`. -/
theorem gram_dominated_contraction (X : Matrix I C ℂ) (Y : Matrix O C ℂ)
    (h : (Xᴴ*X-Yᴴ*Y).PosSemidef) : ∃ V : Matrix O I ℂ, ‖V‖ ≤ 1 ∧ V*X=Y := by
  obtain ⟨W,hW⟩ :=
      Qatlib.Concepts.GramQueryCore.GramRealization.gram_positive_matrix_actual_factorization C _ h
  let R : Matrix (I ⊕ (O ⊕ C)) I ℂ := Matrix.fromRows 1 0
  let L : Matrix (I ⊕ (O ⊕ C)) O ℂ := Matrix.fromRows 0 (Matrix.fromRows 1 0)
  let B : Matrix (I ⊕ (O ⊕ C)) C ℂ := Matrix.fromRows 0 (Matrix.fromRows Y W)
  have hR : Qatlib.Concepts.Execution.WorkspaceCP.IsIsometry R := by
    simp [Qatlib.Concepts.Execution.WorkspaceCP.IsIsometry,R,
      Matrix.conjTranspose_fromRows_eq_fromCols_conjTranspose,Matrix.fromCols_mul_fromRows]
  have hL : Qatlib.Concepts.Execution.WorkspaceCP.IsIsometry L := by
    simp [Qatlib.Concepts.Execution.WorkspaceCP.IsIsometry,L,
      Matrix.conjTranspose_fromRows_eq_fromCols_conjTranspose,Matrix.fromCols_mul_fromRows]
  have hg : (R*X)ᴴ*(R*X)=Bᴴ*B := by
    have hl : (R*X)ᴴ*(R*X)=Xᴴ*X := by
      calc
        _ = Xᴴ*(Rᴴ*R)*X := by simp only [Matrix.conjTranspose_mul,Matrix.mul_assoc]
        _ = Xᴴ*X := by rw [hR,Matrix.mul_one]
    rw [hl]
    simp only [B,Matrix.conjTranspose_fromRows_eq_fromCols_conjTranspose,
      Matrix.fromCols_mul_fromRows,Matrix.conjTranspose_zero,Matrix.zero_mul,zero_add,hW]
    abel
  obtain ⟨U,hU,he⟩ :=
      Qatlib.Concepts.GramQueryCore.GramRealization.gram_equal_actual_unitary_transport _ _
      (R*X) B hg
  refine ⟨Lᴴ*U*R,Qatlib.Concepts.BlockEncoding.EncodingCore.l2_norm_compress_le_one hL hU hR,?_⟩
  calc
    _ = Lᴴ*(U*(R*X)) := by simp only [Matrix.mul_assoc]
    _ = Lᴴ*B := by rw [he]
    _ = Y := by simp [L,B,Matrix.conjTranspose_fromRows_eq_fromCols_conjTranspose,
      Matrix.fromCols_mul_fromRows]

omit [DecidableEq O] in

/-- If `Xᴴ * X` is invertible and dominates `Yᴴ * Y`, then `Y * (Xᴴ * X)⁻¹ * Xᴴ` has operator
norm at most 1 and maps `X` to `Y`. -/
theorem gram_full_rank_transfer (X : Matrix I C ℂ) (Y : Matrix O C ℂ)
    (hX : IsUnit (Xᴴ*X).det) (h : (Xᴴ*X-Yᴴ*Y).PosSemidef) :
    let V := Y*(Xᴴ*X)⁻¹*Xᴴ
    ‖V‖ ≤ 1 ∧ V*X=Y := by
  let T := Xᴴ*X
  let L := T⁻¹*Xᴴ
  let P := X*L
  let V := Y*L
  have hLX : L*X=1 := by
    dsimp [L,T]
    rw [Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hX]
  have hP : Pᴴ=P := by
    dsimp [P,L,T]
    simp only [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose,
      (Matrix.isHermitian_conjTranspose_mul_self X).inv.eq, Matrix.mul_assoc]
  have hPP : P*P=P := by
    dsimp [P]
    calc
      X*L*(X*L) = X*(L*X)*L := by simp only [Matrix.mul_assoc]
      _ = X*L := by rw [hLX, Matrix.mul_one]
  have hgram : Lᴴ*(Xᴴ*X)*L=P := by
    calc
      _ = (X*L)ᴴ*(X*L) := by simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
      _ = P := by change Pᴴ*P=P; rw [hP,hPP]
  have hid : (1-P)ᴴ*(1-P) + Lᴴ*(Xᴴ*X-Yᴴ*Y)*L = 1-Vᴴ*V := by
    simp only [Matrix.conjTranspose_sub, Matrix.conjTranspose_one, hP,
      Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, Matrix.one_mul]
    rw [hPP, hgram]
    have hv : Lᴴ*(Yᴴ*Y)*L=Vᴴ*V := by
      dsimp [V]
      simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
    rw [hv]
    abel
  have hpos : (1-Vᴴ*V).PosSemidef := by
    rw [← hid]
    exact (Matrix.posSemidef_conjTranspose_mul_self (1-P)).add
      (h.conjTranspose_mul_mul_same L)
  change ‖Y*T⁻¹*Xᴴ‖ ≤ 1 ∧ (Y*T⁻¹*Xᴴ)*X=Y
  have hV : Y*T⁻¹*Xᴴ=V := Matrix.mul_assoc _ _ _
  rw [hV]
  refine ⟨norm_le_one_of_defect V hpos,?_⟩
  change Y*L*X=Y
  rw [Matrix.mul_assoc,hLX,Matrix.mul_one]
end Qatlib.Concepts.MpsAdaptation.MpsTransfer
