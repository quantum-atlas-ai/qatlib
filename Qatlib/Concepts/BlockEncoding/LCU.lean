/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.Execution.WorkspaceCP.ProjectedUnitaryEncoding

/-!
# Linear combinations through preparation frames

`prepareLift` embeds a system using preparation amplitudes, while `select` applies a matrix
controlled by the preparation label. Their compression yields `lcuMatrix` or the two-vector
variant `lcuBilinearMatrix`, giving projected unitary encodings when the amplitudes are
normalized and the selected matrices are unitary.

The mathematical background is described in [GilyenSuLowWiebe2019].

## Main statements

* `prepare_select_compress_bilinear`: compression gives the bilinear coefficient sum.
* `lcu_factorized_projectedUnitaryEncoding`: encoding for coefficients factored through two unit
  vectors.

## References

* [Gilyén et al., 2019][GilyenSuLowWiebe2019]
-/

set_option backward.isDefEq.respectTransparency false

open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.Execution.WorkspaceCP

namespace Qatlib.Concepts.BlockEncoding.LCU

open Matrix

variable {J I : Type*} [Fintype J] [Fintype I] [DecidableEq J] [DecidableEq I]

/-- The embedding tensoring the system with the amplitude vector `a` on the preparation
register. -/
noncomputable def prepareLift (a : J → ℂ) : Matrix (J × I) I ℂ :=
  Matrix.of fun p i => if p.2 = i then a p.1 else 0

/-- The block diagonal matrix applying `U j` on the system when the preparation register equals
`j`. -/
noncomputable def select (U : J → Matrix I I ℂ) : Matrix (J × I) (J × I) ℂ :=
  Matrix.of fun p q => if p.1 = q.1 then U p.1 p.2 q.2 else 0

/-- The linear combination of `U j` with coefficients `star (a j) * a j`. -/
noncomputable def lcuMatrix (a : J → ℂ) (U : J → Matrix I I ℂ) : Matrix I I ℂ :=
  ∑ j, (star (a j) * a j) • U j

/-- The linear combination of `U j` with coefficients `star (a j) * b j`. -/
noncomputable def lcuBilinearMatrix (a b : J → ℂ) (U : J → Matrix I I ℂ) : Matrix I I ℂ :=
  ∑ j, (star (a j) * b j) • U j

omit [DecidableEq J] in

/-- The preparation lift is an isometry when its amplitude vector has squared norm one. -/
theorem prepareLift_isIsometry (a : J → ℂ) (ha : ∑ j, star (a j) * a j = 1) :
    IsIsometry (prepareLift (I := I) a) := by
  classical
  unfold IsIsometry
  ext i k
  by_cases h : i = k
  · subst k
    simpa [prepareLift, Matrix.mul_apply, Matrix.conjTranspose_apply,
      Fintype.sum_prod_type, mul_ite] using ha
  · simp [prepareLift, Matrix.mul_apply, Matrix.conjTranspose_apply,
      Fintype.sum_prod_type, mul_ite, h, Ne.symm h]

/-- Multiplying selection by the preparation lift gives entries `a p.1 * U p.1 p.2 i`. -/
theorem select_mul_prepareLift (a : J → ℂ) (U : J → Matrix I I ℂ) :
    @HMul.hMul (Matrix (J × I) (J × I) ℂ) (Matrix (J × I) I ℂ)
      (Matrix (J × I) I ℂ) Matrix.instHMulOfFintypeOfMulOfAddCommMonoid
      (select U) (prepareLift (I := I) a) =
      Matrix.of (fun p i => a p.1 * U p.1 p.2 i) := by
  classical
  ext p i
  rcases p with ⟨j, k⟩
  rw [Matrix.mul_apply]
  simp [select, prepareLift, Fintype.sum_prod_type, mul_ite, mul_comm]

/-- Controlled selection is unitary when every selected matrix is unitary. -/
theorem select_unitary (U : J → Matrix I I ℂ)
    (hU : ∀ j, U j ∈ Matrix.unitaryGroup I ℂ) :
    select U ∈ Matrix.unitaryGroup (J × I) ℂ := by
  classical
  rw [Matrix.mem_unitaryGroup_iff', Matrix.star_eq_conjTranspose]
  ext p q
  rcases p with ⟨j, i⟩
  rcases q with ⟨k, l⟩
  by_cases h : j = k
  · subst k
    have hu := hU j
    rw [Matrix.mem_unitaryGroup_iff', Matrix.star_eq_conjTranspose] at hu
    have he := congrFun (congrFun hu i) l
    simpa [select, Matrix.mul_apply, Matrix.conjTranspose_apply,
      Fintype.sum_prod_type, mul_ite, Matrix.one_apply] using he
  · simp [select, Matrix.mul_apply, Matrix.conjTranspose_apply,
      Fintype.sum_prod_type, mul_ite, h, Ne.symm h]

/-- Compressing selection with the same preparation vector on both sides gives `lcuMatrix`. -/
theorem prepare_select_compress (a : J → ℂ) (U : J → Matrix I I ℂ) :
    compress (prepareLift a) (select U) (prepareLift a) = lcuMatrix a U := by
  classical
  unfold compress
  rw [Matrix.mul_assoc, select_mul_prepareLift]
  ext i k
  simp [prepareLift, lcuMatrix, Matrix.mul_apply, Matrix.conjTranspose_apply,
    Fintype.sum_prod_type, apply_ite, ite_mul, Matrix.sum_apply, Matrix.smul_apply, mul_assoc]

/-- Compressing selection between two preparation lifts gives `lcuBilinearMatrix`. -/
theorem prepare_select_compress_bilinear (a b : J → ℂ) (U : J → Matrix I I ℂ) :
    compress (prepareLift a) (select U) (prepareLift b) = lcuBilinearMatrix a b U := by
  classical
  unfold compress
  rw [Matrix.mul_assoc, select_mul_prepareLift]
  ext i k
  simp [prepareLift, lcuBilinearMatrix, Matrix.mul_apply, Matrix.conjTranspose_apply,
    Fintype.sum_prod_type, apply_ite, ite_mul, Matrix.sum_apply, Matrix.smul_apply, mul_assoc]

omit [Fintype I] [DecidableEq J] [DecidableEq I] in

/-- A pointwise factorization `star (a j) * b j = c j` identifies the bilinear LCU with the
coefficient sum. -/
theorem lcuBilinearMatrix_eq_sum (a b c : J → ℂ) (U : J → Matrix I I ℂ)
    (hc : ∀ j, star (a j) * b j = c j) :
    lcuBilinearMatrix a b U = ∑ j, c j • U j := by
  classical
  unfold lcuBilinearMatrix
  apply Finset.sum_congr rfl
  intro j _
  rw [hc j]

/-- Normalized preparation amplitudes and unitary components give a projected unitary encoding
of `lcuMatrix`. -/
theorem lcu_projectedUnitaryEncoding (a : J → ℂ) (U : J → Matrix I I ℂ)
    (ha : ∑ j, star (a j) * a j = 1)
    (hU : ∀ j, U j ∈ Matrix.unitaryGroup I ℂ) :
    ProjectedUnitaryEncoding (lcuMatrix a U) (select U) (prepareLift a) (prepareLift a) :=
  ⟨select_unitary U hU, prepareLift_isIsometry a ha, prepareLift_isIsometry a ha,
    prepare_select_compress a U⟩

/-- Two normalized preparation vectors and unitary components give a projected unitary encoding
of the bilinear LCU. -/
theorem lcuBilinear_projectedUnitaryEncoding (a b : J → ℂ) (U : J → Matrix I I ℂ)
    (ha : ∑ j, star (a j) * a j = 1) (hb : ∑ j, star (b j) * b j = 1)
    (hU : ∀ j, U j ∈ Matrix.unitaryGroup I ℂ) :
    ProjectedUnitaryEncoding (lcuBilinearMatrix a b U) (select U)
      (prepareLift a) (prepareLift b) :=
  ⟨select_unitary U hU, prepareLift_isIsometry a ha, prepareLift_isIsometry b hb,
    prepare_select_compress_bilinear a b U⟩

/-- Coefficients factored as conjugate products of two normalized vectors yield a projected
unitary encoding of their linear combination. -/
theorem lcu_factorized_projectedUnitaryEncoding (a b c : J → ℂ)
    (U : J → Matrix I I ℂ) (ha : ∑ j, star (a j) * a j = 1)
    (hb : ∑ j, star (b j) * b j = 1) (hc : ∀ j, star (a j) * b j = c j)
    (hU : ∀ j, U j ∈ Matrix.unitaryGroup I ℂ) :
    ProjectedUnitaryEncoding (∑ j, c j • U j) (select U) (prepareLift a) (prepareLift b) := by
  rw [← lcuBilinearMatrix_eq_sum a b c U hc]
  exact lcuBilinear_projectedUnitaryEncoding a b U ha hb hU

end Qatlib.Concepts.BlockEncoding.LCU
