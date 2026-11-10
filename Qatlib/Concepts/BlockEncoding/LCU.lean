/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.Execution.WorkspaceCP.ProjectedUnitaryEncoding
set_option backward.isDefEq.respectTransparency false
set_option warningAsError false

open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.Execution.WorkspaceCP

namespace Qatlib.Concepts.BlockEncoding.LCU

open Matrix

variable {J I : Type*} [Fintype J] [Fintype I] [DecidableEq J] [DecidableEq I]

noncomputable def prepareLift (a : J → ℂ) : Matrix (J × I) I ℂ :=
  Matrix.of fun p i => if p.2 = i then a p.1 else 0

noncomputable def select (U : J → Matrix I I ℂ) : Matrix (J × I) (J × I) ℂ :=
  Matrix.of fun p q => if p.1 = q.1 then U p.1 p.2 q.2 else 0

noncomputable def lcuMatrix (a : J → ℂ) (U : J → Matrix I I ℂ) : Matrix I I ℂ :=
  ∑ j, (star (a j) * a j) • U j

noncomputable def lcuBilinearMatrix (a b : J → ℂ) (U : J → Matrix I I ℂ) : Matrix I I ℂ :=
  ∑ j, (star (a j) * b j) • U j

omit [DecidableEq J] in

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

theorem prepare_select_compress (a : J → ℂ) (U : J → Matrix I I ℂ) :
    compress (prepareLift a) (select U) (prepareLift a) = lcuMatrix a U := by
  classical
  unfold compress
  rw [Matrix.mul_assoc, select_mul_prepareLift]
  ext i k
  simp [prepareLift, lcuMatrix, Matrix.mul_apply, Matrix.conjTranspose_apply,
    Fintype.sum_prod_type, apply_ite, ite_mul, Matrix.sum_apply, Matrix.smul_apply, mul_assoc]

theorem prepare_select_compress_bilinear (a b : J → ℂ) (U : J → Matrix I I ℂ) :
    compress (prepareLift a) (select U) (prepareLift b) = lcuBilinearMatrix a b U := by
  classical
  unfold compress
  rw [Matrix.mul_assoc, select_mul_prepareLift]
  ext i k
  simp [prepareLift, lcuBilinearMatrix, Matrix.mul_apply, Matrix.conjTranspose_apply,
    Fintype.sum_prod_type, apply_ite, ite_mul, Matrix.sum_apply, Matrix.smul_apply, mul_assoc]

omit [Fintype I] [DecidableEq J] [DecidableEq I] in

theorem lcuBilinearMatrix_eq_sum (a b c : J → ℂ) (U : J → Matrix I I ℂ)
    (hc : ∀ j, star (a j) * b j = c j) :
    lcuBilinearMatrix a b U = ∑ j, c j • U j := by
  classical
  unfold lcuBilinearMatrix
  apply Finset.sum_congr rfl
  intro j _
  rw [hc j]

theorem lcu_projectedUnitaryEncoding (a : J → ℂ) (U : J → Matrix I I ℂ)
    (ha : ∑ j, star (a j) * a j = 1)
    (hU : ∀ j, U j ∈ Matrix.unitaryGroup I ℂ) :
    ProjectedUnitaryEncoding (lcuMatrix a U) (select U) (prepareLift a) (prepareLift a) :=
  ⟨select_unitary U hU, prepareLift_isIsometry a ha, prepareLift_isIsometry a ha,
    prepare_select_compress a U⟩

theorem lcuBilinear_projectedUnitaryEncoding (a b : J → ℂ) (U : J → Matrix I I ℂ)
    (ha : ∑ j, star (a j) * a j = 1) (hb : ∑ j, star (b j) * b j = 1)
    (hU : ∀ j, U j ∈ Matrix.unitaryGroup I ℂ) :
    ProjectedUnitaryEncoding (lcuBilinearMatrix a b U) (select U)
      (prepareLift a) (prepareLift b) :=
  ⟨select_unitary U hU, prepareLift_isIsometry a ha, prepareLift_isIsometry b hb,
    prepare_select_compress_bilinear a b U⟩

theorem lcu_factorized_projectedUnitaryEncoding (a b c : J → ℂ)
    (U : J → Matrix I I ℂ) (ha : ∑ j, star (a j) * a j = 1)
    (hb : ∑ j, star (b j) * b j = 1) (hc : ∀ j, star (a j) * b j = c j)
    (hU : ∀ j, U j ∈ Matrix.unitaryGroup I ℂ) :
    ProjectedUnitaryEncoding (∑ j, c j • U j) (select U) (prepareLift a) (prepareLift b) := by
  rw [← lcuBilinearMatrix_eq_sum a b c U hc]
  exact lcuBilinear_projectedUnitaryEncoding a b U ha hb hU

end Qatlib.Concepts.BlockEncoding.LCU
