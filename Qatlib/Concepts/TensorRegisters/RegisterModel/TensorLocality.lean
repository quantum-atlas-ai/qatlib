/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.TensorRegisters.RegisterModel.QmaCompletenessLocalSupport
import Mathlib.Tactic

/-!
# Tensor locality on qubit supports

The predicate `TensorLocalOn S H` expresses that `H` is a matrix on the support `S` tensored
with the identity on the complement, using the canonical register split. Products of single-wire
matrices are local when all off-support factors are identities, and locality is preserved by
linear combinations and adjoints. For background, see [KitaevShenVyalyi2002].

## Main statements

* `productMatrix_tensor_local`: support of a product of single-wire matrices.
* `tensorLocalOn_adjoint`: locality is preserved by conjugate transpose.

## References

* [Kitaev, Shen, and Vyalyi, 2002][KitaevShenVyalyi2002]
-/

set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false
noncomputable section

open Matrix
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.TensorRegisters.RegisterModel

namespace Qatlib.Concepts.TensorRegisters.RegisterModel

/-- The property that `H` is the partition lift of some matrix on the ordered support register
`S`. -/
def TensorLocalOn {N : ℕ} (S : Finset (Fin N)) (H : Matrix (Reg N) (Reg N) ℂ) : Prop :=
  ∃ M : Matrix (Reg S.card) (Reg S.card) ℂ, H = partitionLift (split S) M

/-- A product of single-wire matrices is local on `S` when every factor outside `S` is the
identity. -/
theorem productMatrix_tensor_local {N : ℕ} (S : Finset (Fin N))
    (A : Fin N → Matrix Bool Bool ℂ) (hA : ∀ i, i ∉ S → A i = 1) :
    TensorLocalOn S (productMatrix A) := by
  classical
  let B : Matrix (Reg S.card) (Reg S.card) ℂ :=
    productMatrix (fun i : Fin S.card => A (wireEmbedding S i))
  refine ⟨B, eq_partitionLift_of_entries S (productMatrix A) B ?_⟩
  intro x y
  by_cases he : outside S x = outside S y
  · rw [if_pos he]
    have hout := (outside_eq_iff S x y).mp he
    have hp : (∏ i ∈ S, A i (x i) (y i)) = ∏ i : Fin N, A i (x i) (y i) := by
      apply Finset.prod_subset (Finset.subset_univ S)
      intro i _ hi
      rw [hA i hi, Matrix.one_apply, if_pos (hout i hi)]
    change (∏ i : Fin N, A i (x i) (y i)) =
      ∏ j : Fin S.card, A (wireEmbedding S j) (x (wireEmbedding S j)) (y (wireEmbedding S j))
    rw [← hp, ← Finset.prod_coe_sort]
    symm
    apply Fintype.prod_equiv (S.orderIsoOfFin rfl).toEquiv
    intro i
    rfl
  · rw [if_neg he]
    have hex : ∃ i : Fin N, i ∉ S ∧ x i ≠ y i := by
      by_contra h
      push Not at h
      exact he ((outside_eq_iff S x y).mpr h)
    obtain ⟨i, hi, hxy⟩ := hex
    apply Finset.prod_eq_zero (Finset.mem_univ i)
    rw [hA i hi, Matrix.one_apply, if_neg hxy]

/-- The sum of two matrices local on `S` is local on `S`. -/
theorem tensorLocalOn_add {N : ℕ} (S : Finset (Fin N))
    {A B : Matrix (Reg N) (Reg N) ℂ} (hA : TensorLocalOn S A) (hB : TensorLocalOn S B) :
    TensorLocalOn S (A + B) := by
  obtain ⟨a, rfl⟩ := hA
  obtain ⟨b, rfl⟩ := hB
  refine ⟨a + b, eq_partitionLift_of_entries S _ _ ?_⟩
  intro x y
  simp only [Matrix.add_apply, partitionLift_apply]
  split_ifs <;> simp

/-- Multiplying a matrix local on `S` by a complex scalar preserves locality on `S`. -/
theorem tensorLocalOn_smul {N : ℕ} (S : Finset (Fin N))
    {A : Matrix (Reg N) (Reg N) ℂ} (hA : TensorLocalOn S A) (c : ℂ) :
    TensorLocalOn S (c • A) := by
  obtain ⟨a, rfl⟩ := hA
  refine ⟨c • a, eq_partitionLift_of_entries S _ _ ?_⟩
  intro x y
  simp only [Matrix.smul_apply, partitionLift_apply]
  split_ifs <;> simp

/-- The conjugate transpose of a matrix local on `S` remains local on `S`. -/
theorem tensorLocalOn_adjoint {N : ℕ} (S : Finset (Fin N))
    {A : Matrix (Reg N) (Reg N) ℂ} (hA : TensorLocalOn S A) :
    TensorLocalOn S Aᴴ := by
  obtain ⟨a, rfl⟩ := hA
  refine ⟨aᴴ, eq_partitionLift_of_entries S _ _ ?_⟩
  intro x y
  simp only [Matrix.conjTranspose_apply, partitionLift_apply]
  by_cases h : outside S x = outside S y
  · simp only [if_pos h, if_pos h.symm]
  · simp only [if_neg h, if_neg (Ne.symm h), star_zero]

end Qatlib.Concepts.TensorRegisters.RegisterModel
