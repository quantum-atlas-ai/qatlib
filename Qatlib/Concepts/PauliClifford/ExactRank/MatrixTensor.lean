/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Foundations.PureStateMath.BornBridge.RepresentationBridge

/-!
# Tensor products of single-qubit matrices

This module defines `pauliProductDensity` by multiplying single-qubit matrix entries over
Boolean registers and defines `tensorPauliProduct` by relabeling the result to `Fin (2 ^ n)`.
Both constructions accept arbitrary complex single-qubit operators, and their algebraic
identities supply tensor-product calculations used in quantum information [NielsenChuang2010].

## Main statements

* `pauliProductDensity_mul` and `tensorPauliProduct_mul` identify products with coordinatewise
  matrix multiplication.
* `pauliProductDensity_trace` and `tensorPauliProduct_trace` factor traces into products of
  local traces.
* `tensorPauliProduct_sum` and `tensorPauliProduct_smul` describe finite sums and local scalar
  factors.
* `tensorPauliTrace_relabel_mul` transports a trace pairing across an index equivalence.

## References

* [Nielsen and Chuang, 2010][NielsenChuang2010]
-/

set_option backward.isDefEq.respectTransparency false

open Qatlib.Foundations.PureStateMath
open Qatlib.Foundations.PureStateMath.BornBridge

set_option autoImplicit false

namespace Qatlib.Concepts.PauliClifford.ExactRank

open Matrix
open scoped ComplexOrder

/-- The matrix on Boolean registers whose entries are products of the corresponding entries of
the supplied single-qubit operators. No positivity or trace condition is required of the
factors. -/
noncomputable def pauliProductDensity {n : ℕ} (ρ : Fin n → Operator 2) :
    Matrix (Reg n) (Reg n) ℂ :=
  Matrix.of fun x y => ∏ i, (ρ i) (boolEquivFin2 (x i)) (boolEquivFin2 (y i))

/-- Conjugate transposition of the product matrix equals the product matrix of the
conjugate-transposed local factors. -/
theorem pauliProductDensity_conjTranspose {n : ℕ} (A : Fin n → Operator 2) :
    (pauliProductDensity A)ᴴ = pauliProductDensity (fun i => (A i)ᴴ) := by
  ext x y
  simp [pauliProductDensity, Matrix.conjTranspose_apply]

/-- Multiplying two product matrices equals forming the product matrix from coordinatewise
products of their local factors. -/
theorem pauliProductDensity_mul {n : ℕ} (A B : Fin n → Operator 2) :
    pauliProductDensity A * pauliProductDensity B =
      pauliProductDensity (fun i => A i * B i) := by
  ext x y
  simp only [Matrix.mul_apply, pauliProductDensity, Matrix.of_apply]
  simp_rw [← Finset.prod_mul_distrib]
  rw [← Fintype.prod_sum (fun i b =>
    A i (boolEquivFin2 (x i)) (boolEquivFin2 b) *
      B i (boolEquivFin2 b) (boolEquivFin2 (y i)))]
  apply Finset.prod_congr rfl
  intro i _
  exact (Equiv.sum_comp boolEquivFin2
    (fun k => A i (boolEquivFin2 (x i)) k * B i k (boolEquivFin2 (y i))))

/-- The product matrix with the identity at every coordinate is the identity on the Boolean
register. -/
theorem pauliProductDensity_one (n : ℕ) :
    pauliProductDensity (fun _ : Fin n => (1 : Operator 2)) = 1 := by
  ext x y
  by_cases h : x = y
  · subst y
    simp [pauliProductDensity]
  · obtain ⟨i, hi⟩ := Function.ne_iff.mp h
    have hb : boolEquivFin2 (x i) ≠ boolEquivFin2 (y i) :=
      fun he => hi (boolEquivFin2.injective he)
    rw [Matrix.one_apply_ne h]
    apply Finset.prod_eq_zero (Finset.mem_univ i)
    exact Matrix.one_apply_ne hb

/-- The trace of a product matrix is the product of the traces of its local factors. -/
theorem pauliProductDensity_trace {n : ℕ} (A : Fin n → Operator 2) :
    Matrix.trace (pauliProductDensity A) = ∏ i, Matrix.trace (A i) := by
  change (∑ x : Reg n, ∏ i, A i (boolEquivFin2 (x i)) (boolEquivFin2 (x i))) = _
  rw [← Fintype.prod_sum (fun i b => A i (boolEquivFin2 b) (boolEquivFin2 b))]
  apply Finset.prod_congr rfl
  intro i _
  exact Equiv.sum_comp boolEquivFin2 (fun k => A i k k)

/-- Summing product matrices over all independent choices of local labels equals the product
matrix of the local sums. -/
theorem pauliProductDensity_sum {n : ℕ} {O : Type*} [Fintype O]
    (A : Fin n → O → Operator 2) :
    (∑ o : Fin n → O, pauliProductDensity (fun i => A i (o i))) =
      pauliProductDensity (fun i => ∑ o, A i o) := by
  ext x y
  simp only [Matrix.sum_apply, pauliProductDensity, Matrix.of_apply]
  exact (Fintype.prod_sum
    (fun i o => A i o (boolEquivFin2 (x i)) (boolEquivFin2 (y i)))).symm

/-- Scaling each local factor scales the product matrix by the product of all local scalars. -/
theorem pauliProductDensity_smul {n : ℕ} (c : Fin n → ℂ) (A : Fin n → Operator 2) :
    pauliProductDensity (fun i => c i • A i) = (∏ i, c i) • pauliProductDensity A := by
  ext x y
  simp [pauliProductDensity, Finset.prod_mul_distrib]

/-- The product of the supplied single-qubit matrices, relabeled from Boolean registers to an
operator of dimension `2 ^ n` using `bitVecEquiv`. -/
noncomputable def tensorPauliProduct (n : ℕ) (A : Fin n → Operator 2) : Operator (2 ^ n) :=
  relabelGate (bitVecEquiv n) (pauliProductDensity A)

/-- The relabeled tensor product preserves coordinatewise multiplication of local factors. -/
theorem tensorPauliProduct_mul (n : ℕ) (A B : Fin n → Operator 2) :
    tensorPauliProduct n A * tensorPauliProduct n B =
      tensorPauliProduct n (fun i => A i * B i) := by
  simp only [tensorPauliProduct, relabelGate, Matrix.reindex_apply,
    Matrix.submatrix_mul_equiv, pauliProductDensity_mul]

/-- Conjugate transposition of the relabeled tensor product acts on each local factor
separately. -/
theorem tensorPauliProduct_conjTranspose (n : ℕ) (A : Fin n → Operator 2) :
    (tensorPauliProduct n A)ᴴ = tensorPauliProduct n (fun i => (A i)ᴴ) := by
  simp only [tensorPauliProduct, relabelGate, Matrix.reindex_apply,
    Matrix.conjTranspose_submatrix, pauliProductDensity_conjTranspose]

/-- The relabeled tensor product of single-qubit identities is the identity operator of
dimension `2 ^ n`. -/
theorem tensorPauliProduct_one (n : ℕ) :
    tensorPauliProduct n (fun _ => 1) = 1 := by
  simp only [tensorPauliProduct, pauliProductDensity_one, relabelGate,
    Matrix.reindex_apply, Matrix.submatrix_one_equiv]

/-- The trace of the relabeled tensor product is the product of the traces of its local factors. -/
theorem tensorPauliProduct_trace (n : ℕ) (A : Fin n → Operator 2) :
    Matrix.trace (tensorPauliProduct n A) = ∏ i, Matrix.trace (A i) := by
  change (∑ x, pauliProductDensity A ((bitVecEquiv n).symm x)
    ((bitVecEquiv n).symm x)) = _
  rw [Equiv.sum_comp (bitVecEquiv n).symm (fun x => pauliProductDensity A x x)]
  exact pauliProductDensity_trace A

/-- The sum of relabeled tensor products over independent local labels equals the relabeled
tensor product of the local sums. -/
theorem tensorPauliProduct_sum (n : ℕ) {O : Type*} [Fintype O]
    (A : Fin n → O → Operator 2) :
    (∑ o : Fin n → O, tensorPauliProduct n (fun i => A i (o i))) =
      tensorPauliProduct n (fun i => ∑ o, A i o) := by
  unfold tensorPauliProduct
  rw [← pauliProductDensity_sum A]
  ext; simp only [relabelGate, Matrix.reindex_apply, Matrix.sum_apply,
    Matrix.submatrix_apply]

/-- Local scalar multiplication contributes the product of the scalars to the relabeled tensor
product. -/
theorem tensorPauliProduct_smul (n : ℕ) (c : Fin n → ℂ) (A : Fin n → Operator 2) :
    tensorPauliProduct n (fun i => c i • A i) = (∏ i, c i) • tensorPauliProduct n A := by
  unfold tensorPauliProduct
  rw [pauliProductDensity_smul]
  rfl

/-- Reindexing both indices of a square matrix by an equivalence preserves its trace. -/
theorem tensorPauliTrace_submatrix {I J : Type*} [Fintype I] [Fintype J]
    [DecidableEq I] [DecidableEq J] (e : I ≃ J) (A : Matrix J J ℂ) :
    Matrix.trace (A.submatrix e e) = Matrix.trace A :=
  Equiv.sum_comp e (fun i => A i i)

/-- The trace pairing of a relabeled matrix with `B` equals the trace pairing of the original
matrix with `B` pulled back along the index equivalence. -/
theorem tensorPauliTrace_relabel_mul {I J : Type*} [Fintype I] [Fintype J]
    [DecidableEq I] [DecidableEq J] (e : I ≃ J)
    (A : Matrix I I ℂ) (B : Matrix J J ℂ) :
    Matrix.trace (relabelGate e A * B) = Matrix.trace (A * B.submatrix e e) := by
  rw [← tensorPauliTrace_submatrix e (relabelGate e A * B)]
  rw [← Matrix.submatrix_mul_equiv (relabelGate e A) B e e e]
  congr 2
  ext
  simp [relabelGate]

end Qatlib.Concepts.PauliClifford.ExactRank
