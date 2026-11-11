/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Data.Matrix.Mul
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Tactic

/-!
# Linear hashes for syndrome correction

The map `finiteLinearMatrixHash` pairs a vector with each column of a finite matrix over a
commutative ring. It is multiplication by the transpose matrix and preserves subtraction and
finite linear combinations.

The correction lemmas remove prescribed hash contributions or add combinations from the hash
kernel without changing the target. They provide algebraic tools for linear syndrome
calculations in quantum error correction; see [Wilde2017] for background.

## Main statements

* `hash_eq_transpose_mulVec`: identifies the hash with transpose matrix multiplication.
* `finite_linear_matrix_hash_scaled_correction`: removes a specified linear combination of hash
  contributions.
* `finite_linear_matrix_hash_scaled_grid_correction`: handles corrections with scaled coordinate
  hashes.
* `finite_linear_matrix_hash_kernel_shift`: preserves the hash under kernel shifts.

## References

* [Wilde, 2017][Wilde2017]
-/

set_option autoImplicit false

open Matrix
namespace Qatlib.Concepts.CodingDecoding.CssRecovery.LinearSyndrome

open scoped BigOperators

/-- The finite linear hash that pairs the input vector with each column of `A` over a
commutative ring. -/
def finiteLinearMatrixHash {K I J : Type} [CommRing K] [Fintype I]
    (A : Matrix I J K) (v : I → K) : J → K := fun j => ∑ i, A i j * v i

/-- The finite linear matrix hash is multiplication by the transpose of its matrix. -/
theorem hash_eq_transpose_mulVec {K I J : Type} [CommRing K] [Fintype I]
    (A : Matrix I J K) (v : I → K) : finiteLinearMatrixHash A v = A.transpose *ᵥ v := rfl

/-- The finite linear matrix hash preserves subtraction. -/
theorem finite_linear_matrix_hash_sub
    {K I J : Type} [CommRing K] [Fintype I]
    (A : Matrix I J K) (v w : I → K) :
    finiteLinearMatrixHash A (v - w) =
      finiteLinearMatrixHash A v - finiteLinearMatrixHash A w := by
  funext j
  change (∑ i : I, A i j * (v i - w i)) =
    (∑ i : I, A i j * v i) - ∑ i : I, A i j * w i
  calc
    (∑ i : I, A i j * (v i - w i)) =
        ∑ i : I, (A i j * v i - A i j * w i) := by
          apply Finset.sum_congr rfl
          intro i _
          rw [mul_sub]
    _ = (∑ i : I, A i j * v i) - ∑ i : I, A i j * w i :=
      by rw [Finset.sum_sub_distrib]

/-- The hash of a finite linear combination is the corresponding linear combination of the
hashes. -/
theorem finite_linear_matrix_hash_smul_sum
    {K I J P : Type} [CommRing K] [Fintype I] [Fintype P]
    (A : Matrix I J K) (g : P → I → K) (digits : P → K) :
    finiteLinearMatrixHash A (fun i => ∑ p : P, digits p * g p i) =
      ∑ p : P, digits p • finiteLinearMatrixHash A (g p) := by
  funext j
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  change (∑ i : I, A i j * (∑ p : P, digits p * g p i)) =
    ∑ p : P, digits p * (∑ i : I, A i j * g p i)
  calc
    (∑ i : I, A i j * (∑ p : P, digits p * g p i)) =
        ∑ i : I, ∑ p : P, A i j * (digits p * g p i) := by
      apply Finset.sum_congr rfl
      intro i hi
      rw [Finset.mul_sum (Finset.univ : Finset P)]
    _ = ∑ p : P, ∑ i : I, A i j * (digits p * g p i) := by
      rw [Finset.sum_comm]
    _ = ∑ p : P, digits p * (∑ i : I, A i j * g p i) := by
      apply Finset.sum_congr rfl
      intro p hp
      rw [Finset.mul_sum (Finset.univ : Finset I)]
      apply Finset.sum_congr rfl
      intro i hi
      ring

/-- Subtracting a linear combination of correction vectors removes the matching hash
contribution and leaves the target hash. -/
theorem finite_linear_matrix_hash_scaled_correction
    {K I J P : Type} [CommRing K] [Fintype I] [Fintype P]
    (A : Matrix I J K) (c₀ : I → K) (g : P → I → K)
    (digits : P → K) (target : J → K)
    (hbase : finiteLinearMatrixHash A c₀ =
      target + ∑ p : P, digits p • finiteLinearMatrixHash A (g p)) :
    finiteLinearMatrixHash A
        (fun i => c₀ i - ∑ p : P, digits p * g p i) = target := by
  let w : I → K := fun i => ∑ p : P, digits p * g p i
  have hw : (fun i => c₀ i - ∑ p : P, digits p * g p i) = c₀ - w := by
    funext i
    rfl
  rw [hw, finite_linear_matrix_hash_sub]
  have hsum : finiteLinearMatrixHash A w =
      ∑ p : P, digits p • finiteLinearMatrixHash A (g p) := by
    exact finite_linear_matrix_hash_smul_sum A g digits
  rw [hsum, hbase]
  funext j
  simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
  ring

/-- Correction vectors whose hashes form a scaled coordinate grid remove the prescribed
coordinate offsets from the hash. -/
theorem finite_linear_matrix_hash_scaled_grid_correction
    {K I J : Type} [CommRing K] [Fintype I] [Fintype J] [DecidableEq J]
    (A : Matrix I J K) (c₀ : I → K) (g : J → I → K)
    (digits : J → K) (k : K) (u : J → K)
    (hbase : finiteLinearMatrixHash A c₀ =
      u + (fun j => k * digits j))
    (hgen : ∀ p j, finiteLinearMatrixHash A (g p) j =
      if p = j then k else 0) :
    finiteLinearMatrixHash A
        (fun i => c₀ i - ∑ p : J, digits p * g p i) = u := by
  apply finite_linear_matrix_hash_scaled_correction A c₀ g digits u
  have hsum :
      (∑ p : J, digits p • finiteLinearMatrixHash A (g p)) =
        (fun j => k * digits j) := by
    funext j
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    calc
      (∑ p : J, digits p * finiteLinearMatrixHash A (g p) j) =
          ∑ p : J, digits p * (if p = j then k else 0) := by
            apply Finset.sum_congr rfl
            intro p _
            rw [hgen p j]
      _ = digits j * k := by simp
      _ = k * digits j := by ring
  rw [hsum]
  exact hbase

/-- Adding a linear combination of vectors in the hash kernel leaves the target hash unchanged. -/
theorem finite_linear_matrix_hash_kernel_shift
    {K I J P : Type} [CommRing K] [Fintype I] [Fintype P]
    (A : Matrix I J K) (c : I → K) (g : P → I → K)
    (digits : P → K) (target : J → K)
    (hbase : finiteLinearMatrixHash A c = target)
    (hkernel : ∀ p : P, finiteLinearMatrixHash A (g p) = 0) :
    finiteLinearMatrixHash A
        (fun i => c i + ∑ p : P, digits p * g p i) = target := by
  let w : I → K := fun i => ∑ p : P, digits p * g p i
  have hw : (fun i => c i + ∑ p : P, digits p * g p i) = c + w := by
    funext i
    rfl
  have hadd : finiteLinearMatrixHash A (c + w) =
      finiteLinearMatrixHash A c + finiteLinearMatrixHash A w := by
    funext j
    change (∑ i : I, A i j * (c i + w i)) =
      (∑ i : I, A i j * c i) + ∑ i : I, A i j * w i
    calc
      (∑ i : I, A i j * (c i + w i)) =
          ∑ i : I, (A i j * c i + A i j * w i) := by
            apply Finset.sum_congr rfl
            intro i _
            rw [mul_add]
      _ = (∑ i : I, A i j * c i) + ∑ i : I, A i j * w i :=
        Finset.sum_add_distrib
  have hsum := finite_linear_matrix_hash_smul_sum A g digits
  have hzero : finiteLinearMatrixHash A w = 0 := by
    rw [hsum]
    simp [hkernel]
  rw [hw, hadd, hbase, hzero, add_zero]

/-- A linear combination of vectors in the hash kernel also lies in the kernel. -/
theorem finite_linear_matrix_hash_kernel_combination
    {K I J P : Type} [CommRing K] [Fintype I] [Fintype P]
    (A : Matrix I J K) (g : P → I → K) (digits : P → K)
    (hkernel : ∀ p : P, finiteLinearMatrixHash A (g p) = 0) :
    finiteLinearMatrixHash A
        (fun i => ∑ p : P, digits p * g p i) = 0 := by
  rw [finite_linear_matrix_hash_smul_sum]
  simpa [hkernel]

/-- Two vectors have the same hash when their difference lies in the hash kernel. -/
theorem finite_linear_matrix_hash_eq_of_sub_kernel
    {K I J : Type} [CommRing K] [Fintype I]
    (A : Matrix I J K) (c d : I → K)
    (hkernel : finiteLinearMatrixHash A (c - d) = 0) :
    finiteLinearMatrixHash A c = finiteLinearMatrixHash A d := by
  have hsub := finite_linear_matrix_hash_sub A c d
  have hzero : finiteLinearMatrixHash A c - finiteLinearMatrixHash A d = 0 := by
    rw [← hsub]
    exact hkernel
  exact sub_eq_zero.mp hzero

end Qatlib.Concepts.CodingDecoding.CssRecovery.LinearSyndrome
