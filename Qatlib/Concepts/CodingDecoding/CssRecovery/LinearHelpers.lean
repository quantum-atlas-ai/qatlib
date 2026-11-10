/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Data.Matrix.Mul
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Tactic

set_option autoImplicit false

open Matrix
namespace Qatlib.Concepts.CodingDecoding.CssRecovery.LinearSyndrome

open scoped BigOperators

def finiteLinearMatrixHash {K I J : Type} [CommRing K] [Fintype I]
    (A : Matrix I J K) (v : I → K) : J → K := fun j => ∑ i, A i j * v i

theorem hash_eq_transpose_mulVec {K I J : Type} [CommRing K] [Fintype I]
    (A : Matrix I J K) (v : I → K) : finiteLinearMatrixHash A v = A.transpose *ᵥ v := rfl

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

theorem finite_linear_matrix_hash_kernel_combination
    {K I J P : Type} [CommRing K] [Fintype I] [Fintype P]
    (A : Matrix I J K) (g : P → I → K) (digits : P → K)
    (hkernel : ∀ p : P, finiteLinearMatrixHash A (g p) = 0) :
    finiteLinearMatrixHash A
        (fun i => ∑ p : P, digits p * g p i) = 0 := by
  rw [finite_linear_matrix_hash_smul_sum]
  simpa [hkernel]

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
