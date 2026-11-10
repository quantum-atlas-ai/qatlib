/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Matrix.Mul
import Mathlib.LinearAlgebra.Matrix.Hermitian
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Real.Sqrt
import Mathlib.Tactic

set_option autoImplicit false
noncomputable section

open Finset

namespace Qatlib.Papers.DiagPowerBQP06.MainResults.OffDiagonal

def bilin {N : ℕ} (B : Matrix (Fin N) (Fin N) ℝ) (v w : Fin N → ℝ) : ℝ :=
  ∑ a, ∑ b, v a * B a b * w b

def quad {N : ℕ} (B : Matrix (Fin N) (Fin N) ℝ) (v : Fin N → ℝ) : ℝ :=
  bilin B v v

def basis {N : ℕ} (i : Fin N) : Fin N → ℝ := fun k => if k = i then 1 else 0

def plusState {N : ℕ} (i j : Fin N) : Fin N → ℝ :=
  (Real.sqrt 2)⁻¹ • (basis i + basis j)

def minusState {N : ℕ} (i j : Fin N) : Fin N → ℝ :=
  (Real.sqrt 2)⁻¹ • (basis i - basis j)

theorem bilin_add_left {N : ℕ} (B : Matrix (Fin N) (Fin N) ℝ)
    (v w w' : Fin N → ℝ) :
    bilin B (v + w) w' = bilin B v w' + bilin B w w' := by
  unfold bilin
  simp only [Pi.add_apply]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro a _
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro b _
  ring

theorem bilin_add_right {N : ℕ} (B : Matrix (Fin N) (Fin N) ℝ)
    (v w w' : Fin N → ℝ) :
    bilin B v (w + w') = bilin B v w + bilin B v w' := by
  unfold bilin
  simp only [Pi.add_apply]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro a _
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro b _
  ring

theorem bilin_sub_left {N : ℕ} (B : Matrix (Fin N) (Fin N) ℝ)
    (v w w' : Fin N → ℝ) :
    bilin B (v - w) w' = bilin B v w' - bilin B w w' := by
  unfold bilin
  simp only [Pi.sub_apply]
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro a _
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro b _
  ring

theorem bilin_sub_right {N : ℕ} (B : Matrix (Fin N) (Fin N) ℝ)
    (v w w' : Fin N → ℝ) :
    bilin B v (w - w') = bilin B v w - bilin B v w' := by
  unfold bilin
  simp only [Pi.sub_apply]
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro a _
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro b _
  ring

theorem bilin_smul_left {N : ℕ} (B : Matrix (Fin N) (Fin N) ℝ) (c : ℝ)
    (v w : Fin N → ℝ) :
    bilin B (c • v) w = c * bilin B v w := by
  unfold bilin
  simp only [Pi.smul_apply, smul_eq_mul]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro a _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro b _
  ring

theorem bilin_smul_right {N : ℕ} (B : Matrix (Fin N) (Fin N) ℝ) (c : ℝ)
    (v w : Fin N → ℝ) :
    bilin B v (c • w) = c * bilin B v w := by
  unfold bilin
  simp only [Pi.smul_apply, smul_eq_mul]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro a _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro b _
  ring

theorem bilin_basis_basis {N : ℕ} (B : Matrix (Fin N) (Fin N) ℝ) (i j : Fin N) :
    bilin B (basis i) (basis j) = B i j := by
  unfold bilin
  rw [Finset.sum_eq_single i]
  · rw [Finset.sum_eq_single j]
    · simp [basis]
    · intro b _ hbj
      simp [basis, hbj]
    · intro hj
      exact absurd (Finset.mem_univ j) hj
  · intro a _ hai
    simp [basis, hai]
  · intro hi
    exact absurd (Finset.mem_univ i) hi

theorem offdiag_quadratic_identity {N : ℕ} (B : Matrix (Fin N) (Fin N) ℝ)
    (hB : B.IsHermitian) (i j : Fin N) (hij : i ≠ j) :
    quad B (plusState i j) - quad B (minusState i j) = 2 * B i j := by
  have hplus : quad B (plusState i j)
      = (Real.sqrt 2)⁻¹ * ((Real.sqrt 2)⁻¹ *
          ((B i i + B i j) + (B j i + B j j))) := by
    unfold quad plusState
    simp only [bilin_smul_left, bilin_smul_right, bilin_add_left, bilin_add_right,
      bilin_basis_basis] <;> ring
  have hminus : quad B (minusState i j)
      = (Real.sqrt 2)⁻¹ * ((Real.sqrt 2)⁻¹ *
          ((B i i - B i j) - (B j i - B j j))) := by
    unfold quad minusState
    simp only [bilin_smul_left, bilin_smul_right, bilin_sub_left, bilin_sub_right,
      bilin_basis_basis] <;> ring
  rw [hplus, hminus]
  have hsym : B j i = B i j := by
    simpa using hB.apply i j
  have hsq : Real.sqrt 2 * Real.sqrt 2 = 2 := by
    rw [← pow_two, Real.sq_sqrt (by norm_num)]
  have hc2 : (Real.sqrt 2)⁻¹ * (Real.sqrt 2)⁻¹ = (1 / 2 : ℝ) := by
    calc (Real.sqrt 2)⁻¹ * (Real.sqrt 2)⁻¹ = (Real.sqrt 2 * Real.sqrt 2)⁻¹ := by
          rw [mul_inv_rev]
      _ = (2 : ℝ)⁻¹ := by rw [hsq]
      _ = 1 / 2 := by norm_num
  have hcc : ∀ X : ℝ, (Real.sqrt 2)⁻¹ * ((Real.sqrt 2)⁻¹ * X) = X / 2 := by
    intro X
    rw [← mul_assoc, hc2]
    ring
  simp only [hsym]
  rw [hcc, hcc]
  ring

theorem isHermitian_pow {N : ℕ} (A : Matrix (Fin N) (Fin N) ℝ)
    (hA : A.IsHermitian) (m : ℕ) : (A ^ m).IsHermitian :=
  Matrix.isHermitian_iff_isSelfAdjoint.mpr
    ((Matrix.isHermitian_iff_isSelfAdjoint.mp hA).pow m)

end Qatlib.Papers.DiagPowerBQP06.MainResults.OffDiagonal
