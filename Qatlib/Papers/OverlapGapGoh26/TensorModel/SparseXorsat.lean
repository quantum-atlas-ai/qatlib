/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Foundations.MatrixAlgebra.TensorDiff

set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Qatlib.Foundations.MatrixAlgebra.TensorDiff

namespace Qatlib.Papers.OverlapGapGoh26.TensorModel.SparseXorsat

def bitSpin {N : ℕ} (x : Fin N → Bool) (i : Fin N) : ℝ := if x i then 1 else -1

def reward {E : Type} [Fintype E] {q N : ℕ}
    (ends : E → Fin q → Fin N) (J : E → ℝ) (z : Fin N → ℝ) : ℝ :=
  ∑ e,(1+J e*∏ a,z (ends e a))/2

def sparseTensor {E : Type} [Fintype E] {q N : ℕ}
    (ends : E → Fin q → Fin N) (J : E → ℝ) : Tensor q N :=
  fun k => ∑ e,if ends e=k then J e else 0

theorem actual_sparse_energy {E : Type} [Fintype E] {q N : ℕ}
    (ends : E → Fin q → Fin N) (J : E → ℝ) (z : Fin N → ℝ) :
    tensorEnergy (sparseTensor ends J) z=∑ e,J e*∏ a,z (ends e a) := by
  classical
  unfold tensorEnergy sparseTensor
  simp_rw [Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro e _
  simp

theorem reward_eq_sparse_energy {E : Type} [Fintype E] {q N : ℕ}
    (ends : E → Fin q → Fin N) (J : E → ℝ) (z : Fin N → ℝ) :
    reward ends J z=(Fintype.card E:ℝ)/2+tensorEnergy (sparseTensor ends J) z/2 := by
  rw [actual_sparse_energy]
  unfold reward
  simp_rw [add_div]
  rw [Finset.sum_add_distrib,← Finset.sum_div]
  simp [Finset.sum_div]

theorem binary_constraint_range {E : Type} [Fintype E] {q N : ℕ}
    (ends : E → Fin q → Fin N) (J : E → ℝ) (hJ : ∀ e,J e∈({-1,1} : Set ℝ))
    (x : Fin N → Bool) (e : E) : (1+J e*∏ a,bitSpin x (ends e a))/2∈Set.Icc (0:ℝ) 1 := by
  have hp : (∏ a,bitSpin x (ends e a))^2=1 := by
    rw [← Finset.prod_pow]
    apply Finset.prod_eq_one
    intro a _
    unfold bitSpin
    cases x (ends e a) <;> norm_num
  have hj : (J e)^2=1 := by
    rcases (Set.mem_insert_iff.mp (hJ e)) with h|h
    · rw [h]; norm_num
    · have he : J e=1 := Set.mem_singleton_iff.mp h
      rw [he]; norm_num
  have he : (J e*∏ a,bitSpin x (ends e a))^2=1 := by rw [mul_pow,hj,hp,one_mul]
  constructor <;> nlinarith

theorem binary_reward_range {E : Type} [Fintype E] {q N : ℕ}
    (ends : E → Fin q → Fin N) (J : E → ℝ) (hJ : ∀ e,J e∈({-1,1} : Set ℝ))
    (x : Fin N → Bool) : reward ends J (bitSpin x)∈Set.Icc (0:ℝ) (Fintype.card E) := by
  constructor
  · exact Finset.sum_nonneg (fun e _ => (binary_constraint_range ends J hJ x e).1)
  · calc
      _ ≤ ∑ _e : E,(1:ℝ) := Finset.sum_le_sum (fun e _ => (binary_constraint_range ends J hJ x e).2)
      _ = _ := by simp

def incidenceDegree {E : Type} [Fintype E] {q N : ℕ}
    (ends : E → Fin q → Fin N) (i : Fin N) : ℕ :=
  ∑ e,∑ a,if ends e a=i then 1 else 0

theorem actual_incidence_sum {E : Type} [Fintype E] {q N : ℕ}
    (ends : E → Fin q → Fin N) : ∑ i,incidenceDegree ends i=Fintype.card E*q := by
  classical
  unfold incidenceDegree
  calc
    _ = ∑ e,∑ a,∑ i,if ends e a=i then 1 else 0 := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro e _
      rw [Finset.sum_comm]
    _ = _ := by simp

theorem regular_divisibility {E : Type} [Fintype E] {q N : ℕ}
    (ends : E → Fin q → Fin N) (d : ℕ) (hd : ∀ i,incidenceDegree ends i=d) : q∣N*d := by
  have h := actual_incidence_sum ends
  simp_rw [hd] at h
  simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,Nat.cast_id] at h
  rw [h]
  exact dvd_mul_left q (Fintype.card E)

end Qatlib.Papers.OverlapGapGoh26.TensorModel.SparseXorsat
