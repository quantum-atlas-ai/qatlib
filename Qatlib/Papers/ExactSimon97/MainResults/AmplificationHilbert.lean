/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.ExactSimon97.MainResults.GroverLemma
set_option warningAsError false

set_option autoImplicit false
set_option maxHeartbeats 1000000

noncomputable section

open scoped BigOperators

open Matrix

namespace Qatlib.Papers.ExactSimon97.MainResults

def e0 (d : ℕ) : Fin (d + 1) → ℂ := Pi.single 0 1

def ketBra {d : ℕ} (u v : Fin (d + 1) → ℂ) : Matrix (Fin (d + 1)) (Fin (d + 1)) ℂ :=
  Matrix.of (fun i j => u i * star (v j))

lemma e0_zero (d : ℕ) : e0 d 0 = 1 := by
  simp [e0]

lemma e0_ne (d : ℕ) {l : Fin (d + 1)} (hl : l ≠ 0) : e0 d l = 0 := by
  simp [e0, Pi.single_eq_of_ne hl]

lemma mul_ketBra_e0 (d : ℕ) (A : Matrix (Fin (d + 1)) (Fin (d + 1)) ℂ) :
    A * ketBra (e0 d) (e0 d) * Aᴴ = ketBra (A *ᵥ e0 d) (A *ᵥ e0 d) := by
  ext i j
  simp only [Matrix.mul_apply, ketBra, Matrix.of_apply, Matrix.mulVec, dotProduct]
  have hsumA : ∀ z : Fin (d + 1), (∑ x, A z x * e0 d x) = A z 0 := by
    intro z
    rw [Finset.sum_eq_single_of_mem 0 (Finset.mem_univ 0)]
    · rw [e0_zero, mul_one]
    · intro k _ hk
      rw [e0_ne d hk, mul_zero]
  have hinner : ∀ x : Fin (d + 1),
      (∑ x_1, A i x_1 * (e0 d x_1 * star (e0 d x))) = A i 0 * star (e0 d x) := by
    intro x
    rw [Finset.sum_eq_single_of_mem 0 (Finset.mem_univ 0)]
    · rw [e0_zero, one_mul]
    · intro k _ hk
      rw [e0_ne d hk, zero_mul, mul_zero]
  simp_rw [hinner]
  rw [Finset.sum_eq_single_of_mem 0 (Finset.mem_univ 0)]
  · rw [e0_zero, star_one, mul_one]
    rw [hsumA, hsumA, Matrix.conjTranspose_apply]
  · intro k _ hk
    rw [e0_ne d hk, star_zero, mul_zero, zero_mul]

theorem zeroRefl_conj (d : ℕ) (A : Matrix (Fin (d + 1)) (Fin (d + 1)) ℂ)
    (hA : A * Aᴴ = 1) :
    A * (1 + (Complex.I - 1) • ketBra (e0 d) (e0 d)) * Aᴴ =
      1 + (Complex.I - 1) • ketBra (A *ᵥ e0 d) (A *ᵥ e0 d) := by
  calc A * (1 + (Complex.I - 1) • ketBra (e0 d) (e0 d)) * Aᴴ
      = (A * 1 + A * ((Complex.I - 1) • ketBra (e0 d) (e0 d))) * Aᴴ := by
          rw [Matrix.mul_add]
    _ = (A * 1) * Aᴴ + (A * ((Complex.I - 1) • ketBra (e0 d) (e0 d))) * Aᴴ := by
          rw [Matrix.add_mul]
    _ = (A * 1) * Aᴴ + ((Complex.I - 1) • (A * ketBra (e0 d) (e0 d))) * Aᴴ := by
          rw [Matrix.mul_smul]
    _ = (A * 1) * Aᴴ + (Complex.I - 1) • ((A * ketBra (e0 d) (e0 d)) * Aᴴ) := by
          rw [smul_mul]
    _ = A * Aᴴ + (Complex.I - 1) • ((A * ketBra (e0 d) (e0 d)) * Aᴴ) := by
          rw [Matrix.mul_one]
    _ = 1 + (Complex.I - 1) • ketBra (A *ᵥ e0 d) (A *ᵥ e0 d) := by
          rw [hA, mul_ketBra_e0]

end Qatlib.Papers.ExactSimon97.MainResults
