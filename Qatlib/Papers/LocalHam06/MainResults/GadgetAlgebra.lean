/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.LinearAlgebra.Matrix.Kronecker
import Mathlib.Tactic

/-!
# Real matrix algebra for local gadgets

This module studies three explicit real two-by-two matrices and their quadratic forms, including
the skew-symmetric matrix `pauliY`. It proves coefficient bounds and expands three-factor
Kronecker products to isolate a residual in `twoLocalSpan`, supplying algebraic ingredients for
Lemma 8 of [KempeKitaevRegev2006].

## Main statements

* `gadget_B_lower`: Bounds the quadratic form of a shifted, scaled matrix from below.
* `kron_expand`: Expands a three-factor product into eight terms.
* `gadget_product_sub_mem_twoLocal`: Shows that subtracting the three-factor term leaves a
  two-local residual.

## References

* [Kempe et al., 2006][KempeKitaevRegev2006]
-/

noncomputable section

open Matrix
open scoped Kronecker BigOperators

namespace Qatlib.Papers.LocalHam06.MainResults.GadgetAlgebra

set_option autoImplicit false

/-- The real matrix with rows `(0, 1)` and `(1, 0)`. -/
def pauliX : Matrix (Fin 2) (Fin 2) ℝ := !![0, 1; 1, 0]

/-- The real skew-symmetric matrix with rows `(0, -1)` and `(1, 0)`. -/
def pauliY : Matrix (Fin 2) (Fin 2) ℝ := !![0, -1; 1, 0]

/-- The real diagonal matrix with diagonal entries one and negative one. -/
def pauliZ : Matrix (Fin 2) (Fin 2) ℝ := !![1, 0; 0, -1]

/-- The real quadratic form `∑ i, v i * (B *ᵥ v) i`. -/
def rayleighR {n : Type*} [Fintype n] (B : Matrix n n ℝ) (v : n → ℝ) : ℝ :=
  ∑ i, v i * (B.mulVec v) i

/-- The square of `pauliX` is the identity matrix. -/
theorem pauliX_sq : pauliX * pauliX = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [pauliX, Matrix.mul_apply, Fin.sum_univ_two]

/-- The square of the real skew-symmetric matrix `pauliY` is negative identity. -/
theorem pauliY_sq : pauliY * pauliY = -1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [pauliY, Matrix.mul_apply, Fin.sum_univ_two]

/-- The square of `pauliZ` is the identity matrix. -/
theorem pauliZ_sq : pauliZ * pauliZ = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [pauliZ, Matrix.mul_apply, Fin.sum_univ_two]

/-- The quadratic form of `pauliX` at `v` is `2 * v 0 * v 1`. -/
theorem rayleighR_pauliX (v : Fin 2 → ℝ) :
    rayleighR pauliX v = 2 * (v 0 * v 1) := by
  simp [rayleighR, pauliX, Matrix.mulVec, dotProduct, Fin.sum_univ_two]
  ring

/-- The quadratic form of the real skew-symmetric matrix `pauliY` is zero. -/
theorem rayleighR_pauliY (v : Fin 2 → ℝ) : rayleighR pauliY v = 0 := by
  simp [rayleighR, pauliY, Matrix.mulVec, dotProduct, Fin.sum_univ_two]
  ring

/-- The quadratic form of `pauliZ` is `v 0^2 - v 1^2`. -/
theorem rayleighR_pauliZ (v : Fin 2 → ℝ) :
    rayleighR pauliZ v = v 0 ^ 2 - v 1 ^ 2 := by
  simp [rayleighR, pauliZ, Matrix.mulVec, dotProduct, Fin.sum_univ_two]
  ring

/-- The quadratic form of any of the three listed real matrices is bounded below by the negative
squared Euclidean norm [KempeKitaevRegev2006]. -/
theorem rayleighR_pauli_lower (P : Matrix (Fin 2) (Fin 2) ℝ)
    (hP : P = pauliX ∨ P = pauliY ∨ P = pauliZ) (v : Fin 2 → ℝ) :
    -(∑ i, v i ^ 2) ≤ rayleighR P v := by
  rcases hP with rfl | rfl | rfl
  · rw [rayleighR_pauliX, Fin.sum_univ_two]
    nlinarith [sq_nonneg (v 0 + v 1), sq_nonneg (v 0 - v 1)]
  · rw [rayleighR_pauliY, Fin.sum_univ_two]
    nlinarith [sq_nonneg (v 0), sq_nonneg (v 1)]
  · rw [rayleighR_pauliZ, Fin.sum_univ_two]
    nlinarith [sq_nonneg (v 0), sq_nonneg (v 1)]

/-- The quadratic form of any of the three listed real matrices is bounded above by the squared
Euclidean norm. -/
theorem rayleighR_pauli_upper (P : Matrix (Fin 2) (Fin 2) ℝ)
    (hP : P = pauliX ∨ P = pauliY ∨ P = pauliZ) (v : Fin 2 → ℝ) :
    rayleighR P v ≤ ∑ i, v i ^ 2 := by
  rcases hP with rfl | rfl | rfl
  · rw [rayleighR_pauliX, Fin.sum_univ_two]
    nlinarith [sq_nonneg (v 0 - v 1)]
  · rw [rayleighR_pauliY, Fin.sum_univ_two]
    nlinarith [sq_nonneg (v 0), sq_nonneg (v 1)]
  · rw [rayleighR_pauliZ, Fin.sum_univ_two]
    nlinarith [sq_nonneg (v 0), sq_nonneg (v 1)]

/-- The quadratic form of `a • 1 + t • P` is `a` times the squared Euclidean norm plus `t` times
the quadratic form of `P`. -/
theorem rayleighR_smul_add {n : Type*} [Fintype n] [DecidableEq n] (a t : ℝ)
    (P : Matrix n n ℝ) (v : n → ℝ) :
    rayleighR (a • (1 : Matrix n n ℝ) + t • P) v
      = a * (∑ i, v i ^ 2) + t * rayleighR P v := by
  unfold rayleighR
  simp only [Matrix.add_mulVec, Matrix.smul_mulVec, Pi.add_apply, Pi.smul_apply, smul_eq_mul,
    Matrix.one_mulVec]
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  ring

/-- For `n ≥ 1` and `|t| ≤ 1 / n^3`, the quadratic form of `(2 / n^3) • 1 + t • P` is at least
`1 / n^3` times the squared norm for each listed matrix `P` [KempeKitaevRegev2006]. -/
theorem gadget_B_lower {n : ℝ} (hn : 1 ≤ n) (P : Matrix (Fin 2) (Fin 2) ℝ)
    (hP : P = pauliX ∨ P = pauliY ∨ P = pauliZ) {t : ℝ}
    (ht : |t| ≤ 1 / n ^ 3) (v : Fin 2 → ℝ) :
    (1 / n ^ 3) * (∑ i, v i ^ 2)
      ≤ rayleighR ((2 / n ^ 3) • (1 : Matrix (Fin 2) (Fin 2) ℝ) + t • P) v := by
  rw [rayleighR_smul_add]
  set S : ℝ := ∑ i, v i ^ 2 with hSdef
  set R : ℝ := rayleighR P v with hRdef
  have hS : 0 ≤ S := Finset.sum_nonneg (fun i _ => sq_nonneg (v i))
  have hlow : -S ≤ R := rayleighR_pauli_lower P hP v
  have hup : R ≤ S := rayleighR_pauli_upper P hP v
  have hRabs : |R| ≤ S := abs_le.mpr ⟨hlow, hup⟩
  have hn3 : (0 : ℝ) < n ^ 3 := by positivity
  have ht0 : 0 ≤ |t| := abs_nonneg t
  have hprod : |t| * |R| ≤ |t| * S := mul_le_mul_of_nonneg_left hRabs ht0
  have habs : |t * R| = |t| * |R| := abs_mul t R
  have hge : -( |t| * S ) ≤ t * R := by
    have h := neg_abs_le (t * R)
    rw [habs] at h
    linarith
  have hb : -( |t| * S ) ≥ -(1 / n ^ 3) * S := by
    have hle : |t| * S ≤ (1 / n ^ 3) * S := mul_le_mul_of_nonneg_right ht hS
    linarith
  have hcoef : (1 / n ^ 3) * S ≤ (2 / n ^ 3) * S - |t| * S := by
    have hle2 : |t| * S ≤ (1 / n ^ 3) * S := mul_le_mul_of_nonneg_right ht hS
    have hid : 2 / n ^ 3 - 1 / n ^ 3 = 1 / n ^ 3 := by ring
    nlinarith [hle2, hid]
  linarith

/-- Each entry of any of the three listed real matrices has absolute value at most one. -/
theorem pauli_entry_abs_le_one (P : Matrix (Fin 2) (Fin 2) ℝ)
    (hP : P = pauliX ∨ P = pauliY ∨ P = pauliZ) (i j : Fin 2) :
    |P i j| ≤ 1 := by
  rcases hP with h | h | h
  · subst h; fin_cases i <;> fin_cases j <;> simp [pauliX]
  · subst h; fin_cases i <;> fin_cases j <;> simp [pauliY]
  · subst h; fin_cases i <;> fin_cases j <;> simp [pauliZ]

/-- For `n ≥ 1` and `|t| ≤ 1 / n^3`, each entry of `(2 / n^3) • 1 + t • P` has absolute value at
most `3 / n^3` for each listed matrix `P` [KempeKitaevRegev2006]. -/
theorem gadget_B_entry_bound {n : ℝ} (hn : 1 ≤ n) (P : Matrix (Fin 2) (Fin 2) ℝ)
    (hP : P = pauliX ∨ P = pauliY ∨ P = pauliZ) {t : ℝ}
    (ht : |t| ≤ 1 / n ^ 3) (i j : Fin 2) :
    |((2 / n ^ 3) • (1 : Matrix (Fin 2) (Fin 2) ℝ) + t • P) i j| ≤ 3 / n ^ 3 := by
  have hn3 : (0 : ℝ) < n ^ 3 := by positivity
  have h1 : |(1 : Matrix (Fin 2) (Fin 2) ℝ) i j| ≤ 1 := by
    fin_cases i <;> fin_cases j <;> simp
  have hP1 : |P i j| ≤ 1 := pauli_entry_abs_le_one P hP i j
  have hA : |2 / n ^ 3 * (1 : Matrix (Fin 2) (Fin 2) ℝ) i j| ≤ 2 / n ^ 3 := by
    rw [abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 2 / n ^ 3)]
    calc 2 / n ^ 3 * |(1 : Matrix (Fin 2) (Fin 2) ℝ) i j| ≤ 2 / n ^ 3 * 1 :=
          mul_le_mul_of_nonneg_left h1 (by positivity)
      _ = 2 / n ^ 3 := mul_one _
  have hB : |t * P i j| ≤ 1 / n ^ 3 := by
    rw [abs_mul]
    have := mul_le_mul ht hP1 (abs_nonneg (P i j)) (by positivity : (0 : ℝ) ≤ 1 / n ^ 3)
    simpa using this
  simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
  have hsum : |2 / n ^ 3 * (1 : Matrix (Fin 2) (Fin 2) ℝ) i j + t * P i j|
      ≤ 2 / n ^ 3 + 1 / n ^ 3 :=
    le_trans (abs_add_le _ _) (add_le_add hA hB)
  have hid : 2 / n ^ 3 + 1 / n ^ 3 = 3 / n ^ 3 := by ring
  linarith [hsum, hid]

/-- The Kronecker product of three sums `ai • 1 + ti • Ai` expands into the eight terms obtained
by independently choosing an identity or matrix factor [KempeKitaevRegev2006]. -/
theorem kron_expand (a1 a2 a3 t1 t2 t3 : ℝ)
    (A1 A2 A3 : Matrix (Fin 2) (Fin 2) ℝ) :
    (a1 • (1 : Matrix (Fin 2) (Fin 2) ℝ) + t1 • A1) ⊗ₖ
        (a2 • (1 : Matrix (Fin 2) (Fin 2) ℝ) + t2 • A2) ⊗ₖ
        (a3 • (1 : Matrix (Fin 2) (Fin 2) ℝ) + t3 • A3)
      = (a1 * a2 * a3) • ((1 : Matrix (Fin 2) (Fin 2) ℝ) ⊗ₖ 1 ⊗ₖ 1)
        + (a2 * a3 * t1) • (A1 ⊗ₖ 1 ⊗ₖ 1)
        + (a1 * a3 * t2) • (1 ⊗ₖ A2 ⊗ₖ 1)
        + (a1 * a2 * t3) • (1 ⊗ₖ 1 ⊗ₖ A3)
        + (a3 * t1 * t2) • (A1 ⊗ₖ A2 ⊗ₖ 1)
        + (a2 * t1 * t3) • (A1 ⊗ₖ 1 ⊗ₖ A3)
        + (a1 * t2 * t3) • (1 ⊗ₖ A2 ⊗ₖ A3)
        + (t1 * t2 * t3) • (A1 ⊗ₖ A2 ⊗ₖ A3) := by
  simp only [add_kronecker, kronecker_add, smul_kronecker, kronecker_smul]
  ext i j
  simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, Matrix.kroneckerMap_apply]
  ring

/-- The basis index type `(Fin 2 × Fin 2) × Fin 2` for three binary factors. -/
abbrev G3 : Type := (Fin 2 × Fin 2) × Fin 2

/-- The real span of three-factor Kronecker matrices with at least one identity factor. -/
def twoLocalSpan : Submodule ℝ (Matrix G3 G3 ℝ) :=
  Submodule.span ℝ
    {M : Matrix G3 G3 ℝ |
      (∃ A B : Matrix (Fin 2) (Fin 2) ℝ, M = A ⊗ₖ B ⊗ₖ 1) ∨
      (∃ A C : Matrix (Fin 2) (Fin 2) ℝ, M = A ⊗ₖ 1 ⊗ₖ C) ∨
      (∃ B C : Matrix (Fin 2) (Fin 2) ℝ, M = 1 ⊗ₖ B ⊗ₖ C)}

/-- For nonzero `n`, subtracting `c • (A1 ⊗ₖ A2 ⊗ₖ A3)` from the specified product of shifted
factors leaves an element of `twoLocalSpan` [KempeKitaevRegev2006]. -/
theorem gadget_product_sub_mem_twoLocal {n : ℝ} (hn : n ≠ 0) (c : ℝ)
    (A1 A2 A3 : Matrix (Fin 2) (Fin 2) ℝ) :
    (((2 / n ^ 3) • (1 : Matrix (Fin 2) (Fin 2) ℝ) + (n ^ 6 * c) • A1) ⊗ₖ
        ((2 / n ^ 3) • (1 : Matrix (Fin 2) (Fin 2) ℝ) + (n ^ 3)⁻¹ • A2) ⊗ₖ
        ((2 / n ^ 3) • (1 : Matrix (Fin 2) (Fin 2) ℝ) + (n ^ 3)⁻¹ • A3)
      - c • (A1 ⊗ₖ A2 ⊗ₖ A3)) ∈ twoLocalSpan := by
  have hexp := kron_expand (2 / n ^ 3) (2 / n ^ 3) (2 / n ^ 3)
    (n ^ 6 * c) ((n ^ 3)⁻¹) ((n ^ 3)⁻¹) A1 A2 A3
  rw [hexp]
  have ht : (n ^ 6 * c) * (n ^ 3)⁻¹ * (n ^ 3)⁻¹ = c := by
    field_simp
  rw [ht]
  rw [add_sub_cancel_right]
  clear hexp ht
  have hm1 : (2 / n ^ 3 * (2 / n ^ 3) * (2 / n ^ 3)) •
      ((1 : Matrix (Fin 2) (Fin 2) ℝ) ⊗ₖ 1 ⊗ₖ 1) ∈ twoLocalSpan :=
    Submodule.smul_mem _ _ (Submodule.subset_span (Or.inl ⟨1, 1, rfl⟩))
  have hm2 : ((2 / n ^ 3) * (2 / n ^ 3) * (n ^ 6 * c)) •
      (A1 ⊗ₖ 1 ⊗ₖ 1) ∈ twoLocalSpan :=
    Submodule.smul_mem _ _ (Submodule.subset_span (Or.inl ⟨A1, 1, rfl⟩))
  have hm3 : ((2 / n ^ 3) * (2 / n ^ 3) * (n ^ 3)⁻¹) •
      (1 ⊗ₖ A2 ⊗ₖ 1) ∈ twoLocalSpan :=
    Submodule.smul_mem _ _ (Submodule.subset_span (Or.inl ⟨1, A2, rfl⟩))
  have hm4 : ((2 / n ^ 3) * (2 / n ^ 3) * (n ^ 3)⁻¹) •
      (1 ⊗ₖ 1 ⊗ₖ A3) ∈ twoLocalSpan :=
    Submodule.smul_mem _ _ (Submodule.subset_span (Or.inr (Or.inl ⟨1, A3, rfl⟩)))
  have hm5 : ((2 / n ^ 3) * (n ^ 6 * c) * (n ^ 3)⁻¹) •
      (A1 ⊗ₖ A2 ⊗ₖ 1) ∈ twoLocalSpan :=
    Submodule.smul_mem _ _ (Submodule.subset_span (Or.inl ⟨A1, A2, rfl⟩))
  have hm6 : ((2 / n ^ 3) * (n ^ 6 * c) * (n ^ 3)⁻¹) •
      (A1 ⊗ₖ 1 ⊗ₖ A3) ∈ twoLocalSpan :=
    Submodule.smul_mem _ _ (Submodule.subset_span (Or.inr (Or.inl ⟨A1, A3, rfl⟩)))
  have hm7 : ((2 / n ^ 3) * (n ^ 3)⁻¹ * (n ^ 3)⁻¹) •
      (1 ⊗ₖ A2 ⊗ₖ A3) ∈ twoLocalSpan :=
    Submodule.smul_mem _ _ (Submodule.subset_span (Or.inr (Or.inr ⟨A2, A3, rfl⟩)))
  exact Submodule.add_mem _
    (Submodule.add_mem _
      (Submodule.add_mem _
        (Submodule.add_mem _
          (Submodule.add_mem _ (Submodule.add_mem _ hm1 hm2) hm3) hm4) hm5) hm6) hm7

end Qatlib.Papers.LocalHam06.MainResults.GadgetAlgebra
