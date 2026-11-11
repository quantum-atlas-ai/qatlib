/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Data.Complex.Basic
import Mathlib.Analysis.Complex.Basic
import Mathlib.Algebra.BigOperators.Field
import Mathlib.LinearAlgebra.Matrix.Hermitian
import Mathlib.Tactic.Ring
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.IntervalCases

/-!
# Algebra for Hermitian sampling and cubic filters

This module gives algebraic identities expressing Hermitian samples through a matrix `L + I • H`
and its conjugate transpose. It also proves cubic root-of-unity filters for coefficients and
finite polynomials, together with the coefficient weight `sqrt (1 + s ^ 2)` appearing in the
original-oracle representation of [WangEtAl2026].

## Main statements

* `hermitian_sample_from_original`: reconstructs `L + s • H` from a matrix and its adjoint.
* `cubic_root_polynomial_projection`: averaging three rotated polynomial values keeps exponents
  divisible by three.
* `original_oracle_coefficient_weight`: computes the sum of the two coefficient norms.

## References

* [Wang et al., 2026][WangEtAl2026]
-/

namespace Qatlib.Foundations.CbmdAnalysis.Core

set_option autoImplicit false

namespace CBMD
open Complex Matrix

/-- For Hermitian `L` and `H` and real `s`, the specified linear combination of `L + I • H` and
its conjugate transpose equals `L + s • H`. -/
theorem hermitian_sample_from_original {n : Type*} (L H : Matrix n n ℂ)
    (hL : L.IsHermitian) (hH : H.IsHermitian) (s : ℝ) :
    (((1 - I * (s : ℂ)) / 2) : ℂ) • (L + I • H) +
      (((1 + I * (s : ℂ)) / 2) : ℂ) • (L + I • H)ᴴ =
      L + (s : ℂ) • H := by
  rw [Matrix.conjTranspose_add, Matrix.conjTranspose_smul, hL.eq, hH.eq]
  ext i j
  simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, star_def, conj_I]
  ring_nf
  simp [I_sq]

/-- For Hermitian `L` and `H` and real `s`, the specified linear combination of `L + I • H` and
its conjugate transpose equals `H + s • L`. -/
theorem first_order_sample_from_original {n : Type*} (L H : Matrix n n ℂ)
    (hL : L.IsHermitian) (hH : H.IsHermitian) (s : ℝ) :
    ((((s : ℂ) - I) / 2) : ℂ) • (L + I • H) +
      ((((s : ℂ) + I) / 2) : ℂ) • (L + I • H)ᴴ =
      H + (s : ℂ) • L := by
  rw [Matrix.conjTranspose_add, Matrix.conjTranspose_smul, hL.eq, hH.eq]
  ext i j
  simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, star_def, conj_I]
  ring_nf
  simp [I_sq]

/-- A complex root of `ω ^ 2 + ω + 1 = 0` has cube one. -/
theorem cubic_root_cube (ω : ℂ) (hω : ω ^ 2 + ω + 1 = 0) : ω ^ 3 = 1 := by
  linear_combination (ω - 1) * hω

/-- For `ω ^ 2 + ω + 1 = 0`, the sum `1 + ω ^ n + ω ^ (2 * n)` is three when `n` is divisible by
three and zero otherwise. -/
theorem cubic_root_filter (ω : ℂ) (hω : ω ^ 2 + ω + 1 = 0) (n : ℕ) :
    1 + ω ^ n + ω ^ (2 * n) = if n % 3 = 0 then 3 else 0 := by
  have hcube := cubic_root_cube ω hω
  have hp (k : ℕ) : ω ^ k = ω ^ (k % 3) := by
    calc
      ω ^ k = ω ^ (k % 3 + 3 * (k / 3)) := by rw [Nat.mod_add_div]
      _ = ω ^ (k % 3) := by rw [pow_add, pow_mul, hcube]; simp
  rw [hp n, hp (2 * n)]
  have hn := Nat.mod_lt n (by decide : 0 < 3)
  have hmod : (2 * n) % 3 = (2 * (n % 3)) % 3 := by omega
  rw [hmod]
  interval_cases h : n % 3
  · norm_num
  · norm_num
    linear_combination hω
  · norm_num
    linear_combination hω

/-- Averaging a coefficient multiplied by the three cubic phases keeps it exactly when its
exponent is divisible by three. -/
theorem cubic_root_coefficient_projection (ω c : ℂ)
    (hω : ω ^ 2 + ω + 1 = 0) (n : ℕ) :
    (c + c * ω ^ n + c * ω ^ (2 * n)) / 3 =
      if n % 3 = 0 then c else 0 := by
  have hf := cubic_root_filter ω hω n
  by_cases h : n % 3 = 0
  · simp only [h, if_true] at hf ⊢
    linear_combination c / 3 * hf
  · simp only [h, if_false] at hf ⊢
    linear_combination c / 3 * hf

/-- Averaging a finite polynomial at `z`, `ω * z`, and `ω ^ 2 * z` retains precisely the terms
whose exponents are divisible by three. -/
theorem cubic_root_polynomial_projection (ω z : ℂ) (a : ℕ → ℂ)
    (hω : ω ^ 2 + ω + 1 = 0) (N : ℕ) :
    ((∑ k ∈ Finset.range N, a k * z ^ k) +
      (∑ k ∈ Finset.range N, a k * (ω * z) ^ k) +
      (∑ k ∈ Finset.range N, a k * (ω ^ 2 * z) ^ k)) / 3 =
      ∑ k ∈ Finset.range N, if k % 3 = 0 then a k * z ^ k else 0 := by
  rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib, Finset.sum_div]
  apply Finset.sum_congr rfl
  intro k hk
  convert cubic_root_coefficient_projection ω (a k * z ^ k) hω k using 1
  simp only [mul_pow, pow_mul]
  ring

/-- For real `s`, the norms of `(1 - I * s) / 2` and `(1 + I * s) / 2` sum to `sqrt (1 + s ^
2)`. -/
theorem original_oracle_coefficient_weight (s : ℝ) :
    ‖((1 - I * (s : ℂ)) / 2 : ℂ)‖ +
      ‖((1 + I * (s : ℂ)) / 2 : ℂ)‖ = Real.sqrt (1 + s ^ 2) := by
  have hm : ‖(1 - I * (s : ℂ) : ℂ)‖ = Real.sqrt (1 + s ^ 2) := by
    rw [Complex.norm_def]
    congr 1
    simp [Complex.normSq_apply, pow_two]
  have hp : ‖(1 + I * (s : ℂ) : ℂ)‖ = Real.sqrt (1 + s ^ 2) := by
    rw [Complex.norm_def]
    congr 1
    simp [Complex.normSq_apply, pow_two]
  rw [norm_div, norm_div, hm, hp]
  norm_num

end CBMD

end Qatlib.Foundations.CbmdAnalysis.Core
