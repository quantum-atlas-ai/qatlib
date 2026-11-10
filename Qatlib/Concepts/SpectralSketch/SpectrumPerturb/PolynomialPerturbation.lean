/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.OperatorErrors.Robustness
import Mathlib.Algebra.Polynomial.AlgebraMap
set_option warningAsError false

namespace Qatlib.Concepts.SpectralSketch.SpectrumPerturb

open Matrix Polynomial
open Qatlib
open Qatlib.Concepts.BlockEncoding
open Qatlib.Concepts.BlockEncoding.Encoding
open Qatlib
open Qatlib
open Qatlib
open scoped Matrix.Norms.L2Operator

noncomputable def coefficientLipschitzBound (p : Polynomial ℂ) (M : ℝ) : ℝ :=
  ∑ k ∈ Finset.range (p.natDegree + 1), ‖p.coeff k‖ * (k : ℝ) * M ^ (k - 1)

theorem coefficientLipschitzBound_nonneg (p : Polynomial ℂ) {M : ℝ} (hM : 0 ≤ M) :
    0 ≤ coefficientLipschitzBound p M := by
  apply Finset.sum_nonneg
  intro k _
  exact mul_nonneg (mul_nonneg (norm_nonneg _) (Nat.cast_nonneg _)) (pow_nonneg hM _)

@[simp] theorem coefficientLipschitzBound_C (c : ℂ) (M : ℝ) :
    coefficientLipschitzBound (C c) M = 0 := by
  simp [coefficientLipschitzBound]

@[simp] theorem coefficientLipschitzBound_X (M : ℝ) :
    coefficientLipschitzBound (X : Polynomial ℂ) M = 1 := by
  simp [coefficientLipschitzBound, Finset.sum_range_succ]

section Matrices

variable {N : Type*} [Fintype N] [DecidableEq N]

theorem matrix_norm_pow_le_radius (X : Matrix N N ℂ) {M : ℝ}
    (hM : 0 ≤ M) (hX : ‖X‖ ≤ M) (n : ℕ) : ‖X ^ n‖ ≤ M ^ n := by
  induction n with
  | zero => simpa using (matrix_one_norm_le (I := N))
  | succ n ih =>
    rw [pow_succ, pow_succ]
    exact (norm_mul_le _ _).trans
      (mul_le_mul ih hX (norm_nonneg X) (pow_nonneg hM n))

theorem matrix_norm_pow_sub_pow_le (X Y : Matrix N N ℂ) {M : ℝ}
    (hM : 0 ≤ M) (hX : ‖X‖ ≤ M) (hY : ‖Y‖ ≤ M) (n : ℕ) :
    ‖X ^ n - Y ^ n‖ ≤ ‖X - Y‖ * (n : ℝ) * M ^ (n - 1) := by
  induction n with
  | zero => simp
  | succ n ih =>
    cases n with
    | zero => simp
    | succ k =>
      have he : X ^ (k + 1 + 1) - Y ^ (k + 1 + 1) =
          X ^ (k + 1) * (X - Y) + (X ^ (k + 1) - Y ^ (k + 1)) * Y := by
        simp only [pow_succ]
        noncomm_ring
      rw [he]
      calc
        _ ≤ ‖X ^ (k + 1) * (X - Y)‖ + ‖(X ^ (k + 1) - Y ^ (k + 1)) * Y‖ :=
          norm_add_le _ _
        _ ≤ ‖X ^ (k + 1)‖ * ‖X - Y‖ + ‖X ^ (k + 1) - Y ^ (k + 1)‖ * ‖Y‖ :=
          add_le_add (norm_mul_le _ _) (norm_mul_le _ _)
        _ ≤ M ^ (k + 1) * ‖X - Y‖ +
            (‖X - Y‖ * ((k + 1 : ℕ) : ℝ) * M ^ k) * M := by
          apply add_le_add
          · exact mul_le_mul_of_nonneg_right (matrix_norm_pow_le_radius X hM hX _) (norm_nonneg _)
          · apply mul_le_mul (by simpa using ih) hY (norm_nonneg Y)
            exact mul_nonneg (mul_nonneg (norm_nonneg _) (Nat.cast_nonneg _)) (pow_nonneg hM _)
        _ = _ := by
          simp only [Nat.add_sub_cancel, Nat.cast_add, Nat.cast_one, pow_succ]
          ring

theorem matrix_polynomial_perturbation (p : Polynomial ℂ) (X Y : Matrix N N ℂ)
    {M : ℝ} (hM : 0 ≤ M) (hX : ‖X‖ ≤ M) (hY : ‖Y‖ ≤ M) :
    ‖aeval X p - aeval Y p‖ ≤ ‖X - Y‖ * coefficientLipschitzBound p M := by
  rw [Polynomial.aeval_eq_sum_range, Polynomial.aeval_eq_sum_range,
    ← Finset.sum_sub_distrib]
  simp_rw [← smul_sub]
  calc
    _ ≤ ∑ k ∈ Finset.range (p.natDegree + 1), ‖p.coeff k • (X ^ k - Y ^ k)‖ :=
      norm_sum_le _ _
    _ ≤ ∑ k ∈ Finset.range (p.natDegree + 1),
        ‖p.coeff k‖ * (‖X - Y‖ * (k : ℝ) * M ^ (k - 1)) := by
      apply Finset.sum_le_sum
      intro k _
      rw [norm_smul]
      exact mul_le_mul_of_nonneg_left (matrix_norm_pow_sub_pow_le X Y hM hX hY k)
        (norm_nonneg _)
    _ = _ := by
      rw [coefficientLipschitzBound, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro k _
      ring

end Matrices

end Qatlib.Concepts.SpectralSketch.SpectrumPerturb
