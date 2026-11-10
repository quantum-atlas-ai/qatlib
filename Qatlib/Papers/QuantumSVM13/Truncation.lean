/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Foundations.PureStateMath.MixedState

set_option autoImplicit false
set_option maxHeartbeats 400000

noncomputable section

open scoped BigOperators ComplexOrder

namespace Qatlib.Papers.QuantumSVM13.Truncation

open Matrix
open Qatlib.Foundations.PureStateMath

variable {M : ℕ}

noncomputable def truncationError (lam : Fin M → ℂ) : ℝ :=
  Real.sqrt (∑ i, Complex.normSq (lam i))

noncomputable def inverseSqrt (M : ℕ) : ℝ := 1 / Real.sqrt (M : ℝ)

theorem schattenTwo_diagonal (lam : Fin M → ℂ) :
    SchattenTwo (Matrix.diagonal lam) = truncationError lam := by
  unfold SchattenTwo truncationError
  congr 1
  rw [Matrix.diagonal_conjTranspose, Matrix.diagonal_mul_diagonal, Matrix.trace_diagonal]
  rw [Complex.re_sum]
  apply Finset.sum_congr rfl
  intro i _
  have hconj : star lam i = (starRingEnd ℂ) (lam i) := by
    rw [Pi.star_apply]
    exact congrFun Complex.star_def (lam i)
  rw [hconj, ← Complex.normSq_eq_conj_mul_self, Complex.ofReal_re]

theorem sqrt_inv_eq (hM : 0 < M) : Real.sqrt (1 / (M : ℝ)) = 1 / Real.sqrt (M : ℝ) := by
  have hMpos : (0 : ℝ) < M := by exact_mod_cast hM
  have hnonneg : 0 ≤ 1 / Real.sqrt (M : ℝ) := by positivity
  have hsq : (1 / Real.sqrt (M : ℝ)) ^ 2 = 1 / (M : ℝ) := by
    rw [div_pow, one_pow, Real.sq_sqrt hMpos.le]
  rw [← hsq, Real.sqrt_sq hnonneg]

theorem truncationError_le (hM : 0 < M) (lam : Fin M → ℂ)
    (h : ∀ i, Complex.normSq (lam i) ≤ 1 / (M : ℝ) ^ 2) :
    truncationError lam ≤ inverseSqrt M := by
  have hMpos : (0 : ℝ) < M := by exact_mod_cast hM
  have hsum : (∑ i, Complex.normSq (lam i)) ≤ 1 / (M : ℝ) := by
    calc ∑ i, Complex.normSq (lam i) ≤ ∑ _i : Fin M, 1 / (M : ℝ) ^ 2 :=
          Finset.sum_le_sum fun i _ => h i
      _ = (M : ℝ) * (1 / (M : ℝ) ^ 2) := by simp
      _ = 1 / (M : ℝ) := by field_simp
  unfold truncationError inverseSqrt
  calc Real.sqrt (∑ i, Complex.normSq (lam i)) ≤ Real.sqrt (1 / (M : ℝ)) :=
        Real.sqrt_le_sqrt hsum
    _ = 1 / Real.sqrt (M : ℝ) := sqrt_inv_eq hM

theorem truncationError_uniform (hM : 0 < M) :
    truncationError (fun _ : Fin M => ((1 / (M : ℝ) : ℝ) : ℂ)) = inverseSqrt M := by
  have hMpos : (0 : ℝ) < M := by exact_mod_cast hM
  unfold truncationError inverseSqrt
  have hnorm : ∀ i : Fin M, Complex.normSq ((1 / (M : ℝ) : ℝ) : ℂ) = 1 / (M : ℝ) ^ 2 := by
    intro i
    rw [Complex.normSq_ofReal]
    ring
  have hsum_norm : (∑ i, Complex.normSq ((1 / (M : ℝ) : ℝ) : ℂ))
      = ∑ _i : Fin M, (1 / (M : ℝ) ^ 2) :=
    Finset.sum_congr rfl (fun i _ => hnorm i)
  rw [hsum_norm, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  have hsum : (M : ℝ) * (1 / (M : ℝ) ^ 2) = 1 / (M : ℝ) := by field_simp
  rw [hsum, sqrt_inv_eq hM]

theorem schattenTwo_uniform_truncation (hM : 0 < M) :
    SchattenTwo (Matrix.diagonal (fun _ : Fin M => ((1 / (M : ℝ) : ℝ) : ℂ)))
      = inverseSqrt M := by
  rw [schattenTwo_diagonal, truncationError_uniform hM]

end Qatlib.Papers.QuantumSVM13.Truncation
