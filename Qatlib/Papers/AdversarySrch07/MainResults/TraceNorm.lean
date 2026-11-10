/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.AdversarySrch07.MainResults.Definitions
import Mathlib.LinearAlgebra.Matrix.Hermitian
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.Analysis.Matrix.Spectrum
set_option backward.isDefEq.respectTransparency false
set_option warningAsError false

set_option autoImplicit false
noncomputable section

open scoped Classical BigOperators
open Finset

namespace Qatlib.Papers.AdversarySrch07.MainResults.TraceNorm

def lemmaSixMatrix {n : ℕ} (v w : Fin n → ℝ) : Matrix (Fin n) (Fin n) ℝ :=
  fun i j => if i ≤ j then v i * w j else v j * w i

theorem lemmaSixMatrix_isHermitian {n : ℕ} (v w : Fin n → ℝ) :
    (lemmaSixMatrix v w).IsHermitian := by
  apply Matrix.IsHermitian.ext
  intro i j
  simp only [star_trivial, lemmaSixMatrix]
  by_cases hji : j ≤ i
  · rw [if_pos hji]
    by_cases hij : i ≤ j
    · have hEq : i = j := le_antisymm hij hji
      rw [hEq, if_pos (le_refl j)]
    · rw [if_neg hij]
  · rw [if_neg hji, if_pos (le_of_not_ge hji)]

theorem lemmaSixMatrix_comm {n : ℕ} (v w : Fin n → ℝ) (i j : Fin n) :
    lemmaSixMatrix v w i j = lemmaSixMatrix v w j i := by
  have h := (lemmaSixMatrix_isHermitian v w).apply j i
  simpa using! h

theorem lemmaSixMatrix_self {n : ℕ} (v w : Fin n → ℝ) (i : Fin n) :
    lemmaSixMatrix v w i i = v i * w i := by
  simp [lemmaSixMatrix]

theorem lemmaSixMatrix_nonneg {n : ℕ} (v w : Fin n → ℝ)
    (hv : ∀ i, 0 ≤ v i) (hw : ∀ i, 0 ≤ w i) (i j : Fin n) :
    0 ≤ lemmaSixMatrix v w i j := by
  unfold lemmaSixMatrix
  split_ifs
  · exact mul_nonneg (hv i) (hw j)
  · exact mul_nonneg (hv j) (hw i)

theorem lemmaSixMatrix_le_add {n : ℕ} (v w : Fin n → ℝ)
    (hv : ∀ i, 0 ≤ v i) (hw : ∀ i, 0 ≤ w i) (i j : Fin n) :
    lemmaSixMatrix v w i j ≤ v i * w j + v j * w i := by
  unfold lemmaSixMatrix
  split_ifs
  · have : 0 ≤ v j * w i := mul_nonneg (hv j) (hw i)
    linarith
  · have : 0 ≤ v i * w j := mul_nonneg (hv i) (hw j)
    linarith

theorem lemmaSixMatrix_ge_rankOne {n : ℕ} (v w : Fin n → ℝ) {i j : Fin n} (h : i ≤ j) :
    v i * w j ≤ lemmaSixMatrix v w i j := by
  simp [lemmaSixMatrix, h]

theorem trace_lemmaSix {n : ℕ} (v w : Fin n → ℝ) :
    ∑ i, lemmaSixMatrix v w i i = ∑ i, v i * w i := by
  apply Finset.sum_congr rfl
  intro i _
  exact lemmaSixMatrix_self v w i

noncomputable def l2norm {n : ℕ} (v : Fin n → ℝ) : ℝ := Real.sqrt (∑ i, v i ^ 2)

theorem l2norm_nonneg {n : ℕ} (v : Fin n → ℝ) : 0 ≤ l2norm v := Real.sqrt_nonneg _

noncomputable def symTraceNorm {n : ℕ} (M : Matrix (Fin n) (Fin n) ℝ) (hM : M.IsHermitian) : ℝ :=
  ∑ i, |hM.eigenvalues i|

theorem symTraceNorm_nonneg {n : ℕ} (M : Matrix (Fin n) (Fin n) ℝ) (hM : M.IsHermitian) :
    0 ≤ symTraceNorm M hM :=
  Finset.sum_nonneg (fun _ _ => abs_nonneg _)

theorem posSemidef_trace_eq_symTraceNorm {n : ℕ} (P : Matrix (Fin n) (Fin n) ℝ)
    (hP : P.PosSemidef) : symTraceNorm P hP.1 = P.trace := by
  unfold symTraceNorm
  rw [hP.1.trace_eq_sum_eigenvalues]
  exact Finset.sum_congr rfl (fun i _ => abs_of_nonneg (hP.eigenvalues_nonneg i))

theorem posSemidef_trace_nonneg {n : ℕ} (P : Matrix (Fin n) (Fin n) ℝ) (hP : P.PosSemidef) :
    0 ≤ P.trace := by
  rw [hP.1.trace_eq_sum_eigenvalues]
  exact Finset.sum_nonneg (fun i _ => hP.eigenvalues_nonneg i)

theorem trace_le_symTraceNorm_lemmaSix {n : ℕ} (v w : Fin n → ℝ) :
    ∑ i, v i * w i ≤
      symTraceNorm (lemmaSixMatrix v w) (lemmaSixMatrix_isHermitian v w) := by
  have htr : ∑ i, v i * w i = (lemmaSixMatrix v w).trace := by
    rw [← trace_lemmaSix]
    simp [Matrix.trace]
  rw [htr, symTraceNorm, (lemmaSixMatrix_isHermitian v w).trace_eq_sum_eigenvalues]
  exact Finset.sum_le_sum (fun i _ => le_abs_self _)

end Qatlib.Papers.AdversarySrch07.MainResults.TraceNorm
