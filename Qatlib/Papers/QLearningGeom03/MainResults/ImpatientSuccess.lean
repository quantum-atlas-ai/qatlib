/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Analysis.Complex.Basic
import Mathlib.Data.Matrix.Mul
import Qatlib.Papers.QLearningGeom03.MainResults.ImpatientCritical
set_option warningAsError false

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace Qatlib.Papers.QLearningGeom03.MainResults

open Matrix
open scoped Matrix

variable {n : ℕ}

noncomputable def equalSuperposition (n : ℕ) : Fin n → ℂ :=
  fun _ => (((Real.sqrt n : ℝ) : ℂ))⁻¹

theorem queryState_eq_column (A : Matrix (Fin n) (Fin n) ℂ) (c : Fin n) :
    A *ᵥ (Pi.single c 1) = A.col c := by
  rw [Matrix.mulVec_single_one]

theorem impatient_success_amplitude (A S : Matrix (Fin n) (Fin n) ℂ) (c : Fin n) :
    (S *ᵥ (A *ᵥ (Pi.single c 1))) c = (S * A) c c := by
  rw [Matrix.mulVec_mulVec, Matrix.mulVec_single_one]
  rfl

theorem impatient_success_probability (A S : Matrix (Fin n) (Fin n) ℂ) (c : Fin n) :
    Complex.normSq ((S *ᵥ (A *ᵥ (Pi.single c 1))) c) = Complex.normSq ((S * A) c c) := by
  rw [impatient_success_amplitude]

theorem impatient_success_probability_le_one (A S : Matrix (Fin n) (Fin n) ℂ) (c : Fin n)
    (h : Complex.normSq ((S * A) c c) ≤ 1) :
    Complex.normSq ((S *ᵥ (A *ᵥ (Pi.single c 1))) c) ≤ 1 := by
  rw [impatient_success_probability]
  exact h

lemma unitary_row_normSq {U : Matrix (Fin n) (Fin n) ℂ} (hU : U * Uᴴ = 1) (c : Fin n) :
    (∑ x, Complex.normSq (U c x) : ℝ) = 1 := by
  have hentry : (U * Uᴴ) c c = 1 := by rw [hU, Matrix.one_apply_eq]
  have hsum : (U * Uᴴ) c c = ((∑ x, Complex.normSq (U c x) : ℝ) : ℂ) := by
    rw [Matrix.mul_apply, Complex.ofReal_sum]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [Matrix.conjTranspose_apply, Complex.star_def, mul_comm, ← Complex.normSq_eq_conj_mul_self]
  rw [hsum] at hentry
  exact Complex.ofReal_inj.mp hentry

lemma abs_diag_mul_le_column {U A : Matrix (Fin n) (Fin n) ℂ} (hU : U * Uᴴ = 1)
    (c : Fin n) :
    ‖(U * A) c c‖ ≤ Real.sqrt (∑ x, Complex.normSq (A x c)) := by
  have hrow : (∑ x, ‖U c x‖ ^ 2 : ℝ) = 1 := by
    rw [← unitary_row_normSq hU c]
    exact Finset.sum_congr rfl fun x _ => by rw [Complex.normSq_eq_norm_sq]
  have hcol : (∑ x, ‖A x c‖ ^ 2 : ℝ) = ∑ x, Complex.normSq (A x c) :=
    Finset.sum_congr rfl fun x _ => by rw [Complex.normSq_eq_norm_sq]
  have hbound : ‖(U * A) c c‖ ≤ ∑ x, ‖U c x‖ * ‖A x c‖ := by
    rw [Matrix.mul_apply]
    calc ‖∑ x, U c x * A x c‖ ≤ ∑ x, ‖U c x * A x c‖ := norm_sum_le _ _
      _ = ∑ x, ‖U c x‖ * ‖A x c‖ := by
          exact Finset.sum_congr rfl fun x _ => by rw [norm_mul]
  have hcs : (∑ x, ‖U c x‖ * ‖A x c‖ : ℝ)
      ≤ Real.sqrt (∑ x, ‖U c x‖ ^ 2) * Real.sqrt (∑ x, ‖A x c‖ ^ 2) := by
    simpa using Real.sum_mul_le_sqrt_mul_sqrt (Finset.univ : Finset (Fin n))
      (fun x => ‖U c x‖) (fun x => ‖A x c‖)
  rw [hrow, hcol, Real.sqrt_one, one_mul] at hcs
  linarith

theorem impatient_amplitude_bound {A S : Matrix (Fin n) (Fin n) ℂ} (hS : S * Sᴴ = 1)
    (c : Fin n) :
    ‖(S * A) c c‖ ≤ Real.sqrt (∑ x, Complex.normSq (A x c)) :=
  abs_diag_mul_le_column hS c

end Qatlib.Papers.QLearningGeom03.MainResults
