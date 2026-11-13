/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Analysis.Complex.Basic
import Mathlib.Data.Matrix.Mul
import Qatlib.Papers.QLearningGeom03.MainResults.ImpatientCritical

/-!
# Success amplitudes for impatient learning

This module identifies the output amplitude of a query column followed by a matrix `S` with the
corresponding diagonal entry of `S * A`. It also bounds that amplitude by the Euclidean norm of
the query column when `S * Sᴴ = 1`.

The identities give the matrix formulation of impatient learning success used in
[HunzikerEtAl2003].

## Main statements

* `impatient_success_amplitude`: Success amplitude as a diagonal matrix entry.
* `impatient_success_probability`: The corresponding squared-norm identity.
* `impatient_amplitude_bound`: A unitary-row bound on the success amplitude.

## References

* [Hunziker et al., 2003][HunzikerEtAl2003]
-/

set_option autoImplicit false

namespace Qatlib.Papers.QLearningGeom03.MainResults

open Matrix
open scoped Matrix

variable {n : ℕ}

/-- The vector on `Fin n` whose entries are all the complex embedding of 1/√n. -/
noncomputable def equalSuperposition (n : ℕ) : Fin n → ℂ :=
  fun _ => (((Real.sqrt n : ℝ) : ℂ))⁻¹

/-- Applying `A` to the standard basis vector at `c` gives column `c` of `A`. -/
theorem queryState_eq_column (A : Matrix (Fin n) (Fin n) ℂ) (c : Fin n) :
    A *ᵥ (Pi.single c 1) = A.col c := by
  rw [Matrix.mulVec_single_one]

/-- The c-th amplitude after applying `A` and then `S` to the c-th basis vector equals `(S * A)
c c`, as used in [Hunziker et al., Theorem 3.4][HunzikerEtAl2003]. -/
theorem impatient_success_amplitude (A S : Matrix (Fin n) (Fin n) ℂ) (c : Fin n) :
    (S *ᵥ (A *ᵥ (Pi.single c 1))) c = (S * A) c c := by
  rw [Matrix.mulVec_mulVec, Matrix.mulVec_single_one]
  rfl

/-- The squared norm of the c-th output amplitude equals the squared norm of `(S * A) c c`,
giving the success expression used in [Hunziker et al., Theorem 3.4][HunzikerEtAl2003]. -/
theorem impatient_success_probability (A S : Matrix (Fin n) (Fin n) ℂ) (c : Fin n) :
    Complex.normSq ((S *ᵥ (A *ᵥ (Pi.single c 1))) c) = Complex.normSq ((S * A) c c) := by
  rw [impatient_success_amplitude]

/-- If the squared norm of `(S * A) c c` is at most 1, then the squared norm of the
corresponding output amplitude is at most 1. -/
theorem impatient_success_probability_le_one (A S : Matrix (Fin n) (Fin n) ℂ) (c : Fin n)
    (h : Complex.normSq ((S * A) c c) ≤ 1) :
    Complex.normSq ((S *ᵥ (A *ᵥ (Pi.single c 1))) c) ≤ 1 := by
  rw [impatient_success_probability]
  exact h

/-- Every row of a complex matrix satisfying `U * Uᴴ = 1` has total squared entry norm 1. -/
lemma unitary_row_normSq {U : Matrix (Fin n) (Fin n) ℂ} (hU : U * Uᴴ = 1) (c : Fin n) :
    (∑ x, Complex.normSq (U c x) : ℝ) = 1 := by
  have hentry : (U * Uᴴ) c c = 1 := by rw [hU, Matrix.one_apply_eq]
  have hsum : (U * Uᴴ) c c = ((∑ x, Complex.normSq (U c x) : ℝ) : ℂ) := by
    rw [Matrix.mul_apply, Complex.ofReal_sum]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [Matrix.conjTranspose_apply, Complex.star_def, mul_comm, ← Complex.normSq_eq_conj_mul_self]
  rw [hsum] at hentry
  exact Complex.ofReal_inj.mp hentry

/-- If `U * Uᴴ = 1`, the norm of `(U * A) c c` is at most the Euclidean norm of column `c` of
`A`. -/
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

/-- A matrix `S` satisfying `S * Sᴴ = 1` bounds the diagonal success amplitude by the Euclidean
norm of the input query column, as used in [HunzikerEtAl2003]. -/
theorem impatient_amplitude_bound {A S : Matrix (Fin n) (Fin n) ℂ} (hS : S * Sᴴ = 1)
    (c : Fin n) :
    ‖(S * A) c c‖ ≤ Real.sqrt (∑ x, Complex.normSq (A x c)) :=
  abs_diag_mul_le_column hS c

end Qatlib.Papers.QLearningGeom03.MainResults
