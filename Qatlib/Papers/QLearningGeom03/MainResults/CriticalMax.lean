/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Analysis.Complex.Basic
import Mathlib.Data.Matrix.Mul
import Mathlib.Analysis.Real.Sqrt
import Mathlib.LinearAlgebra.Matrix.Trace
import Qatlib.Papers.QLearningGeom03.MainResults.ImpatientCritical

/-!
# Optimality under constant diagonal constraints

This module proves Frobenius and trace inequalities for complex matrices and applies them to
`diagNormSq`. If both a positive matrix `Cᴴ * C` and its left unitary transform have constant
diagonals, the transform cannot increase the diagonal squared norm or the squared amplitude of
the common diagonal entry.

These estimates supply the constrained optimality argument for impatient learning in
[HunzikerEtAl2003].

## Main statements

* `abs_trace_conjTranspose_mul_le`: The Hilbert–Schmidt Cauchy–Schwarz inequality.
* `diagNormSq_mul_unitary_le`: Diagonal squared norm does not increase under the stated
  constant-diagonal assumptions.
* `impatient_optimal_amplitude`: The corresponding bound on a diagonal amplitude.

## References

* [Hunziker et al., 2003][HunzikerEtAl2003]
-/

set_option autoImplicit false

namespace Qatlib.Papers.QLearningGeom03.MainResults

open Matrix
open scoped Matrix

variable {n : ℕ}

/-- The squared Frobenius norm, defined as the sum of squared complex norms of all matrix
entries. -/
noncomputable def frobSq (A : Matrix (Fin n) (Fin n) ℂ) : ℝ :=
  ∑ i, ∑ j, Complex.normSq (A i j)

/-- The squared Frobenius norm is the real part of the trace of `Aᴴ * A`. -/
theorem frobSq_eq_trace_re (A : Matrix (Fin n) (Fin n) ℂ) :
    frobSq A = (Matrix.trace (Aᴴ * A)).re := by
  rw [frobSq]
  have h : (Matrix.trace (Aᴴ * A)).re = (∑ i, ∑ j, Complex.normSq (A j i) : ℝ) := by
    have hh := trace_conjTranspose_mul_self A
    calc (Matrix.trace (Aᴴ * A)).re
        = ((↑(∑ i, ∑ j, Complex.normSq (A j i) : ℝ) : ℂ)).re := by rw [hh]
      _ = (∑ i, ∑ j, Complex.normSq (A j i) : ℝ) := Complex.ofReal_re _
  rw [h, normSq_sum_swap]

/-- The squared Frobenius norm is nonnegative. -/
lemma frobSq_nonneg (A : Matrix (Fin n) (Fin n) ℂ) : 0 ≤ frobSq A :=
  Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => Complex.normSq_nonneg _

/-- The trace of `Aᴴ * A` is the complex embedding of the squared Frobenius norm. -/
theorem trace_conjTranspose_mul_self_eq_frobSq (A : Matrix (Fin n) (Fin n) ℂ) :
    Matrix.trace (Aᴴ * A) = ((frobSq A : ℝ) : ℂ) := by
  rw [frobSq, ← normSq_sum_swap]
  exact trace_conjTranspose_mul_self A

/-- The Cauchy–Schwarz bound for the double sum of products of two real arrays. -/
lemma sum_sum_mul_le_sqrt (f g : Fin n → Fin n → ℝ) :
    (∑ i, ∑ j, f i j * g i j)
      ≤ Real.sqrt (∑ i, ∑ j, f i j ^ 2) * Real.sqrt (∑ i, ∑ j, g i j ^ 2) := by
  have h := Real.sum_mul_le_sqrt_mul_sqrt (Finset.univ : Finset (Fin n × Fin n))
    (fun p : Fin n × Fin n => f p.1 p.2) (fun p : Fin n × Fin n => g p.1 p.2)
  simpa [Fintype.sum_prod_type] using h

/-- The norm of the Hilbert–Schmidt pairing is bounded by the product of the Frobenius norms. -/
theorem abs_trace_conjTranspose_mul_le (A B : Matrix (Fin n) (Fin n) ℂ) :
    ‖Matrix.trace (Aᴴ * B)‖ ≤ Real.sqrt (frobSq A) * Real.sqrt (frobSq B) := by
  have htr : Matrix.trace (Aᴴ * B) = ∑ i, ∑ j, star (A j i) * B j i := by
    rw [Matrix.trace]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp [Matrix.diag_apply, Matrix.mul_apply, Matrix.conjTranspose_apply]
  have hbound : ‖∑ i, ∑ j, star (A j i) * B j i‖
      ≤ ∑ i, ∑ j, ‖A j i‖ * ‖B j i‖ := by
    calc ‖∑ i, ∑ j, star (A j i) * B j i‖
        ≤ ∑ i, ‖∑ j, star (A j i) * B j i‖ := norm_sum_le _ _
      _ ≤ ∑ i, ∑ j, ‖star (A j i) * B j i‖ :=
          Finset.sum_le_sum fun i _ => norm_sum_le _ _
      _ = ∑ i, ∑ j, ‖A j i‖ * ‖B j i‖ := by
          refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
          rw [norm_mul, norm_star]
  have hcs : (∑ i, ∑ j, ‖A j i‖ * ‖B j i‖ : ℝ)
      ≤ Real.sqrt (∑ i, ∑ j, ‖A j i‖ ^ 2) * Real.sqrt (∑ i, ∑ j, ‖B j i‖ ^ 2) :=
    sum_sum_mul_le_sqrt (fun i j => ‖A j i‖) (fun i j => ‖B j i‖)
  have hA : (∑ i, ∑ j, ‖A j i‖ ^ 2 : ℝ) = frobSq A := by
    rw [frobSq, Finset.sum_comm]
    exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by
      rw [Complex.normSq_eq_norm_sq]
  have hB : (∑ i, ∑ j, ‖B j i‖ ^ 2 : ℝ) = frobSq B := by
    rw [frobSq, Finset.sum_comm]
    exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by
      rw [Complex.normSq_eq_norm_sq]
  rw [htr]
  exact hbound.trans (by rw [hA, hB] at hcs; exact hcs)

/-- Right multiplication by a matrix satisfying `U * Uᴴ = 1` preserves the squared Frobenius
norm. -/
theorem frobSq_mul_of_unitary {C U : Matrix (Fin n) (Fin n) ℂ} (hU : U * Uᴴ = 1) :
    frobSq (C * U) = frobSq C := by
  have hconj : (C * U)ᴴ * (C * U) = Uᴴ * (Cᴴ * C) * U := by
    rw [Matrix.conjTranspose_mul]
    simp only [Matrix.mul_assoc]
  have htrace : Matrix.trace (Uᴴ * (Cᴴ * C) * U) = Matrix.trace (Cᴴ * C) := by
    calc Matrix.trace (Uᴴ * (Cᴴ * C) * U)
        = Matrix.trace (U * (Uᴴ * (Cᴴ * C))) := Matrix.trace_mul_comm _ _
      _ = Matrix.trace ((U * Uᴴ) * (Cᴴ * C)) := by rw [Matrix.mul_assoc]
      _ = Matrix.trace (Cᴴ * C) := by rw [hU, Matrix.one_mul]
  rw [frobSq_eq_trace_re, hconj, htrace, ← frobSq_eq_trace_re]

/-- For `U * Uᴴ = 1`, the norm of the trace of `U * (Cᴴ * C)` is at most `frobSq C`. -/
theorem abs_trace_mul_unitary_le {C U : Matrix (Fin n) (Fin n) ℂ} (hU : U * Uᴴ = 1) :
    ‖Matrix.trace (U * (Cᴴ * C))‖ ≤ frobSq C := by
  have htrace : Matrix.trace (U * (Cᴴ * C)) = Matrix.trace (Cᴴ * (C * U)) := by
    rw [← Matrix.mul_assoc Cᴴ C U]
    exact (Matrix.trace_mul_comm (Cᴴ * C) U).symm
  rw [htrace]
  have h := abs_trace_conjTranspose_mul_le C (C * U)
  rw [frobSq_mul_of_unitary hU] at h
  have hsq : Real.sqrt (frobSq C) * Real.sqrt (frobSq C) = frobSq C :=
    Real.mul_self_sqrt (frobSq_nonneg C)
  simpa [hsq] using h

/-- For a matrix with constant diagonal, `diagNormSq` is n times the squared norm of its
diagonal entry. -/
lemma diagNormSq_eq_card_mul [NeZero n] {B : Matrix (Fin n) (Fin n) ℂ}
    (h : ∀ i, B i i = B 0 0) :
    diagNormSq B = (n : ℝ) * Complex.normSq (B 0 0) := by
  rw [diagNormSq]
  rw [Finset.sum_congr rfl fun i _ => by rw [h i], Finset.sum_const, Finset.card_univ,
    Fintype.card_fin]
  simp [nsmul_eq_mul]

/-- For a matrix with constant diagonal, the trace is n times its diagonal entry. -/
lemma trace_eq_card_mul [NeZero n] {B : Matrix (Fin n) (Fin n) ℂ}
    (h : ∀ i, B i i = B 0 0) :
    Matrix.trace B = (n : ℂ) * B 0 0 := by
  rw [Matrix.trace]
  simp only [Matrix.diag_apply]
  rw [Finset.sum_congr rfl fun i _ => h i, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin]
  simp [nsmul_eq_mul]

/-- For a matrix with constant diagonal and positive size, `diagNormSq` is the squared norm of
its trace divided by n. -/
theorem diagNormSq_eq_normSq_trace_div [NeZero n] {B : Matrix (Fin n) (Fin n) ℂ}
    (h : ∀ i, B i i = B 0 0) :
    diagNormSq B = Complex.normSq (Matrix.trace B) / (n : ℝ) := by
  have hn : (n : ℝ) ≠ 0 := by
    exact_mod_cast NeZero.ne n
  rw [diagNormSq_eq_card_mul h, trace_eq_card_mul h, Complex.normSq_mul,
    Complex.normSq_natCast]
  field_simp

/-- If `Cᴴ * C` and `U * (Cᴴ * C)` have constant diagonals and `U * Uᴴ = 1`, left multiplication
by `U` cannot increase `diagNormSq`. This is the constrained maximality estimate used in
[HunzikerEtAl2003]. -/
theorem diagNormSq_mul_unitary_le [NeZero n] {C : Matrix (Fin n) (Fin n) ℂ}
    (hdiag : ∀ i, (Cᴴ * C) i i = (Cᴴ * C) 0 0)
    {U : Matrix (Fin n) (Fin n) ℂ} (hU : U * Uᴴ = 1)
    (hdiagU : ∀ i, (U * (Cᴴ * C)) i i = (U * (Cᴴ * C)) 0 0) :
    diagNormSq (U * (Cᴴ * C)) ≤ diagNormSq (Cᴴ * C) := by
  have hnpos : (0 : ℝ) < n := by exact_mod_cast Nat.pos_of_neZero n
  have htraceP : Matrix.trace (Cᴴ * C) = ((frobSq C : ℝ) : ℂ) :=
    trace_conjTranspose_mul_self_eq_frobSq C
  have hupper : ‖Matrix.trace (U * (Cᴴ * C))‖ ≤ frobSq C :=
    abs_trace_mul_unitary_le hU
  have hnormLe : Complex.normSq (Matrix.trace (U * (Cᴴ * C)))
      ≤ Complex.normSq (Matrix.trace (Cᴴ * C)) := by
    rw [Complex.normSq_eq_norm_sq, htraceP, Complex.normSq_ofReal]
    simpa [pow_two] using pow_le_pow_left₀ (norm_nonneg _) hupper 2
  rw [diagNormSq_eq_normSq_trace_div hdiagU, diagNormSq_eq_normSq_trace_div hdiag]
  exact div_le_div_of_nonneg_right hnormLe hnpos.le

/-- Under the stated unitary and constant-diagonal assumptions, the squared norm of the diagonal
entry of `U * (Cᴴ * C)` is at most that of `Cᴴ * C`, as used in [HunzikerEtAl2003]. -/
theorem impatient_optimal_amplitude [NeZero n] {C : Matrix (Fin n) (Fin n) ℂ}
    (hdiag : ∀ i, (Cᴴ * C) i i = (Cᴴ * C) 0 0)
    {U : Matrix (Fin n) (Fin n) ℂ} (hU : U * Uᴴ = 1)
    (hdiagU : ∀ i, (U * (Cᴴ * C)) i i = (U * (Cᴴ * C)) 0 0) :
    Complex.normSq ((U * (Cᴴ * C)) 0 0) ≤ Complex.normSq ((Cᴴ * C) 0 0) := by
  have hmax := diagNormSq_mul_unitary_le hdiag hU hdiagU
  rw [diagNormSq_eq_card_mul hdiagU, diagNormSq_eq_card_mul hdiag] at hmax
  have hn : (0 : ℝ) < n := by exact_mod_cast Nat.pos_of_neZero n
  exact le_of_mul_le_mul_left hmax hn

end Qatlib.Papers.QLearningGeom03.MainResults
