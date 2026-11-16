/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Mathlib.Analysis.Matrix.Order
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Ring

@[expose] public section


/-! # Finite Cauchy kernels are positive semidefinite

The proof uses a rank-one plus compressed-Cauchy decomposition and induction
on the number of labels. Positive parameters may coincide. No inverse
matrix, distinct-parameter condition, infinite sum, or integral is used.
-/

namespace Qatlib.Foundations.SpectralForms.CauchyKernel

open Matrix
open scoped BigOperators MatrixOrder ComplexOrder

noncomputable def fullCauchyMatrix {n : ℕ} (a : Fin n → ℝ) :
    Matrix (Fin n) (Fin n) ℂ := fun i j => ((1 / (a i + a j) : ℝ) : ℂ)

/-- Full Cauchy scalar step for the stated finite source data. -/
theorem fullCauchy_scalar_step (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    1 / (a + b) =
      2 * c * (1 / (a + c)) * (1 / (b + c)) +
        ((a - c) / (a + c)) * ((b - c) / (b + c)) * (1 / (a + b)) := by
  have hab : a + b ≠ 0 := ne_of_gt (add_pos ha hb)
  have hac : a + c ≠ 0 := ne_of_gt (add_pos ha hc)
  have hbc : b + c ≠ 0 := ne_of_gt (add_pos hb hc)
  field_simp [hab, hac, hbc]
  ring

/-- The first label is removed and all remaining columns are scaled.
The first column is zero, including when other parameters equal the first. -/
noncomputable def fullCauchyCompression {n : ℕ} (a : Fin (n + 1) → ℝ) :
    Matrix (Fin n) (Fin (n + 1)) ℂ := fun k i =>
  if i = k.succ then (((a i - a 0) / (a i + a 0) : ℝ) : ℂ) else 0

/-- Full Cauchy remainder entry for the stated finite source data. -/
theorem fullCauchy_remainder_entry {n : ℕ} (a : Fin (n + 1) → ℝ)
    (i j : Fin (n + 1)) :
    ((fullCauchyCompression a)ᴴ * fullCauchyMatrix (fun k => a k.succ) *
      fullCauchyCompression a) i j =
      ((((a i - a 0) / (a i + a 0)) * ((a j - a 0) / (a j + a 0)) *
        (1 / (a i + a j)) : ℝ) : ℂ) := by
  classical
  have hstar (c : Prop) [Decidable c] (z : ℂ) :
      (starRingEnd ℂ) (if c then z else 0) = if c then (starRingEnd ℂ) z else 0 := by
    split_ifs <;> simp
  refine Fin.cases ?_ (fun i => ?_) i <;>
    refine Fin.cases ?_ (fun j => ?_) j <;>
    simp [fullCauchyCompression, fullCauchyMatrix, Matrix.mul_apply,
      Matrix.conjTranspose_apply, hstar, mul_ite, ite_mul]
  ring

/-- Exact finite decomposition with a positive rank-one first summand. -/
theorem fullCauchyMatrix_decomposition {n : ℕ} (a : Fin (n + 1) → ℝ)
    (ha : ∀ i, 0 < a i) :
    fullCauchyMatrix a =
      ((2 * a 0 : ℝ) : ℂ) • Matrix.vecMulVec
        (fun i => ((1 / (a i + a 0) : ℝ) : ℂ))
        (star (fun i => ((1 / (a i + a 0) : ℝ) : ℂ))) +
      (fullCauchyCompression a)ᴴ * fullCauchyMatrix (fun k => a k.succ) *
        fullCauchyCompression a := by
  ext i j
  simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul,
    Matrix.vecMulVec, Matrix.of_apply, Pi.star_apply, Complex.star_def, Complex.conj_ofReal,
    fullCauchy_remainder_entry, fullCauchyMatrix]
  have h := congrArg (fun r : ℝ => (r : ℂ))
    (fullCauchy_scalar_step (a i) (a j) (a 0) (ha i) (ha j) (ha 0))
  push_cast at h ⊢
  simpa only [mul_assoc] using h

/-- Cauchy positivity on all complex coefficient vectors; repeated
positive parameters are retained as distinct labels. -/
theorem fullCauchyMatrix_posSemidef (n : ℕ) (a : Fin n → ℝ) (ha : ∀ i, 0 < a i) :
    (fullCauchyMatrix a).PosSemidef := by
  induction n with
  | zero =>
      have hz : fullCauchyMatrix a = 0 := by
        ext i j
        exact Fin.elim0 i
      rw [hz]
      exact Matrix.PosSemidef.zero
  | succ n ih =>
      rw [fullCauchyMatrix_decomposition a ha]
      have hfirst : (0 : ℂ) ≤ ((2 * a 0 : ℝ) : ℂ) :=
        Complex.zero_le_real.mpr (mul_nonneg (by norm_num) (ha 0).le)
      exact ((Matrix.posSemidef_vecMulVec_self_star _).smul hfirst).add
        ((ih (fun k => a k.succ) (fun k => ha k.succ)).conjTranspose_mul_mul_same
          (fullCauchyCompression a))

/-- The same positive Cauchy kernel on an arbitrary finite label type. -/
theorem fullCauchyKernel_posSemidef {κ : Type*} [Fintype κ]
    (a : κ → ℝ) (ha : ∀ i, 0 < a i) :
    Matrix.PosSemidef (fun i j => ((1 / (a i + a j) : ℝ) : ℂ) : Matrix κ κ ℂ) := by
  classical
  let e := Fintype.equivFin κ
  have hp := fullCauchyMatrix_posSemidef (Fintype.card κ)
    (fun i => a (e.symm i)) (fun i => ha (e.symm i))
  have hmat : (fun i j => ((1 / (a i + a j) : ℝ) : ℂ) : Matrix κ κ ℂ) =
      (fullCauchyMatrix (fun i => a (e.symm i))).submatrix e e := by
    ext i j
    simp [fullCauchyMatrix]
  rw [hmat]
  exact hp.submatrix e

end Qatlib.Foundations.SpectralForms.CauchyKernel
