/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Matrix.Mul
import Mathlib.LinearAlgebra.Matrix.Hermitian
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic

/-!
# Rescaling to signed unit matrix entries

This module proves the matrix-power scaling identities used in restricting matrix entries to
zero and signed one. It shows that real scaling preserves Hermiticity, transports a
diagonal-entry gap under scaling by `sqrt 2`, and converts entries in `{0, ±1 / sqrt 2}` to `{0,
±1}`.

These constructions accompany the results of [JanzingWocjan2006a].

## Main statements

* `smul_pow_diagonal`: computes diagonal entries of powers after scalar multiplication.
* `entry_restriction_promise_transfer`: transports a positive strict diagonal-entry gap.
* `rescaled_entry_mem`: verifies the rescaled entry values.

## References

* [Janzing and Wocjan, 2006][JanzingWocjan2006a]
-/

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.DiagPowerBQP06.MainResults.EntryRestriction

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- The `m`th power of a real scalar multiple of a matrix equals the original power multiplied
by the `m`th power of the scalar. See [JanzingWocjan2006a]. -/
theorem smul_pow_matrix (A : Matrix n n ℝ) (c : ℝ) (m : ℕ) :
    (c • A) ^ m = c ^ m • A ^ m := by
  induction m with
  | zero => simp
  | succ k ih =>
      calc (c • A) ^ (k + 1) = (c • A) ^ k * (c • A) := pow_succ _ _
        _ = (c ^ k • A ^ k) * (c • A) := by rw [ih]
        _ = c ^ k • (A ^ k * (c • A)) := by rw [Matrix.smul_mul]
        _ = c ^ k • (c • (A ^ k * A)) := by rw [Matrix.mul_smul]
        _ = (c ^ k * c) • (A ^ k * A) := by rw [smul_smul]
        _ = c ^ (k + 1) • A ^ (k + 1) := by rw [pow_succ, pow_succ]

/-- A diagonal entry of the `m`th power scales by `c ^ m` when the matrix is multiplied by `c`.
See [JanzingWocjan2006a]. -/
theorem smul_pow_diagonal (A : Matrix n n ℝ) (c : ℝ) (m : ℕ) (j : n) :
    ((c • A) ^ m) j j = c ^ m * (A ^ m) j j := by
  rw [smul_pow_matrix, Matrix.smul_apply, smul_eq_mul]

/-- Real scalar multiplication preserves Hermiticity of a real matrix. See [JanzingWocjan2006a]. -/
theorem isHermitian_smul_real (A : Matrix n n ℝ) (hA : A.IsHermitian) (c : ℝ) :
    (c • A).IsHermitian := by
  refine Matrix.IsHermitian.ext (fun i j => ?_)
  show star ((c • A) j i) = (c • A) i j
  rw [star_trivial, Matrix.smul_apply, Matrix.smul_apply, smul_eq_mul, smul_eq_mul]
  rw [show A j i = A i j from by simpa using hA.apply i j]

/-- Scaling a matrix by `sqrt 2` transports a strict positive lower bound `δ` on a diagonal
power entry to the bound `δ * (sqrt 2) ^ m`. See [JanzingWocjan2006a]. -/
theorem entry_restriction_promise_transfer {A : Matrix n n ℝ} {m : ℕ} {j : n}
    {δ : ℝ} (hδ : 0 < δ) (h : δ < (A ^ m) j j) :
    δ * (Real.sqrt 2) ^ m < ((Real.sqrt 2 • A) ^ m) j j := by
  rw [smul_pow_diagonal]
  have hs : 0 < (Real.sqrt 2) ^ m := pow_pos (by positivity) m
  have hmul := mul_lt_mul_of_pos_left h hs
  simpa [mul_comm] using hmul

/-- Multiplication by `sqrt 2` sends zero and signed reciprocal-square-root-two entries to zero
and signed one entries. See [JanzingWocjan2006a]. -/
theorem rescaled_entry_mem (x : ℝ)
    (hx : x = 0 ∨ x = 1 / Real.sqrt 2 ∨ x = -(1 / Real.sqrt 2)) :
    Real.sqrt 2 * x = 0 ∨ Real.sqrt 2 * x = 1 ∨ Real.sqrt 2 * x = -1 := by
  have hs : Real.sqrt 2 ≠ 0 := by positivity
  rcases hx with h | h | h
  · left
    rw [h]
    ring
  · right; left
    rw [h, mul_one_div, div_self hs]
  · right; right
    rw [h, mul_neg, mul_one_div, div_self hs]

end Qatlib.Papers.DiagPowerBQP06.MainResults.EntryRestriction
