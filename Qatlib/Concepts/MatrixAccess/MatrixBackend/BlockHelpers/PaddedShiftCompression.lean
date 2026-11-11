/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Complex.Basic
import Mathlib.LinearAlgebra.UnitaryGroup
import Mathlib.Data.Nat.ModEq
import Mathlib.Tactic

/-!
# Compression of padded cyclic shifts

This module defines the truncated shifts `truncatedStep`, cyclic shifts `cyclicStep`, and the
coordinate inclusion `prefixFrame`. With sufficient padding, compressing powers or finite
polynomials of a cyclic shift gives the corresponding expression in the truncated shift.

The isometric compression and unitary representation provide a finite matrix instance of the
operator-theoretic setting in [Paulsen2002].

## Main statements

* `prefix_cyclic_polynomial`: proves polynomial compression when n + d ≤ N.
* `cyclic_polynomial_representation`: packages unitarity, isometry, and polynomial compression.

## References

* [Paulsen, 2002][Paulsen2002]
-/

set_option autoImplicit false
noncomputable section
open scoped Matrix
namespace Qatlib.Concepts.MatrixAccess.MatrixBackend.PaddedShiftCompression

/-- The k-step forward shift on n coordinates, with entries outside the coordinate range
discarded. -/
def truncatedStep (n k : ℕ) : Matrix (Fin n) (Fin n) ℂ :=
  fun i j => if i.val = j.val + k then 1 else 0

/-- The k-step cyclic shift on N coordinates, with indices reduced modulo N. -/
def cyclicStep (N k : ℕ) : Matrix (Fin N) (Fin N) ℂ :=
  fun i j => if i.val = (j.val + k) % N then 1 else 0

/-- The zero-step truncated shift is the identity matrix. -/
theorem truncatedStep_zero (n : ℕ) : truncatedStep n 0 = 1 := by
  ext i j
  simp [truncatedStep, Matrix.one_apply, Fin.ext_iff]

/-- Multiplication of truncated shifts adds their step sizes. -/
theorem truncatedStep_mul (n a b : ℕ) :
    truncatedStep n a * truncatedStep n b = truncatedStep n (a + b) := by
  ext i j
  rw [Matrix.mul_apply]
  by_cases h : j.val + b < n
  · let mid : Fin n := ⟨j.val + b, h⟩
    rw [Finset.sum_eq_single mid]
    · simp [truncatedStep, mid, Nat.add_left_comm, Nat.add_comm]
    · intro z _hz hne
      have hval : z.val ≠ j.val + b := by
        intro hz
        apply hne
        exact Fin.ext hz
      simp [truncatedStep, hval]
    · simp
  · have hout : i.val ≠ j.val + (a + b) := by omega
    rw [show truncatedStep n (a + b) i j = 0 by simp [truncatedStep, hout]]
    apply Finset.sum_eq_zero
    intro z _hz
    have hval : z.val ≠ j.val + b := by omega
    simp [truncatedStep, hval]

/-- The zero-step cyclic shift is the identity matrix. -/
theorem cyclicStep_zero (N : ℕ) : cyclicStep N 0 = 1 := by
  ext i j
  simp [cyclicStep, Nat.mod_eq_of_lt j.isLt, Matrix.one_apply, Fin.ext_iff]

/-- Multiplication of cyclic shifts adds their step sizes. -/
theorem cyclicStep_mul (N a b : ℕ) :
    cyclicStep N a * cyclicStep N b = cyclicStep N (a + b) := by
  ext i j
  have hN : 0 < N := by have := j.isLt; omega
  let mid : Fin N := ⟨(j.val + b) % N, Nat.mod_lt _ hN⟩
  rw [Matrix.mul_apply, Finset.sum_eq_single mid]
  · have hmod : ((j.val + b) % N + a) % N = (j.val + (a + b)) % N := by
      simp [Nat.add_mod, Nat.add_left_comm, Nat.add_comm]
    simp [cyclicStep, mid, hmod]
  · intro z _hz hne
    have hval : z.val ≠ (j.val + b) % N := by
      intro hz
      apply hne
      exact Fin.ext hz
    simp [cyclicStep, hval]
  · simp

/-- The kth power of the one-step truncated shift is the k-step truncated shift. -/
theorem truncatedStep_pow (n k : ℕ) :
    (truncatedStep n 1) ^ k = truncatedStep n k := by
  induction k with
  | zero => simp [truncatedStep_zero]
  | succ k hk => rw [pow_succ, hk, truncatedStep_mul]

/-- The kth power of the one-step cyclic shift is the k-step cyclic shift. -/
theorem cyclicStep_pow (N k : ℕ) :
    (cyclicStep N 1) ^ k = cyclicStep N k := by
  induction k with
  | zero => simp [cyclicStep_zero]
  | succ k hk => rw [pow_succ, hk, cyclicStep_mul]

/-- Includes `Fin n` into the first n coordinates of `Fin N` using n ≤ N. -/
def prefixIndex {n N : ℕ} (hn : n ≤ N) (j : Fin n) : Fin N :=
  ⟨j.val, lt_of_lt_of_le j.isLt hn⟩

/-- The coordinate inclusion matrix from n coordinates into the first n of N coordinates. -/
def prefixFrame {n N : ℕ} (hn : n ≤ N) : Matrix (Fin N) (Fin n) ℂ :=
  fun i j => if i = prefixIndex hn j then 1 else 0

/-- Compression by `prefixFrame` extracts the submatrix on the first n coordinates. -/
theorem prefixFrame_compress {n N : ℕ} (hn : n ≤ N)
    (B : Matrix (Fin N) (Fin N) ℂ) :
    (prefixFrame hn)ᴴ * B * prefixFrame hn =
      B.submatrix (prefixIndex hn) (prefixIndex hn) := by
  ext i j
  simp [Matrix.mul_apply, prefixFrame, Matrix.conjTranspose_apply]

/-- The prefix inclusion matrix is an isometry. -/
theorem prefixFrame_isometry {n N : ℕ} (hn : n ≤ N) :
    (prefixFrame hn)ᴴ * prefixFrame hn = 1 := by
  have hinj : Function.Injective (prefixIndex hn) := by
    intro i j hij
    exact Fin.ext (congrArg (fun x : Fin N => x.val) hij)
  ext i j
  simp [Matrix.mul_apply, prefixFrame, Matrix.conjTranspose_apply,
    Matrix.one_apply, hinj.eq_iff, eq_comm]

/-- If n + k ≤ N, compressing the kth power of the N-dimensional cyclic shift yields the kth
power of the n-dimensional truncated shift. -/
theorem prefix_cyclic_pow {n N : ℕ} (hn : n ≤ N) (k : ℕ)
    (hpadding : n + k ≤ N) :
    (prefixFrame hn)ᴴ * (cyclicStep N 1) ^ k * prefixFrame hn =
      (truncatedStep n 1) ^ k := by
  rw [cyclicStep_pow, truncatedStep_pow, prefixFrame_compress]
  ext i j
  have hj : j.val + k < N := by omega
  simp [Matrix.submatrix_apply, cyclicStep, truncatedStep, prefixIndex,
    Nat.mod_eq_of_lt hj]

end Qatlib.Concepts.MatrixAccess.MatrixBackend.PaddedShiftCompression

namespace Qatlib.Concepts.MatrixAccess.MatrixBackend.PaddedShiftCompression
open scoped BigOperators

/-- Evaluates the finite matrix polynomial with coefficients indexed from zero through d. -/
def finitePolynomial {n : ℕ} (d : ℕ) (coeff : ℕ → ℂ)
    (A : Matrix (Fin n) (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ :=
  ∑ k ∈ Finset.range (d + 1), coeff k • A ^ k

/-- If n + d ≤ N, compression of a degree-at-most-d polynomial in the cyclic shift equals the
same polynomial in the truncated shift. -/
theorem prefix_cyclic_polynomial {n N : ℕ} (hn : n ≤ N) (d : ℕ)
    (hpadding : n + d ≤ N) (coeff : ℕ → ℂ) :
    (prefixFrame hn)ᴴ * finitePolynomial d coeff (cyclicStep N 1) * prefixFrame hn =
      finitePolynomial d coeff (truncatedStep n 1) := by
  simp only [finitePolynomial, Matrix.mul_sum, Matrix.sum_mul, Matrix.mul_smul,
    Matrix.smul_mul]
  apply Finset.sum_congr rfl
  intro k hk
  have hkd : k ≤ d := by
    have := Finset.mem_range.mp hk
    omega
  rw [prefix_cyclic_pow hn k (by omega)]

end Qatlib.Concepts.MatrixAccess.MatrixBackend.PaddedShiftCompression

namespace Qatlib.Concepts.MatrixAccess.MatrixBackend.PaddedShiftCompression

/-- The one-step cyclic shift is unitary in every finite dimension. -/
theorem cyclicStep_unitary (N : ℕ) :
    cyclicStep N 1 ∈ Matrix.unitaryGroup (Fin N) ℂ := by
  rw [Matrix.mem_unitaryGroup_iff']
  change (cyclicStep N 1)ᴴ * cyclicStep N 1 = 1
  by_cases hN : N = 0
  · subst N
    ext i j
    exact Fin.elim0 i
  · have hNpos : 0 < N := Nat.pos_of_ne_zero hN
    let f : Fin N → Fin N := fun j => ⟨(j.val + 1) % N, Nat.mod_lt _ hNpos⟩
    have hf : Function.Injective f := by
      intro i j hij
      have heq : (i.val + 1) % N = (j.val + 1) % N := congrArg Fin.val hij
      have hmod : Nat.ModEq N i.val j.val :=
        Nat.ModEq.add_right_cancel' 1 heq
      apply Fin.ext
      simpa only [Nat.ModEq, Nat.mod_eq_of_lt i.isLt, Nat.mod_eq_of_lt j.isLt] using hmod
    have hstep (i j : Fin N) :
        cyclicStep N 1 i j = if i = f j then 1 else 0 := by
      simp [cyclicStep, f, Fin.ext_iff]
    ext i j
    simp [Matrix.mul_apply, Matrix.conjTranspose_apply, hstep, hf.eq_iff,
      Matrix.one_apply, eq_comm]

/-- A truncated shift is zero when its step size is at least the dimension. -/
theorem truncatedStep_eq_zero_of_le (n k : ℕ) (hnk : n ≤ k) :
    truncatedStep n k = 0 := by
  ext i j
  have hne : i.val ≠ j.val + k := by omega
  simp [truncatedStep, hne]

end Qatlib.Concepts.MatrixAccess.MatrixBackend.PaddedShiftCompression

namespace Qatlib.Concepts.MatrixAccess.MatrixBackend.PaddedShiftCompression

/-- With n + d ≤ N, the cyclic shift is unitary, the prefix frame is isometric, and compression
preserves every finite polynomial through degree d. -/
theorem cyclic_polynomial_representation {n N : ℕ} (hn : n ≤ N) (d : ℕ)
    (hpadding : n + d ≤ N) (coeff : ℕ → ℂ) :
    cyclicStep N 1 ∈ Matrix.unitaryGroup (Fin N) ℂ ∧
    (prefixFrame hn)ᴴ * prefixFrame hn = 1 ∧
    (prefixFrame hn)ᴴ * finitePolynomial d coeff (cyclicStep N 1) * prefixFrame hn =
      finitePolynomial d coeff (truncatedStep n 1) :=
  ⟨cyclicStep_unitary N, prefixFrame_isometry hn,
    prefix_cyclic_polynomial hn d hpadding coeff⟩

end Qatlib.Concepts.MatrixAccess.MatrixBackend.PaddedShiftCompression
