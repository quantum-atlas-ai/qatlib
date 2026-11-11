/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.LinearAlgebra.Matrix.Permutation
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Tactic

/-!
# Reversible comparison oracles and phase kickback

This module constructs a reversible oracle from computation of a Boolean bank, comparison with a
target, and uncomputation. The permutation `oraclePerm` restores the bank and flips the output
bit according to the comparison; on a zero bank it tests `values k = target`.

The corresponding unitary matrix acts as the diagonal phase oracle `phaseMatrix` on inputs
embedded with a zero bank and a minus-state output qubit. This is the standard phase-kickback
construction [NielsenChuang2010].

## Main statements

* `oraclePerm_clean`: the oracle compares computed values on clean workspace.
* `oracleMatrix_unitary`: the oracle permutation matrix is unitary.
* `oracleMatrix_embed`: the embedded action implements the comparison phase.
* `auxiliary_normalized`: the auxiliary zero-bank and minus-qubit vector is normalized.

## References

* [Nielsen and Chuang, 2010][NielsenChuang2010]
-/

namespace Qatlib.Concepts.CipherCircuits.CipherOracle
set_option autoImplicit false
noncomputable section
open scoped Matrix
variable {I J : Type*}

/-- A Boolean bank with one bit for each index in `J`. -/
abbrev Bank (J : Type*) := J → Bool

/-- The joint basis labels for an input, a Boolean workspace bank, and an output bit. -/
abbrev Whole (I J : Type*) := I × (Bank J × Bool)

/-- The Boolean bank whose entries are all `false`. -/
def zeroBank : Bank J := fun _ => false

/-- The entrywise XOR of two Boolean banks. -/
def bankXor (a b : Bank J) : Bank J := fun j => a j ^^ b j

/-- XORing a Boolean bank with the same bank twice restores the original bank. -/
theorem bankXor_twice (a b : Bank J) : bankXor (bankXor a b) b = a := by
  funext j
  simp [bankXor]

/-- XORing the zero bank with `b` yields `b`. -/
theorem bankXor_zero (b : Bank J) : bankXor zeroBank b = b := by
  funext j
  simp [bankXor, zeroBank]

/-- The reversible computation step that XORs `values` of the input into the workspace bank and
preserves the input and output bit. -/
def computeFn (values : I → Bank J) (x : Whole I J) : Whole I J :=
  (x.1, (bankXor x.2.1 (values x.1), x.2.2))

/-- The self-inverse permutation implementing the workspace XOR computation `computeFn`. -/
def computePerm (values : I → Bank J) : Equiv.Perm (Whole I J) where
  toFun := computeFn values
  invFun := computeFn values
  left_inv := by rintro ⟨k,w,b⟩; simp [computeFn, bankXor_twice]
  right_inv := by rintro ⟨k,w,b⟩; simp [computeFn, bankXor_twice]
variable [Fintype J]

/-- The operation that flips the output bit exactly when the workspace bank equals the target. -/
def compareFn (target : Bank J) (x : Whole I J) : Whole I J :=
  (x.1, (x.2.1, x.2.2 ^^ decide (x.2.1 = target)))

/-- The self-inverse permutation implementing comparison of the workspace bank with the target. -/
def comparePerm (target : Bank J) : Equiv.Perm (Whole I J) where
  toFun := compareFn target
  invFun := compareFn target
  left_inv := by
    rintro ⟨k,w,b⟩
    cases b <;> by_cases h : w = target <;> simp [compareFn, h]
  right_inv := by
    rintro ⟨k,w,b⟩
    cases b <;> by_cases h : w = target <;> simp [compareFn, h]

/-- The permutation that computes into the workspace, flips the comparison bit, and uncomputes
the workspace. -/
def oraclePerm (values : I → Bank J) (target : Bank J) : Equiv.Perm (Whole I J) :=
  (computePerm values).trans ((comparePerm target).trans (computePerm values))

/-- The oracle restores the input and workspace, and XORs the output bit with the test that `w`
XOR `values k` equals the target. -/
theorem oraclePerm_apply (values : I → Bank J) (target : Bank J) (k : I)
    (w : Bank J) (b : Bool) :
    oraclePerm values target (k,w,b) =
      (k,w,b ^^ decide (bankXor w (values k) = target)) := by
  simp [oraclePerm, computePerm, comparePerm, computeFn, compareFn, bankXor_twice]

/-- On a zero workspace bank, the oracle preserves the bank and flips the output bit exactly
when `values k = target`. -/
theorem oraclePerm_clean (values : I → Bank J) (target : Bank J) (k : I) (b : Bool) :
    oraclePerm values target (k,zeroBank,b) =
      (k,zeroBank,b ^^ decide (values k = target)) := by
  rw [oraclePerm_apply, bankXor_zero]

/-- Applying the comparison oracle permutation twice returns the original joint basis label. -/
theorem oraclePerm_involutive (values : I → Bank J) (target : Bank J) :
    Function.Involutive (oraclePerm values target) := by
  rintro ⟨k,w,b⟩
  simp only [oraclePerm_apply]
  cases b <;> by_cases h : bankXor w (values k) = target <;> simp [h]
variable [Fintype I] [DecidableEq I] [DecidableEq J]

/-- The complex permutation matrix of the reversible comparison oracle. -/
def oracleMatrix (values : I → Bank J) (target : Bank J) :
    Matrix (Whole I J) (Whole I J) ℂ := (oraclePerm values target).permMatrix ℂ

/-- The complex permutation matrix associated with a permutation of a finite type is unitary. -/
theorem permutation_unitary {X : Type*} [Fintype X] [DecidableEq X] (e : Equiv.Perm X) :
    e.permMatrix ℂ ∈ Matrix.unitaryGroup X ℂ := by
  rw [Matrix.mem_unitaryGroup_iff', Matrix.star_eq_conjTranspose,
    Matrix.conjTranspose_permMatrix, ← Matrix.permMatrix_mul]
  simp

/-- The matrix of the reversible comparison oracle is unitary. -/
theorem oracleMatrix_unitary (values : I → Bank J) (target : Bank J) :
    oracleMatrix values target ∈ Matrix.unitaryGroup (Whole I J) ℂ :=
  permutation_unitary _

/-- The amplitudes of the minus qubit state, with positive coefficient at `false` and negative
coefficient at `true`. -/
def minus (b : Bool) : ℂ := if b then -((Real.sqrt 2 / 2 : ℝ) : ℂ) else ((Real.sqrt 2 / 2 : ℝ) : ℂ)

/-- XORing the minus-state index by `t` multiplies its amplitude by minus one exactly when `t`
is true. -/
theorem minus_xor (b t : Bool) : minus (b ^^ t) = (if t then (-1 : ℂ) else 1) * minus b := by
  cases b <;> cases t <;> simp [minus]

/-- The auxiliary amplitude vector supported on the zero workspace bank with the output qubit in
the minus state. -/
def auxiliary (x : Bank J × Bool) : ℂ := if x.1 = zeroBank then minus x.2 else 0

/-- The amplitude vector obtained by adjoining the auxiliary zero-bank and minus-qubit vector to
`ψ`. -/
def embed (ψ : I → ℂ) (x : Whole I J) : ℂ := ψ x.1 * auxiliary x.2

/-- The diagonal matrix that negates precisely those input basis states whose computed value
equals the target. -/
def phaseMatrix (values : I → Bank J) (target : Bank J) : Matrix I I ℂ :=
  Matrix.diagonal (fun k => if values k = target then -1 else 1)
omit [DecidableEq J] in

/-- The comparison phase matrix multiplies each input amplitude by minus one for a matching
value and by one otherwise. -/
theorem phaseMatrix_mulVec (values : I → Bank J) (target : Bank J) (ψ : I → ℂ) (k : I) :
    (phaseMatrix values target *ᵥ ψ) k = (if values k = target then -1 else 1) * ψ k := by
  simp [phaseMatrix, Matrix.mulVec, dotProduct, Matrix.diagonal_apply]

/-- The reversible oracle on an embedded input equals the embedding of the comparison phase
oracle applied to that input. -/
theorem oracleMatrix_embed (values : I → Bank J) (target : Bank J) (ψ : I → ℂ) :
    oracleMatrix values target *ᵥ embed ψ = embed (phaseMatrix values target *ᵥ ψ) := by
  rw [oracleMatrix, Matrix.permMatrix_mulVec]
  funext x
  rcases x with ⟨k,w,b⟩
  rw [Function.comp_apply, oraclePerm_apply]
  by_cases hw : w = zeroBank
  · subst w
    by_cases h : values k = target
    · cases b <;> simp [embed, auxiliary, bankXor_zero, phaseMatrix_mulVec, h, minus]
    · cases b <;> simp [embed, auxiliary, bankXor_zero, phaseMatrix_mulVec, h, minus]
  · simp [embed, auxiliary, hw]

/-- Each computational basis amplitude of the minus qubit state has squared norm one half. -/
theorem minus_norm_sq (b : Bool) : ‖minus b‖ ^ 2 = (1 : ℝ) / 2 := by
  have h : ‖((Real.sqrt 2 / 2 : ℝ) : ℂ)‖ ^ 2 = (1 : ℝ) / 2 := by
    rw [Complex.norm_real, Real.norm_eq_abs, sq_abs, div_pow, Real.sq_sqrt (by norm_num)]
    norm_num
  cases b <;> simpa [minus] using h

/-- The auxiliary zero-bank and minus-qubit amplitude vector has total squared norm one. -/
theorem auxiliary_normalized : ∑ x : Bank J × Bool, ‖auxiliary x‖ ^ 2 = 1 := by
  rw [Fintype.sum_prod_type]
  have h (w : Bank J) : (∑ b : Bool, ‖auxiliary (w,b)‖ ^ 2) =
      if w = zeroBank then 1 else 0 := by
    by_cases hw : w = zeroBank
    · simp [auxiliary, hw, minus_norm_sq]
    · simp [auxiliary, hw]
  simp_rw [h]
  simp

end
end Qatlib.Concepts.CipherCircuits.CipherOracle
