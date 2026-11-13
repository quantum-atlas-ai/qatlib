/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.CliffordGroup03.MainResults.Definitions

/-!
# Binary Pauli multiplication

This module proves the multiplication law for the binary Pauli convention of
[DehaeneDeMoor2003]. It combines the single-qubit sign rule, tensor-product multiplication, and
the carry from adding binary powers of `i` to obtain the phase-weighted formula.

## Main statements

* `tau1_mul`: the single-qubit multiplication rule.
* `tau_mul`: the tensor-product rule with a binary dot-product sign.
* `source_lemma_one_pauli_mul`: the full phase-weighted multiplication formula.

## References

* [Dehaene and De Moor, 2003][DehaeneDeMoor2003]
-/

set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false
set_option maxHeartbeats 2000000
noncomputable section

open Matrix
open Qatlib.Concepts.PauliClifford.PauliAlgebra
open Qatlib.Concepts.PauliClifford.PauliAlgebra.PauliCliffordLawsProofs
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.TensorRegisters.RegisterModel
open Qatlib.Concepts.PauliClifford.ExactRank (BooleanVec booleanDot)

namespace Qatlib.Papers.CliffordGroup03.MainResults

/-- Every element of `ZMod 2` is zero or one. -/
lemma zmod2_cases (x : ZMod 2) : x = 0 ∨ x = 1 := by
  fin_cases x <;> first | exact Or.inl rfl | exact Or.inr rfl

/-- The natural representative of zero in `ZMod 2` is zero. -/
@[simp] lemma zmod2_val_zero : (0 : ZMod 2).val = 0 := ZMod.val_zero

/-- The natural representative of one in `ZMod 2` is one. -/
@[simp] lemma zmod2_val_one : (1 : ZMod 2).val = 1 :=
  ZMod.val_one'' (n := 2) (by norm_num)

/-- One plus one equals zero in `ZMod 2`. -/
@[simp] lemma one_add_one_zmod2 : (1 : ZMod 2) + 1 = 0 := by decide

/-- The binary pair `(0,0)` specifies the identity Pauli letter. -/
@[simp] lemma letter_zero_zero : letter (0 : ZMod 2) (0 : ZMod 2) = Pauli1.I := by decide

/-- The binary pair `(1,0)` specifies the Pauli letter `Z`. -/
@[simp] lemma letter_one_zero : letter (1 : ZMod 2) (0 : ZMod 2) = Pauli1.Z := by decide

/-- The binary pair `(0,1)` specifies the Pauli letter `X`. -/
@[simp] lemma letter_zero_one : letter (0 : ZMod 2) (1 : ZMod 2) = Pauli1.X := by decide

/-- The binary pair `(1,1)` specifies the Pauli letter `Y`. -/
@[simp] lemma letter_one_one : letter (1 : ZMod 2) (1 : ZMod 2) = Pauli1.Y := by decide

/-- The matrix `tau1 0 0` is the identity Pauli matrix. -/
@[simp] lemma tau1_zero_zero : tau1 (0 : ZMod 2) (0 : ZMod 2) = P1 Pauli1.I := by
  simp [tau1]

/-- The matrix `tau1 1 0` is the Pauli `Z` matrix. -/
@[simp] lemma tau1_one_zero : tau1 (1 : ZMod 2) (0 : ZMod 2) = P1 Pauli1.Z := by
  simp [tau1]

/-- The matrix `tau1 0 1` is the Pauli `X` matrix. -/
@[simp] lemma tau1_zero_one : tau1 (0 : ZMod 2) (1 : ZMod 2) = P1 Pauli1.X := by
  simp [tau1]

/-- The matrix `tau1 1 1` is `i` times the Pauli `Y` matrix. -/
@[simp] lemma tau1_one_one : tau1 (1 : ZMod 2) (1 : ZMod 2) = Complex.I • P1 Pauli1.Y := by
  simp [tau1]

/-- Multiplying two single-qubit binary Pauli matrices adds their labels and contributes the
sign `(-1)^(v2*w1)`. -/
lemma tau1_mul (v1 w1 v2 w2 : ZMod 2) :
    tau1 v1 w1 * tau1 v2 w2
      = ((-1 : ℂ) ^ (v2 * w1).val) • tau1 (v1 + v2) (w1 + w2) := by
  rcases zmod2_cases v1 with rfl | rfl <;>
    rcases zmod2_cases w1 with rfl | rfl <;>
    rcases zmod2_cases v2 with rfl | rfl <;>
    rcases zmod2_cases w2 with rfl | rfl <;>
    simp only [tau1_zero_zero, tau1_one_zero, tau1_zero_one, tau1_one_one,
      zero_add, add_zero, one_add_one_zmod2, one_mul, zero_mul, mul_zero,
      zmod2_val_zero, zmod2_val_one, pow_zero, pow_one, one_smul] <;>
    ext x y <;> cases x <;> cases y <;>
    simp [P1, Matrix.mul_apply, Fintype.sum_bool, Matrix.smul_apply, smul_eq_mul] <;>
    ring_nf <;>
    simp only [pow_two, Complex.I_mul_I] <;>
    ring

/-- The complex sign `(-1)^x.val` associated with a binary scalar. -/
def signZ2 (x : ZMod 2) : ℂ := (-1 : ℂ) ^ x.val

/-- The complex sign associated with zero is one. -/
lemma signZ2_zero : signZ2 0 = 1 := by simp [signZ2]

/-- Addition of binary scalars corresponds to multiplication of their complex signs. -/
lemma signZ2_add (x y : ZMod 2) : signZ2 (x + y) = signZ2 x * signZ2 y := by
  rcases zmod2_cases x with rfl | rfl <;> rcases zmod2_cases y with rfl | rfl <;>
    simp [signZ2, zmod2_val_zero, zmod2_val_one, one_add_one_zmod2, pow_two]

/-- The product of finitely many binary signs equals the sign of the sum of their binary
exponents. -/
lemma prod_signZ2 {ι : Type*} [Fintype ι] (f : ι → ZMod 2) :
    (∏ k, signZ2 (f k)) = signZ2 (∑ k, f k) := by
  classical
  refine Finset.induction_on (Finset.univ : Finset ι) ?_ ?_
  · simp [signZ2_zero]
  · intro a s h ih
    rw [Finset.prod_insert h, Finset.sum_insert h, signZ2_add, ih]

/-- The product of complex powers of `-1` with binary exponents equals the power associated with
their sum in `ZMod 2`. -/
lemma prod_neg_one {ι : Type*} [Fintype ι] (f : ι → ZMod 2) :
    (∏ k, ((-1 : ℂ) ^ (f k).val)) = ((-1 : ℂ) ^ ((∑ k, f k).val)) := by
  simpa [signZ2] using prod_signZ2 f

/-- Multiplication of tensor-product binary Pauli matrices adds the labels and contributes the
sign determined by `booleanDot a2.1 a1.2`. -/
theorem tau_mul {n : ℕ} (a1 a2 : BV n × BV n) :
    tau a1 * tau a2
      = ((-1 : ℂ) ^ (booleanDot a2.1 a1.2).val) • tau (a1.1 + a2.1, a1.2 + a2.2) := by
  unfold tau
  rw [productMatrix_mul]
  have hfun : (fun k => tau1 (a1.1 k) (a1.2 k) * tau1 (a2.1 k) (a2.2 k))
      = (fun k => ((-1 : ℂ) ^ ((a2.1 k * a1.2 k).val)) •
          tau1 (a1.1 k + a2.1 k) (a1.2 k + a2.2 k)) := by
    funext k; rw [tau1_mul]
  rw [hfun, smul_pow_eq_pow_sum, prod_neg_one]
  rfl

/-- Combines two binary `i`-phase and sign factors with an additional sign, including the carry
term `δ1*δ2`. -/
lemma delta_epsilon_law (δ1 δ2 ε1 ε2 b : ZMod 2) :
    ((Complex.I ^ δ1.val : ℂ) * ((-1 : ℂ) ^ ε1.val)) *
        ((Complex.I ^ δ2.val : ℂ) * ((-1 : ℂ) ^ ε2.val)) * ((-1 : ℂ) ^ b.val)
      = (Complex.I ^ (δ1 + δ2).val : ℂ) *
          ((-1 : ℂ) ^ (ε1 + ε2 + δ1 * δ2 + b).val) := by
  rcases zmod2_cases δ1 with rfl | rfl <;>
    rcases zmod2_cases δ2 with rfl | rfl <;>
    rcases zmod2_cases ε1 with rfl | rfl <;>
    rcases zmod2_cases ε2 with rfl | rfl <;>
    rcases zmod2_cases b with rfl | rfl <;>
    simp only [zmod2_val_zero, zmod2_val_one, one_add_one_zmod2, zero_add, add_zero,
      pow_one, pow_zero, one_mul, mul_one, zero_mul, mul_zero] <;>
    ring_nf <;>
    simp only [pow_two, Complex.I_mul_I] <;>
    ring

/-- Multiplying two phase-weighted binary Pauli matrices adds their labels and updates the sign
by the phase carry and binary dot product. This is the multiplication formula of [Dehaene
and De Moor, Lemma 1][DehaeneDeMoor2003]. -/
theorem source_lemma_one_pauli_mul {n : ℕ}
    (a1 a2 : BV n × BV n) (δ1 δ2 ε1 ε2 : ZMod 2) :
    (((Complex.I ^ δ1.val : ℂ) * ((-1 : ℂ) ^ ε1.val)) • tau a1) *
        (((Complex.I ^ δ2.val : ℂ) * ((-1 : ℂ) ^ ε2.val)) • tau a2)
      = ((Complex.I ^ (δ1 + δ2).val : ℂ) *
          ((-1 : ℂ) ^ (ε1 + ε2 + δ1 * δ2 + booleanDot a2.1 a1.2).val)) •
          tau (a1.1 + a2.1, a1.2 + a2.2) := by
  rw [Algebra.smul_mul_assoc, Algebra.mul_smul_comm, tau_mul, smul_smul, smul_smul]
  rw [delta_epsilon_law δ1 δ2 ε1 ε2 (booleanDot a2.1 a1.2)]

end Qatlib.Papers.CliffordGroup03.MainResults
