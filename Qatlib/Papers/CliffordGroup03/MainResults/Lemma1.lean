/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.CliffordGroup03.MainResults.Definitions
set_option warningAsError false
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

lemma zmod2_cases (x : ZMod 2) : x = 0 ∨ x = 1 := by
  fin_cases x <;> first | exact Or.inl rfl | exact Or.inr rfl

@[simp] lemma zmod2_val_zero : (0 : ZMod 2).val = 0 := ZMod.val_zero

@[simp] lemma zmod2_val_one : (1 : ZMod 2).val = 1 :=
  ZMod.val_one'' (n := 2) (by norm_num)

@[simp] lemma one_add_one_zmod2 : (1 : ZMod 2) + 1 = 0 := by decide

@[simp] lemma letter_zero_zero : letter (0 : ZMod 2) (0 : ZMod 2) = Pauli1.I := by decide

@[simp] lemma letter_one_zero : letter (1 : ZMod 2) (0 : ZMod 2) = Pauli1.Z := by decide

@[simp] lemma letter_zero_one : letter (0 : ZMod 2) (1 : ZMod 2) = Pauli1.X := by decide

@[simp] lemma letter_one_one : letter (1 : ZMod 2) (1 : ZMod 2) = Pauli1.Y := by decide

@[simp] lemma tau1_zero_zero : tau1 (0 : ZMod 2) (0 : ZMod 2) = P1 Pauli1.I := by
  simp [tau1]

@[simp] lemma tau1_one_zero : tau1 (1 : ZMod 2) (0 : ZMod 2) = P1 Pauli1.Z := by
  simp [tau1]

@[simp] lemma tau1_zero_one : tau1 (0 : ZMod 2) (1 : ZMod 2) = P1 Pauli1.X := by
  simp [tau1]

@[simp] lemma tau1_one_one : tau1 (1 : ZMod 2) (1 : ZMod 2) = Complex.I • P1 Pauli1.Y := by
  simp [tau1]

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

def signZ2 (x : ZMod 2) : ℂ := (-1 : ℂ) ^ x.val

lemma signZ2_zero : signZ2 0 = 1 := by simp [signZ2]

lemma signZ2_add (x y : ZMod 2) : signZ2 (x + y) = signZ2 x * signZ2 y := by
  rcases zmod2_cases x with rfl | rfl <;> rcases zmod2_cases y with rfl | rfl <;>
    simp [signZ2, zmod2_val_zero, zmod2_val_one, one_add_one_zmod2, pow_two]

lemma prod_signZ2 {ι : Type*} [Fintype ι] (f : ι → ZMod 2) :
    (∏ k, signZ2 (f k)) = signZ2 (∑ k, f k) := by
  classical
  refine Finset.induction_on (Finset.univ : Finset ι) ?_ ?_
  · simp [signZ2_zero]
  · intro a s h ih
    rw [Finset.prod_insert h, Finset.sum_insert h, signZ2_add, ih]

lemma prod_neg_one {ι : Type*} [Fintype ι] (f : ι → ZMod 2) :
    (∏ k, ((-1 : ℂ) ^ (f k).val)) = ((-1 : ℂ) ^ ((∑ k, f k).val)) := by
  simpa [signZ2] using prod_signZ2 f

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
