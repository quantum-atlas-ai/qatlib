/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Algebra.Field.ZMod
import Mathlib.Algebra.Lie.OfAssociative
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.LinearAlgebra.Matrix.Hermitian
import Mathlib.Tactic.Ext
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Tactic.SimpRw

namespace Qatlib.Concepts.CodingDecoding.CssTesters

open Matrix

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def bitDot (z x : ι → ZMod 2) : ZMod 2 := dotProduct z x

def phaseOfBit (b : ZMod 2) : ℂ := if b = 1 then -1 else 1

def cssPauliX (x : ι → ZMod 2) : Matrix (ι → ZMod 2) (ι → ZMod 2) ℂ :=
  Matrix.of fun a b => if a = b + x then 1 else 0

def cssPauliZ (z : ι → ZMod 2) : Matrix (ι → ZMod 2) (ι → ZMod 2) ℂ :=
  Matrix.diagonal fun a => phaseOfBit (bitDot z a)

def bitWeight (v : ι → ZMod 2) : ℕ := (Finset.univ.filter fun i => v i ≠ 0).card

def pauliWeight (x z : ι → ZMod 2) : ℕ :=
  (Finset.univ.filter fun i => x i ≠ 0 ∨ z i ≠ 0).card

theorem phaseOfBit_add (b b' : ZMod 2) :
    phaseOfBit (b + b') = phaseOfBit b * phaseOfBit b' := by
  have h01 : (0 : ZMod 2) ≠ 1 := by decide
  have h11 : (1 : ZMod 2) + 1 = 0 := by decide
  have hc : ∀ a : ZMod 2, a = 0 ∨ a = 1 := by decide
  rcases hc b with rfl | rfl <;> rcases hc b' with rfl | rfl <;> simp [phaseOfBit, h01, h11]

@[simp] theorem phaseOfBit_zero : phaseOfBit 0 = 1 := by norm_num [phaseOfBit]

@[simp] theorem phaseOfBit_one : phaseOfBit 1 = -1 := by norm_num [phaseOfBit]

theorem phaseOfBit_mul_self (b : ZMod 2) : phaseOfBit b * phaseOfBit b = 1 := by
  have h01 : (0 : ZMod 2) ≠ 1 := by decide
  have hc : b = 0 ∨ b = 1 := by exact (by decide : ∀ a : ZMod 2, a = 0 ∨ a = 1) b
  rcases hc with rfl | rfl <;> simp [phaseOfBit, h01]

omit [DecidableEq ι] in

theorem bitDot_add_left (z z' x : ι → ZMod 2) :
    bitDot (z + z') x = bitDot z x + bitDot z' x := by
  simp [bitDot, dotProduct, add_mul, Finset.sum_add_distrib]

omit [DecidableEq ι] in

theorem bitDot_add_right (z x x' : ι → ZMod 2) :
    bitDot z (x + x') = bitDot z x + bitDot z x' := by
  simp [bitDot, dotProduct, mul_add, Finset.sum_add_distrib]

omit [DecidableEq ι] in

@[simp] theorem bitDot_zero_left (x : ι → ZMod 2) : bitDot 0 x = 0 := by simp [bitDot]
omit [DecidableEq ι] in

@[simp] theorem bitDot_zero_right (z : ι → ZMod 2) : bitDot z 0 = 0 := by simp [bitDot]

omit [Fintype ι] [DecidableEq ι] in

theorem binary_add_self (x : ι → ZMod 2) : x + x = 0 := by
  ext i
  change x i + x i = 0
  rw [← two_mul, show (2 : ZMod 2) = 0 from by decide, zero_mul]

theorem cssPauliX_mul (x x' : ι → ZMod 2) : cssPauliX x * cssPauliX x' = cssPauliX (x + x') := by
  classical
  ext a b
  simp [Matrix.mul_apply, cssPauliX, mul_ite, add_comm, add_left_comm]

theorem cssPauliZ_mul (z z' : ι → ZMod 2) : cssPauliZ z * cssPauliZ z' = cssPauliZ (z + z') := by
  classical
  rw [cssPauliZ, cssPauliZ, cssPauliZ, Matrix.diagonal_mul_diagonal]
  congr 1
  funext a
  exact (phaseOfBit_add (bitDot z a) (bitDot z' a)).symm.trans
    (congrArg phaseOfBit (bitDot_add_left z z' a)).symm

omit [DecidableEq ι] in

@[simp] theorem cssPauliX_zero : cssPauliX (0 : ι → ZMod 2) = 1 := by
  classical
  ext a b
  simp [cssPauliX, Matrix.one_apply]

omit [DecidableEq ι] in

@[simp] theorem cssPauliZ_zero : cssPauliZ (0 : ι → ZMod 2) = 1 := by
  classical
  ext a b
  simp [cssPauliZ, Matrix.diagonal_apply, Matrix.one_apply]

theorem cssPauliXZ_apply (x z : ι → ZMod 2) (a b : ι → ZMod 2) :
    (cssPauliX x * cssPauliZ z) a b = if a = b + x then phaseOfBit (bitDot z b) else 0 := by
  classical
  simp [cssPauliX, cssPauliZ, Matrix.mul_apply, Matrix.diagonal, mul_ite]

theorem cssPauliZX_apply (x z : ι → ZMod 2) (a b : ι → ZMod 2) :
    (cssPauliZ z * cssPauliX x) a b = if a = b + x then phaseOfBit (bitDot z a) else 0 := by
  classical
  simp [cssPauliX, cssPauliZ, Matrix.mul_apply, Matrix.diagonal]

omit [DecidableEq ι] in

@[simp] theorem pauliWeight_zero_left (z : ι → ZMod 2) : pauliWeight 0 z = bitWeight z := by
  simp [pauliWeight, bitWeight]

omit [DecidableEq ι] in

@[simp] theorem pauliWeight_zero_right (x : ι → ZMod 2) : pauliWeight x 0 = bitWeight x := by
  simp [pauliWeight, bitWeight]

omit [DecidableEq ι] in

theorem bitWeight_le_pauliWeight_left (x z : ι → ZMod 2) : bitWeight x ≤ pauliWeight x z := by
  apply Finset.card_le_card
  intro i hi
  exact Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hi).1, Or.inl (Finset.mem_filter.mp hi).2⟩

omit [DecidableEq ι] in

theorem bitWeight_le_pauliWeight_right (x z : ι → ZMod 2) : bitWeight z ≤ pauliWeight x z := by
  apply Finset.card_le_card
  intro i hi
  exact Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hi).1, Or.inr (Finset.mem_filter.mp hi).2⟩

theorem cssPauliZX_phase (x z : ι → ZMod 2) :
    cssPauliZ z * cssPauliX x = phaseOfBit (bitDot z x) • (cssPauliX x * cssPauliZ z) := by
  classical
  ext a b
  simp only [Matrix.smul_apply, smul_eq_mul, cssPauliZX_apply, cssPauliXZ_apply]
  by_cases h : a = b + x
  · subst a
    simp only [if_true, bitDot_add_right, phaseOfBit_add]
    ring
  · simp [h]

theorem cssPauliXZ_comm (x z : ι → ZMod 2) :
    cssPauliX x * cssPauliZ z = phaseOfBit (bitDot z x) • (cssPauliZ z * cssPauliX x) := by
  rw [cssPauliZX_phase, smul_smul, phaseOfBit_mul_self, one_smul]

theorem cssPauliXZ_mul (x x' z z' : ι → ZMod 2) :
    (cssPauliX x * cssPauliZ z) * (cssPauliX x' * cssPauliZ z') =
      phaseOfBit (bitDot z x') • (cssPauliX (x + x') * cssPauliZ (z + z')) := by
  calc
    _ = cssPauliX x * ((cssPauliZ z * cssPauliX x') * cssPauliZ z') := by simp only [mul_assoc]
    _ = phaseOfBit (bitDot z x') • ((cssPauliX x * cssPauliX x') * (cssPauliZ z * cssPauliZ z')) := by
      rw [cssPauliZX_phase]
      simp only [Matrix.smul_mul, Matrix.mul_smul, mul_assoc]
    _ = _ := by rw [cssPauliX_mul, cssPauliZ_mul]

theorem bitDot_single (z : ι → ZMod 2) (i : ι) :
    bitDot z (Pi.single i 1) = z i := by
  simp [bitDot, dotProduct, Pi.single_apply, mul_ite]

theorem sum_phase_bitDot (z : ι → ZMod 2) :
    (∑ a : ι → ZMod 2, phaseOfBit (bitDot z a)) =
      if z = 0 then (Fintype.card (ι → ZMod 2) : ℂ) else 0 := by
  classical
  by_cases hz : z = 0
  · subst z
    simp
  · rw [if_neg hz]
    have hi : ∃ i, z i ≠ 0 := by
      by_contra h
      push Not at h
      exact hz (funext h)
    obtain ⟨i, hzi⟩ := hi
    have hz1 : z i = 1 := by
      rcases (by decide : ∀ b : ZMod 2, b = 0 ∨ b = 1) (z i) with h0 | h1
      · exact False.elim (hzi h0)
      · exact h1
    let e : ι → ZMod 2 := Pi.single i 1
    have hd : bitDot z e = 1 := by rw [bitDot_single, hz1]
    have he : Function.Involutive (fun a : ι → ZMod 2 => a + e) := by
      intro a
      simp only [add_assoc, binary_add_self, add_zero]
    have hs : (∑ a : ι → ZMod 2, phaseOfBit (bitDot z (a + e))) =
        ∑ a : ι → ZMod 2, phaseOfBit (bitDot z a) :=
      Fintype.sum_bijective _ he.bijective _ _ (fun _ => rfl)
    simp_rw [bitDot_add_right, hd, phaseOfBit_add, phaseOfBit_one, mul_neg_one] at hs
    rw [Finset.sum_neg_distrib] at hs
    linear_combination (-1 / 2 : ℂ) * hs

theorem cssPauliXZ_trace (x z : ι → ZMod 2) :
    Matrix.trace (cssPauliX x * cssPauliZ z) =
      if x = 0 ∧ z = 0 then (Fintype.card (ι → ZMod 2) : ℂ) else 0 := by
  classical
  by_cases hx : x = 0
  · subst x
    simp only [cssPauliX_zero, one_mul, cssPauliZ, Matrix.trace_diagonal]
    simpa using sum_phase_bitDot z
  · have hn (a : ι → ZMod 2) : a ≠ a + x := by
      intro hh
      have he : a + 0 = a + x := by simpa using hh
      exact hx (add_left_cancel he).symm
    simp [Matrix.trace, Matrix.diag_apply, cssPauliXZ_apply, hn, hx]

omit [DecidableEq ι] in

theorem bitDot_comm (x z : ι → ZMod 2) : bitDot x z = bitDot z x := by
  simp only [bitDot, dotProduct]
  apply Finset.sum_congr rfl
  intro i _
  exact mul_comm _ _

theorem cssPauliX_self_mul (x : ι → ZMod 2) : cssPauliX x * cssPauliX x = 1 := by
  rw [cssPauliX_mul, binary_add_self, cssPauliX_zero]

theorem cssPauliZ_self_mul (z : ι → ZMod 2) : cssPauliZ z * cssPauliZ z = 1 := by
  rw [cssPauliZ_mul, binary_add_self, cssPauliZ_zero]

theorem phaseOfBit_star (b : ZMod 2) : star (phaseOfBit b) = phaseOfBit b := by
  by_cases h : b = 1 <;> simp [phaseOfBit, h]

theorem cssPauliX_isHermitian (x : ι → ZMod 2) : (cssPauliX x).IsHermitian := by
  classical
  apply Matrix.IsHermitian.ext
  intro a b
  simp only [cssPauliX, Matrix.of_apply, apply_ite (star : ℂ → ℂ), star_one, star_zero]
  have he : b = a + x ↔ a = b + x := by
    constructor <;> intro h
    · subst b
      simp only [add_assoc, binary_add_self, add_zero]
    · subst a
      simp only [add_assoc, binary_add_self, add_zero]
  simp only [he]

theorem cssPauliZ_isHermitian (z : ι → ZMod 2) : (cssPauliZ z).IsHermitian := by
  classical
  apply Matrix.IsHermitian.ext
  intro a b
  by_cases h : a = b
  · subst b
    simpa [cssPauliZ, Matrix.diagonal_apply] using phaseOfBit_star (bitDot z a)
  · simp [cssPauliZ, Matrix.diagonal_apply, h, Ne.symm h]

end Qatlib.Concepts.CodingDecoding.CssTesters
