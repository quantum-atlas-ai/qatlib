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

/-!
# Binary Pauli operators

This module defines binary dot products, complex signs, Hamming weights, and the finite-register
Pauli operators `cssPauliX` and `cssPauliZ`. It proves their multiplication and commutation
laws, including the phase determined by the binary dot product, in the stabilizer formalism of
[Gottesman1997].

Character sums yield the Pauli trace identity. Each X or Z operator squares to the identity and
is Hermitian; the joint support weight bounds both component Hamming weights.

## Main statements

* `cssPauliXZ_mul`: gives multiplication of binary Pauli products with its phase factor.
* `cssPauliXZ_comm`: gives the X-Z commutation phase.
* `sum_phase_bitDot`: evaluates binary dot-product character sums.
* `cssPauliXZ_trace`: computes the trace of every binary Pauli product.
* `cssPauliX_isHermitian` and `cssPauliZ_isHermitian`: prove Hermiticity.

## References

* [Gottesman, 1997][Gottesman1997]
-/

namespace Qatlib.Concepts.CodingDecoding.CssTesters

open Matrix

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The dot product of two binary vectors, valued in `ZMod 2`. -/
def bitDot (z x : ι → ZMod 2) : ZMod 2 := dotProduct z x

/-- The complex sign equal to `1` at the zero bit and `-1` at the unit bit. -/
def phaseOfBit (b : ZMod 2) : ℂ := if b = 1 then -1 else 1

/-- The Pauli X operator that translates computational basis labels by the binary vector `x`. -/
def cssPauliX (x : ι → ZMod 2) : Matrix (ι → ZMod 2) (ι → ZMod 2) ℂ :=
  Matrix.of fun a b => if a = b + x then 1 else 0

/-- The diagonal Pauli Z operator whose entry at `a` is the sign determined by `bitDot z a`. -/
def cssPauliZ (z : ι → ZMod 2) : Matrix (ι → ZMod 2) (ι → ZMod 2) ℂ :=
  Matrix.diagonal fun a => phaseOfBit (bitDot z a)

/-- The Hamming weight of a binary vector, counting its nonzero coordinates. -/
def bitWeight (v : ι → ZMod 2) : ℕ := (Finset.univ.filter fun i => v i ≠ 0).card

/-- The number of coordinates where at least one of the X and Z labels is nonzero. -/
def pauliWeight (x z : ι → ZMod 2) : ℕ :=
  (Finset.univ.filter fun i => x i ≠ 0 ∨ z i ≠ 0).card

/-- The sign of a sum of binary bits is the product of their signs. -/
theorem phaseOfBit_add (b b' : ZMod 2) :
    phaseOfBit (b + b') = phaseOfBit b * phaseOfBit b' := by
  have h01 : (0 : ZMod 2) ≠ 1 := by decide
  have h11 : (1 : ZMod 2) + 1 = 0 := by decide
  have hc : ∀ a : ZMod 2, a = 0 ∨ a = 1 := by decide
  rcases hc b with rfl | rfl <;> rcases hc b' with rfl | rfl <;> simp [phaseOfBit, h01, h11]

/-- The complex phase associated with the zero bit is one. -/
@[simp] theorem phaseOfBit_zero : phaseOfBit 0 = 1 := by norm_num [phaseOfBit]

/-- The complex phase associated with the unit bit is minus one. -/
@[simp] theorem phaseOfBit_one : phaseOfBit 1 = -1 := by norm_num [phaseOfBit]

/-- Every binary phase squares to one. -/
theorem phaseOfBit_mul_self (b : ZMod 2) : phaseOfBit b * phaseOfBit b = 1 := by
  have h01 : (0 : ZMod 2) ≠ 1 := by decide
  have hc : b = 0 ∨ b = 1 := by exact (by decide : ∀ a : ZMod 2, a = 0 ∨ a = 1) b
  rcases hc with rfl | rfl <;> simp [phaseOfBit, h01]

omit [DecidableEq ι] in

/-- The binary dot product is additive in its first argument. -/
theorem bitDot_add_left (z z' x : ι → ZMod 2) :
    bitDot (z + z') x = bitDot z x + bitDot z' x := by
  simp [bitDot, dotProduct, add_mul, Finset.sum_add_distrib]

omit [DecidableEq ι] in

/-- The binary dot product is additive in its second argument. -/
theorem bitDot_add_right (z x x' : ι → ZMod 2) :
    bitDot z (x + x') = bitDot z x + bitDot z x' := by
  simp [bitDot, dotProduct, mul_add, Finset.sum_add_distrib]

omit [DecidableEq ι] in

/-- The binary dot product with zero in the first argument is zero. -/
@[simp] theorem bitDot_zero_left (x : ι → ZMod 2) : bitDot 0 x = 0 := by simp [bitDot]
omit [DecidableEq ι] in

/-- The binary dot product with zero in the second argument is zero. -/
@[simp] theorem bitDot_zero_right (z : ι → ZMod 2) : bitDot z 0 = 0 := by simp [bitDot]

omit [Fintype ι] [DecidableEq ι] in

/-- Every binary vector sums with itself to zero. -/
theorem binary_add_self (x : ι → ZMod 2) : x + x = 0 := by
  ext i
  change x i + x i = 0
  rw [← two_mul, show (2 : ZMod 2) = 0 from by decide, zero_mul]

/-- Multiplying two binary X operators adds their labels, as in the Pauli multiplication rules
of [Gottesman1997]. -/
theorem cssPauliX_mul (x x' : ι → ZMod 2) : cssPauliX x * cssPauliX x' = cssPauliX (x + x') := by
  classical
  ext a b
  simp [Matrix.mul_apply, cssPauliX, mul_ite, add_comm, add_left_comm]

/-- Multiplying two binary Z operators adds their labels, as in the Pauli multiplication rules
of [Gottesman1997]. -/
theorem cssPauliZ_mul (z z' : ι → ZMod 2) : cssPauliZ z * cssPauliZ z' = cssPauliZ (z + z') := by
  classical
  rw [cssPauliZ, cssPauliZ, cssPauliZ, Matrix.diagonal_mul_diagonal]
  congr 1
  funext a
  exact (phaseOfBit_add (bitDot z a) (bitDot z' a)).symm.trans
    (congrArg phaseOfBit (bitDot_add_left z z' a)).symm

omit [DecidableEq ι] in

/-- The binary X operator with zero label is the identity. -/
@[simp] theorem cssPauliX_zero : cssPauliX (0 : ι → ZMod 2) = 1 := by
  classical
  ext a b
  simp [cssPauliX, Matrix.one_apply]

omit [DecidableEq ι] in

/-- The binary Z operator with zero label is the identity. -/
@[simp] theorem cssPauliZ_zero : cssPauliZ (0 : ι → ZMod 2) = 1 := by
  classical
  ext a b
  simp [cssPauliZ, Matrix.diagonal_apply, Matrix.one_apply]

/-- An entry of `cssPauliX x * cssPauliZ z` is zero unless its row label is its column label
plus `x`, when it equals the phase determined by `z` and the column label. -/
theorem cssPauliXZ_apply (x z : ι → ZMod 2) (a b : ι → ZMod 2) :
    (cssPauliX x * cssPauliZ z) a b = if a = b + x then phaseOfBit (bitDot z b) else 0 := by
  classical
  simp [cssPauliX, cssPauliZ, Matrix.mul_apply, Matrix.diagonal, mul_ite]

/-- An entry of `cssPauliZ z * cssPauliX x` is zero unless its row label is its column label
plus `x`, when it equals the phase determined by `z` and the row label. -/
theorem cssPauliZX_apply (x z : ι → ZMod 2) (a b : ι → ZMod 2) :
    (cssPauliZ z * cssPauliX x) a b = if a = b + x then phaseOfBit (bitDot z a) else 0 := by
  classical
  simp [cssPauliX, cssPauliZ, Matrix.mul_apply, Matrix.diagonal]

omit [DecidableEq ι] in

/-- A Pauli label with zero X component has weight equal to the Hamming weight of its Z
component. -/
@[simp] theorem pauliWeight_zero_left (z : ι → ZMod 2) : pauliWeight 0 z = bitWeight z := by
  simp [pauliWeight, bitWeight]

omit [DecidableEq ι] in

/-- A Pauli label with zero Z component has weight equal to the Hamming weight of its X
component. -/
@[simp] theorem pauliWeight_zero_right (x : ι → ZMod 2) : pauliWeight x 0 = bitWeight x := by
  simp [pauliWeight, bitWeight]

omit [DecidableEq ι] in

/-- The Hamming weight of the X label is at most the joint Pauli weight. -/
theorem bitWeight_le_pauliWeight_left (x z : ι → ZMod 2) : bitWeight x ≤ pauliWeight x z := by
  apply Finset.card_le_card
  intro i hi
  exact Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hi).1, Or.inl (Finset.mem_filter.mp hi).2⟩

omit [DecidableEq ι] in

/-- The Hamming weight of the Z label is at most the joint Pauli weight. -/
theorem bitWeight_le_pauliWeight_right (x z : ι → ZMod 2) : bitWeight z ≤ pauliWeight x z := by
  apply Finset.card_le_card
  intro i hi
  exact Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hi).1, Or.inr (Finset.mem_filter.mp hi).2⟩

/-- Commuting a Z operator past an X operator introduces the binary dot-product phase. -/
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

/-- Interchanging the X and Z factors introduces the sign determined by their binary dot
product, as in the Pauli commutation rules of [Gottesman1997]. -/
theorem cssPauliXZ_comm (x z : ι → ZMod 2) :
    cssPauliX x * cssPauliZ z = phaseOfBit (bitDot z x) • (cssPauliZ z * cssPauliX x) := by
  rw [cssPauliZX_phase, smul_smul, phaseOfBit_mul_self, one_smul]

/-- Multiplication of two binary Pauli products adds their labels and contributes the phase from
the first Z label paired with the second X label. This is the Pauli multiplication rule used
in [Gottesman1997]. -/
theorem cssPauliXZ_mul (x x' z z' : ι → ZMod 2) :
    (cssPauliX x * cssPauliZ z) * (cssPauliX x' * cssPauliZ z') =
      phaseOfBit (bitDot z x') • (cssPauliX (x + x') * cssPauliZ (z + z')) := by
  calc
    _ = cssPauliX x * ((cssPauliZ z * cssPauliX x') * cssPauliZ z') := by simp only [mul_assoc]
    _ = phaseOfBit (bitDot z x') • ((cssPauliX x * cssPauliX x') * (cssPauliZ z * cssPauliZ z')) := by
      rw [cssPauliZX_phase]
      simp only [Matrix.smul_mul, Matrix.mul_smul, mul_assoc]
    _ = _ := by rw [cssPauliX_mul, cssPauliZ_mul]

/-- Pairing a binary vector with the unit vector at `i` gives its coordinate at `i`. -/
theorem bitDot_single (z : ι → ZMod 2) (i : ι) :
    bitDot z (Pi.single i 1) = z i := by
  simp [bitDot, dotProduct, Pi.single_apply, mul_ite]

/-- The sum of the binary dot-product character is the number of binary vectors when its label
is zero and is zero otherwise. -/
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

/-- A binary Pauli product has trace equal to the ambient dimension when both labels vanish and
zero otherwise. This trace identity underlies stabilizer dimension counts in
[Gottesman1997]. -/
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

/-- The binary dot product is symmetric. -/
theorem bitDot_comm (x z : ι → ZMod 2) : bitDot x z = bitDot z x := by
  simp only [bitDot, dotProduct]
  apply Finset.sum_congr rfl
  intro i _
  exact mul_comm _ _

/-- Every binary X operator squares to the identity. -/
theorem cssPauliX_self_mul (x : ι → ZMod 2) : cssPauliX x * cssPauliX x = 1 := by
  rw [cssPauliX_mul, binary_add_self, cssPauliX_zero]

/-- Every binary Z operator squares to the identity. -/
theorem cssPauliZ_self_mul (z : ι → ZMod 2) : cssPauliZ z * cssPauliZ z = 1 := by
  rw [cssPauliZ_mul, binary_add_self, cssPauliZ_zero]

/-- Every binary phase is fixed by complex conjugation. -/
theorem phaseOfBit_star (b : ZMod 2) : star (phaseOfBit b) = phaseOfBit b := by
  by_cases h : b = 1 <;> simp [phaseOfBit, h]

/-- Every binary X operator is Hermitian. -/
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

/-- Every binary Z operator is Hermitian. -/
theorem cssPauliZ_isHermitian (z : ι → ZMod 2) : (cssPauliZ z).IsHermitian := by
  classical
  apply Matrix.IsHermitian.ext
  intro a b
  by_cases h : a = b
  · subst b
    simpa [cssPauliZ, Matrix.diagonal_apply] using phaseOfBit_star (bitDot z a)
  · simp [cssPauliZ, Matrix.diagonal_apply, h, Ne.symm h]

end Qatlib.Concepts.CodingDecoding.CssTesters
