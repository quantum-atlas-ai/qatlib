/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore, Qatlib Contributors
-/

import Qatlib.Concepts.UnbiasedBases.ThreeBasis.Register
import Mathlib.Algebra.BigOperators.Ring.Finset

/-!
# Binary characters and Pauli operators

This module constructs binary dot products, their sign characters, and the register operators
`pauliOp` with Z applied before X. It proves the Pauli multiplication and commutation formulas,
character sums, traces, and preservation of inner products used in quantum circuit theory
[NielsenChuang2010].

## Main statements

* `pauliOp_mul`: composition adds binary labels with a sign factor.
* `pauliOp_comm`: the binary symplectic pairing determines the commutation sign.
* `pauliOp_trace`: only the identity labels have nonzero trace.
* `inner_pauliOp`: Pauli operators preserve inner products.

## References

* [Nielsen and Chuang, 2010][NielsenChuang2010]
-/

section

open scoped ComplexConjugate

namespace Qatlib.Concepts.UnbiasedBases.ThreeBasis.QuantumInfo

variable {n : ℕ}

/-- The complex sign character on `Fin 2`, sending zero to one and one to minus one. -/
def signChar (v : Fin 2) : ℂ := if v = 0 then 1 else -1

/-- The sign character takes value one at zero. -/
@[simp] lemma signChar_zero : signChar 0 = 1 := rfl

/-- The sign character sends binary addition to complex multiplication. -/
lemma signChar_add (u v : Fin 2) : signChar (u + v) = signChar u * signChar v := by
  fin_cases u <;> fin_cases v <;>
    norm_num [signChar, show (1 + 1 : Fin 2) = 0 from rfl]

/-- The square of any value of `signChar` is one. -/
lemma signChar_mul_self (u : Fin 2) : signChar u * signChar u = 1 := by
  fin_cases u <;> norm_num [signChar]

/-- Complex conjugation fixes every value of `signChar`. -/
lemma conj_signChar (u : Fin 2) : conj (signChar u) = signChar u := by
  fin_cases u <;> simp [signChar]

/-- The sign character of a finite binary sum is the product of the individual sign characters. -/
lemma signChar_sum {κ : Type*} (s : Finset κ) (f : κ → Fin 2) :
    signChar (∑ i ∈ s, f i) = ∏ i ∈ s, signChar (f i) := by
  classical
  induction s using Finset.induction with
  | empty => simp
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.prod_insert ha, signChar_add, ih]

/-- Every element of `Fin 2` adds to itself to give zero. -/
lemma fin2_add_self (v : Fin 2) : v + v = 0 := by fin_cases v <;> rfl

/-- The dot product of binary vectors, computed as the sum of coordinate products in `Fin 2`. -/
def bdot (b z : Fin n → Fin 2) : Fin 2 := ∑ i, b i * z i

/-- The binary dot product is additive in its second argument. -/
lemma bdot_add_right (b z w : Fin n → Fin 2) : bdot b (z + w) = bdot b z + bdot b w := by
  rw [bdot, bdot, bdot, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Pi.add_apply, mul_add]

/-- The binary dot product is additive in its first argument. -/
lemma bdot_add_left (b b' z : Fin n → Fin 2) : bdot (b + b') z = bdot b z + bdot b' z := by
  rw [bdot, bdot, bdot, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Pi.add_apply, add_mul]

/-- The binary dot product with the zero vector in the second argument is zero. -/
@[simp] lemma bdot_zero_right (b : Fin n → Fin 2) : bdot b 0 = 0 := by
  simp [bdot]

/-- The binary dot product with the zero vector in the first argument is zero. -/
@[simp] lemma bdot_zero_left (z : Fin n → Fin 2) : bdot 0 z = 0 := by
  simp [bdot]

/-- The binary dot product is symmetric. -/
lemma bdot_comm (b z : Fin n → Fin 2) : bdot b z = bdot z b :=
  Finset.sum_congr rfl fun i _ => (by decide : ∀ x y : Fin 2, x * y = y * x) (b i) (z i)

/-- Updating coordinate `k` of the second vector to `v` adds `b k * (z k + v)` to its binary dot
product with `b`. -/
lemma bdot_update (b z : Fin n → Fin 2) (k : Fin n) (v : Fin 2) :
    bdot b (Function.update z k v) = bdot b z + b k * (z k + v) := by
  have hsum : bdot b (Function.update z k v) + bdot b z = b k * (z k + v) := by
    rw [bdot, bdot, ← Finset.sum_add_distrib,
      Finset.sum_eq_single k
        (fun i _ hik => by rw [Function.update_of_ne hik, fin2_add_self])
        (fun hk => absurd (Finset.mem_univ k) hk),
      Function.update_self]
    generalize b k = x
    generalize z k = y
    revert x y v
    decide
  calc bdot b (Function.update z k v)
      = bdot b (Function.update z k v) + (bdot b z + bdot b z) := by
        rw [fin2_add_self, add_zero]
    _ = bdot b (Function.update z k v) + bdot b z + bdot b z := by abel
    _ = b k * (z k + v) + bdot b z := by rw [hsum]
    _ = bdot b z + b k * (z k + v) := by abel

/-- Updating coordinate `k` of the first vector to `v` adds `z k * (b k + v)` to its binary dot
product with `z`. -/
lemma bdot_update_left (b z : Fin n → Fin 2) (k : Fin n) (v : Fin 2) :
    bdot (Function.update b k v) z = bdot b z + z k * (b k + v) := by
  rw [bdot_comm, bdot_update, bdot_comm z b]

/-- The complex sign character of the binary dot product of the two labels. -/
def pauliSign (b z : Fin n → Fin 2) : ℂ := signChar (bdot b z)

/-- Adding binary vectors in the second argument of `pauliSign` multiplies their signs. -/
lemma pauliSign_add_right (b z w : Fin n → Fin 2) :
    pauliSign b (z + w) = pauliSign b z * pauliSign b w := by
  rw [pauliSign, pauliSign, pauliSign, bdot_add_right, signChar_add]

/-- Adding binary vectors in the first argument of `pauliSign` multiplies their signs. -/
lemma pauliSign_add_left (b b' z : Fin n → Fin 2) :
    pauliSign (b + b') z = pauliSign b z * pauliSign b' z := by
  rw [pauliSign, pauliSign, pauliSign, bdot_add_left, signChar_add]

/-- The square of each Pauli sign is one. -/
lemma pauliSign_mul_self (b z : Fin n → Fin 2) : pauliSign b z * pauliSign b z = 1 :=
  signChar_mul_self _

/-- The Pauli sign with zero first label is one. -/
@[simp] lemma pauliSign_zero_left (z : Fin n → Fin 2) : pauliSign 0 z = 1 := by
  rw [pauliSign, bdot_zero_left, signChar_zero]

/-- Complex conjugation fixes every Pauli sign. -/
lemma conj_pauliSign (b z : Fin n → Fin 2) : conj (pauliSign b z) = pauliSign b z :=
  conj_signChar _

/-- The Pauli operation `X^a Z^b`, shifting binary basis labels by `a` after applying the sign
determined by `b`. -/
noncomputable def pauliOp (a b : Fin n → Fin 2) (ψ : QReg n) : QReg n :=
  (WithLp.equiv 2 ((Fin n → Fin 2) → ℂ)).symm
    (fun z => pauliSign b (z + a) * ψ (z + a))

/-- The amplitude at `z` after `pauliOp a b` is `pauliSign b (z + a)` times the input amplitude
at `z + a`. -/
@[simp] lemma pauliOp_apply (a b : Fin n → Fin 2) (ψ : QReg n) (z : Fin n → Fin 2) :
    pauliOp a b ψ z = pauliSign b (z + a) * ψ (z + a) := rfl

/-- The Pauli operator with both labels zero acts as the identity. -/
@[simp] lemma pauliOp_zero (ψ : QReg n) : pauliOp 0 0 ψ = ψ := by
  ext z
  rw [pauliOp_apply, pauliSign_zero_left, one_mul, add_zero]

/-- Pauli operators commute with complex scalar multiplication. -/
lemma pauliOp_smul (a b : Fin n → Fin 2) (c : ℂ) (ψ : QReg n) :
    pauliOp a b (c • ψ) = c • pauliOp a b ψ := by
  ext z
  rw [WithLp.ofLp_smul, Pi.smul_apply, pauliOp_apply, pauliOp_apply, WithLp.ofLp_smul,
    Pi.smul_apply, smul_eq_mul, smul_eq_mul]
  ring

/-- Pauli operators preserve addition of register states. -/
lemma pauliOp_add (a b : Fin n → Fin 2) (ψ χ : QReg n) :
    pauliOp a b (ψ + χ) = pauliOp a b ψ + pauliOp a b χ := by
  ext z
  rw [WithLp.ofLp_add, Pi.add_apply, pauliOp_apply, pauliOp_apply, pauliOp_apply,
    WithLp.ofLp_add, Pi.add_apply]
  ring

/-- Pauli operators distribute over finite sums of register states. -/
lemma pauliOp_sum {κ : Type*} (a b : Fin n → Fin 2) (s : Finset κ) (f : κ → QReg n) :
    pauliOp a b (∑ k ∈ s, f k) = ∑ k ∈ s, pauliOp a b (f k) := by
  ext z
  rw [pauliOp_apply, sum_coord, sum_coord, Finset.mul_sum]
  exact Finset.sum_congr rfl fun k _ => by rw [pauliOp_apply]

/-- The Pauli operator sends basis label `w` to `w + a`, multiplied by `pauliSign b w`. -/
lemma pauliOp_basisState (a b w : Fin n → Fin 2) :
    pauliOp a b (basisState w) = pauliSign b w • basisState (w + a) := by
  have haa : a + a = 0 := funext fun i => fin2_add_self _
  ext z
  rw [pauliOp_apply, WithLp.ofLp_smul, Pi.smul_apply, smul_eq_mul, basisState_apply,
    basisState_apply]
  by_cases h : z + a = w
  · rw [if_pos h, if_pos (by rw [← h, add_assoc, haa, add_zero]), h]
  · rw [if_neg h, if_neg (fun hz => h (by rw [hz, add_assoc, haa, add_zero])), mul_zero,
      mul_zero]

/-- Composing two Pauli operators adds their labels and contributes the sign `pauliSign b a'`. -/
theorem pauliOp_mul (a b a' b' : Fin n → Fin 2) (ψ : QReg n) :
    pauliOp a b (pauliOp a' b' ψ)
      = pauliSign b a' • pauliOp (a + a') (b + b') ψ := by
  ext z
  rw [WithLp.ofLp_smul, Pi.smul_apply, smul_eq_mul, pauliOp_apply, pauliOp_apply,
    pauliOp_apply, show z + a + a' = z + (a + a') from by rw [add_assoc], ← mul_assoc,
    ← mul_assoc]
  congr 1
  rw [pauliSign, pauliSign, pauliSign, pauliSign, ← signChar_add, ← signChar_add]
  congr 1
  rw [bdot_add_left, show z + (a + a') = z + a + a' from by rw [add_assoc],
    bdot_add_right b (z + a) a']
  generalize bdot b (z + a) = p
  generalize bdot b a' = q
  generalize bdot b' (z + a + a') = r
  revert p q r
  decide

/-- Swapping two Pauli operators contributes the sign of their binary symplectic pairing `bdot a
b' + bdot b a'`. -/
theorem pauliOp_comm (a b a' b' : Fin n → Fin 2) (ψ : QReg n) :
    pauliOp a b (pauliOp a' b' ψ)
      = signChar (bdot a b' + bdot b a') • pauliOp a' b' (pauliOp a b ψ) := by
  rw [pauliOp_mul, pauliOp_mul, smul_smul, show a' + a = a + a' from add_comm a' a,
    show b' + b = b + b' from add_comm b' b]
  congr 1
  rw [pauliSign, pauliSign, ← signChar_add, bdot_comm b' a]
  congr 1
  generalize bdot a b' = p
  generalize bdot b a' = q
  revert p q
  decide

/-- Pauli operators commute when the binary symplectic pairing of their labels is zero. -/
theorem pauliOp_comm_of_symp (a b a' b' : Fin n → Fin 2)
    (h : bdot a b' + bdot b a' = 0) (ψ : QReg n) :
    pauliOp a b (pauliOp a' b' ψ) = pauliOp a' b' (pauliOp a b ψ) := by
  rw [pauliOp_comm, h, signChar_zero, one_smul]

/-- Summing `signChar (u * v)` over binary `v` gives two for `u = 0` and zero otherwise. -/
lemma sum_signChar_mul (u : Fin 2) :
    (∑ v : Fin 2, signChar (u * v)) = if u = 0 then 2 else 0 := by
  fin_cases u <;> simp [Fin.sum_univ_two, signChar]

/-- The sum of `pauliSign b z` over all binary strings is `2 ^ n` when `b = 0` and zero
otherwise. -/
theorem sum_pauliSign (b : Fin n → Fin 2) :
    ∑ z : Fin n → Fin 2, pauliSign b z = if b = 0 then ((2 : ℂ) ^ n) else 0 := by
  have hfac : ∀ z : Fin n → Fin 2, pauliSign b z = ∏ i, signChar (b i * z i) := by
    intro z
    rw [pauliSign, bdot, signChar_sum]
  have hswap : (∏ i : Fin n, ∑ v : Fin 2, signChar (b i * v))
      = ∑ z ∈ Fintype.piFinset (fun _ : Fin n => (Finset.univ : Finset (Fin 2))),
          ∏ i, signChar (b i * z i) := Finset.prod_univ_sum _ _
  rw [Finset.sum_congr rfl fun z _ => hfac z, ← Fintype.piFinset_univ, ← hswap]
  rw [Finset.prod_congr rfl fun i _ => sum_signChar_mul (b i)]
  by_cases hb : b = 0
  · subst hb
    simp [Finset.prod_const, Finset.card_univ]
  · rw [if_neg hb]
    obtain ⟨i, hi⟩ := Function.ne_iff.mp hb
    have hi' : b i ≠ 0 := by simpa using hi
    exact Finset.prod_eq_zero (Finset.mem_univ i) (by rw [if_neg hi'])

/-- The sum of the diagonal basis amplitudes of `pauliOp a b` is `2 ^ n` for zero labels and
zero otherwise. -/
theorem pauliOp_trace (a b : Fin n → Fin 2) :
    ∑ z : Fin n → Fin 2, pauliOp a b (basisState z) z
      = if a = 0 ∧ b = 0 then ((2 : ℂ) ^ n) else 0 := by
  have hterm : ∀ z : Fin n → Fin 2,
      pauliOp a b (basisState z) z
        = (if a = 0 then 1 else 0) * pauliSign b (z + a) := by
    intro z
    rw [pauliOp_apply, basisState_apply]
    by_cases ha : a = 0
    · subst ha
      rw [add_zero, if_pos rfl, if_pos rfl, one_mul, mul_one]
    · rw [if_neg ha, if_neg (fun h : z + a = z => ha (by
        have h' : z + a = z + 0 := by rw [add_zero]; exact h
        exact add_left_cancel h')), mul_zero, zero_mul]
  rw [Finset.sum_congr rfl fun z _ => hterm z]
  by_cases ha : a = 0
  · subst ha
    have h1 : ∀ z : Fin n → Fin 2,
        ((if (0 : Fin n → Fin 2) = 0 then (1 : ℂ) else 0) * pauliSign b (z + 0))
          = pauliSign b z := by
      intro z
      rw [if_pos rfl, one_mul, add_zero]
    rw [Finset.sum_congr rfl fun z _ => h1 z, sum_pauliSign]
    by_cases hb : b = 0
    · rw [if_pos hb, if_pos ⟨rfl, hb⟩]
    · rw [if_neg hb, if_neg (fun h => hb h.2)]
  · rw [if_neg (fun h => ha h.1)]
    simp [if_neg ha]

/-- Applying the same Pauli operator to two register states preserves their inner product. -/
theorem inner_pauliOp (a b : Fin n → Fin 2) (ψ φ : QReg n) :
    inner ℂ (pauliOp a b ψ) (pauliOp a b φ) = inner ℂ ψ φ := by
  rw [PiLp.inner_apply, PiLp.inner_apply]
  refine Fintype.sum_equiv (Equiv.addRight a) _ _ fun z => ?_
  simp only [RCLike.inner_apply', pauliOp_apply, Equiv.coe_addRight, map_mul, conj_pauliSign]
  linear_combination (conj (ψ (z + a)) * φ (z + a)) * pauliSign_mul_self b (z + a)

end Qatlib.Concepts.UnbiasedBases.ThreeBasis.QuantumInfo
