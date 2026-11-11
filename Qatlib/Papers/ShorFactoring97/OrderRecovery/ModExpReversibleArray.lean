/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Data.ZMod.Basic
import Mathlib.Data.Nat.Log
import Mathlib.Tactic

set_option backward.isDefEq.respectTransparency false

/-!
# Shor 1997 §3 — register-level reversible modular exponentiation (Dev)

Fixed source: `quant-ph/9508027v2` §3, the paragraphs beginning "We will now
give the method for constructing a reversible gate array that takes only `O(l)`
space and `O(l³)` time to compute `(a, x^a (mod n))` from `a`" up to the
`power`/`result` pseudocode (printed pp.10–12).  This module formalizes the
functional content of claim `c002`:

* the elementary reversible block `b ↦ b + c (mod n)`;
* multiplication from repeated addition (the paper's first stage) and the
  two-stage array that sends `(b, 0)` to `(0, b·c (mod n))`, erasing `b` with
  the precomputed multiples of `c⁻¹` (the paper's second stage);
* the repeated-squaring exponentiation loop that sends `(a, 1)` to
  `(a, x^a (mod n))` and leaves the exponent register untouched;
* reversibility: each stage is a permutation of the register space, so the whole
  array is a permutation; the exponentiation array is a permutation whenever the
  base is a unit.

These definitions certify functions and register permutations. They do not
construct a local quantum gate word or certify its scratch space. Conditional
numeric ledgers are in `ModExpResourceBound` and do not close the resource claim.
-/

set_option autoImplicit false

namespace Qatlib.Papers.ShorFactoring97.OrderRecovery

/-! ## §1. The elementary reversible block `b ↦ b + c (mod n)` -/

/-- The paper's basic reversible gate array: addition of the fixed residue `c`
modulo `n`.  Both `c` and `n` are built into the gate array, and the inverse is
subtraction of `c`, so the array is a permutation of the `n` residue states. -/
def addModEquiv (n : ℕ) [NeZero n] (c : ZMod n) : ZMod n ≃ ZMod n where
  toFun b := b + c
  invFun b := b - c
  left_inv b := by simp
  right_inv b := by simp

/-- The elementary block acts on residues as `b ↦ b + c`. -/
theorem addModEquiv_apply (n : ℕ) [NeZero n] (c b : ZMod n) :
    addModEquiv n c b = b + c := rfl

/-- Multiplication by a fixed unit modulo `n`.  The paper stresses that this step
is reversible only when `c` and `n` have no common factor, which is exactly
unit-ness of `c`; the inverse multiplies by `c⁻¹`. -/
def mulModEquiv (n : ℕ) [NeZero n] (c : (ZMod n)ˣ) : ZMod n ≃ ZMod n where
  toFun b := b * (c : ZMod n)
  invFun b := b * ((c⁻¹ : (ZMod n)ˣ) : ZMod n)
  left_inv b := by
    show b * (c : ZMod n) * ((c⁻¹ : (ZMod n)ˣ) : ZMod n) = b
    rw [mul_assoc, ← Units.val_mul, mul_inv_cancel, Units.val_one, mul_one]
  right_inv b := by
    show b * ((c⁻¹ : (ZMod n)ˣ) : ZMod n) * (c : ZMod n) = b
    rw [mul_assoc, ← Units.val_mul, inv_mul_cancel, Units.val_one, mul_one]

/-- The unit-multiplication block acts on residues as `b ↦ b · c`. -/
theorem mulModEquiv_apply (n : ℕ) [NeZero n] (c : (ZMod n)ˣ) (b : ZMod n) :
    mulModEquiv n c b = b * (c : ZMod n) := rfl

/-! ## §2. Multiplication from repeated addition (the paper's first stage) -/

/-- The first stage of the multiplication array, at gate level: `l` rounds of
repeated addition.  Round `i` adds the precomputed multiple `2^i·c (mod n)`
exactly when the `i`-th bit of `b` is set.  The weight `w` is the precomputed
`2^i·c`; it starts at `c` and is doubled at every round, mirroring the paper's
`result := result + 2^i c (mod n)`. -/
def mulByAdd (n : ℕ) [NeZero n] (c : ZMod n) : ℕ → ℕ → ZMod n → ZMod n
  | 0, _, _ => 0
  | l + 1, b, w => (if b % 2 = 1 then w else 0) + mulByAdd n c l (b / 2) (2 * w)

/-- One round of the repeated-addition loop contributes exactly the weight of
the current bit of `b`. -/
theorem mulByAdd_bit (n : ℕ) (w : ZMod n) (b : ℕ) :
    (if b % 2 = 1 then w else 0) = ((b % 2 : ℕ) : ZMod n) * w := by
  rcases Nat.mod_two_eq_zero_or_one b with h | h <;> simp [h]

/-- **The first stage is correct**: on an `l`-bit input `b`, repeated addition of
the precomputed multiples of the starting weight `w` accumulates exactly
`b · w (mod n)`.  Starting the loop at `w = c` is the paper's multiplication
`b ↦ b·c (mod n)` obtained from repeated addition. -/
theorem mulByAdd_eq (n : ℕ) [NeZero n] (c : ZMod n) (l b : ℕ) (w : ZMod n)
    (hb : b < 2 ^ l) : mulByAdd n c l b w = (b : ZMod n) * w := by
  induction l generalizing b w with
  | zero =>
    have hb0 : b = 0 := by simpa using hb
    subst hb0
    simp [mulByAdd]
  | succ l ih =>
    have hdiv : b / 2 < 2 ^ l := by
      have h : b < 2 * 2 ^ l := by simpa [pow_succ'] using hb
      exact Nat.div_lt_of_lt_mul h
    rw [mulByAdd, ih (b := b / 2) (w := 2 * w) hdiv, mulByAdd_bit]
    have hcast : (b : ZMod n) = ((b % 2 : ℕ) : ZMod n) + ((2 * (b / 2) : ℕ) : ZMod n) := by
      have hb' : b = b % 2 + 2 * (b / 2) := by omega
      conv_lhs => rw [hb']
      push_cast
      ring
    rw [hcast, add_mul]
    congr 1
    push_cast
    ring

/-- The first stage started at the weight `c` computes `b·c (mod n)`: this is
the paper's "multiplication from repeated addition". -/
theorem mulByAdd_eq_mul (n : ℕ) [NeZero n] (c : ZMod n) (l b : ℕ) (hb : b < 2 ^ l) :
    mulByAdd n c l b c = (b : ZMod n) * c :=
  mulByAdd_eq n c l b c hb

/-! ## §3. The two-stage array and its reversibility -/

/-- The first stage as a permutation of the register space `(b, result)`: for
each value of the input register the result register is translated, so the stage
is reversible. -/
def mulStageEquiv (n : ℕ) [NeZero n] (c : ZMod n) : ZMod n × ZMod n ≃ ZMod n × ZMod n where
  toFun y := (y.1, y.2 + y.1 * c)
  invFun y := (y.1, y.2 - y.1 * c)
  left_inv y := by
    rcases y with ⟨b, r⟩
    simp
  right_inv y := by
    rcases y with ⟨b, r⟩
    simp

/-- On an `l`-bit input the first stage is exactly the register-level repeated
addition of `mulByAdd`: the translation by `b·c` is accumulated bit by bit. -/
theorem mulStageEquiv_eq_mulByAdd (n : ℕ) [NeZero n] (c : ZMod n) (l b : ℕ)
    (r : ZMod n) (hb : b < 2 ^ l) :
    mulStageEquiv n c ((b : ZMod n), r) = ((b : ZMod n), r + mulByAdd n c l b c) := by
  rw [mulStageEquiv, mulByAdd_eq_mul n c l b hb]
  rfl

/-- The second stage of the paper's array: erase `b` by subtracting the
precomputed `2^i·c⁻¹ (mod n)` at every set bit of the accumulated result
register. -/
def eraseBySub (n : ℕ) [NeZero n] (cinv : ZMod n) (l r : ℕ) (b : ZMod n) : ZMod n :=
  b - mulByAdd n cinv l r cinv

/-- The erasure stage subtracts `r·c⁻¹` from `b` on an `l`-bit result register. -/
theorem eraseBySub_eq (n : ℕ) [NeZero n] (cinv : ZMod n) (l r : ℕ) (b : ZMod n)
    (hr : r < 2 ^ l) : eraseBySub n cinv l r b = b - (r : ZMod n) * cinv := by
  rw [eraseBySub, mulByAdd_eq n cinv l r cinv hr]

/-- The erasure stage as a permutation of the register space: the result
register `r` selects a translation of the input register, so the stage is
reversible. -/
def eraseStageEquiv (n : ℕ) [NeZero n] (cinv : ZMod n) :
    ZMod n × ZMod n ≃ ZMod n × ZMod n where
  toFun y := (y.1 - y.2 * cinv, y.2)
  invFun y := (y.1 + y.2 * cinv, y.2)
  left_inv y := by
    rcases y with ⟨b, r⟩
    simp
  right_inv y := by
    rcases y with ⟨b, r⟩
    simp

/-- **The two-stage array is correct**: composed on the initial state
`(b, 0)` it produces `(0, b·c (mod n))` — the product survives in the result
register and the input register is erased.  Erasure works because `c` is
invertible modulo `n`, i.e. because the reduction step is a group
multiplication. -/
theorem mulArray_correct (n : ℕ) [NeZero n] (c cinv : ZMod n) (hcc : c * cinv = 1)
    (b : ZMod n) :
    eraseStageEquiv n cinv (mulStageEquiv n c (b, 0)) = (0, b * c) := by
  rw [mulStageEquiv, eraseStageEquiv]
  simp only [Equiv.coe_fn_mk, zero_add]
  have hprod : b * c * cinv = b := by
    rw [mul_assoc, hcc, mul_one]
  rw [hprod, sub_self]

/-! ## §4. Repeated-squaring exponentiation -/

/-- The paper's repeated-squaring exponentiation loop at gate level: `l` rounds.
Round `i` multiplies the running product by the precomputed power `x^(2^i)`
exactly when the `i`-th bit of the exponent `a` is set.  The weight `w` is that
precomputed power; it starts at `x` and is squared at every round. -/
def powBySquare (n : ℕ) [NeZero n] (x : ZMod n) : ℕ → ℕ → ZMod n → ZMod n → ZMod n
  | 0, _, p, _ => p
  | l + 1, a, p, w => powBySquare n x l (a / 2) (if a % 2 = 1 then p * w else p) (w * w)

/-- One round of the exponentiation loop multiplies by `w` exactly at the set
bits of the exponent. -/
theorem powBySquare_bit (n : ℕ) [NeZero n] (p w : ZMod n) (a : ℕ) :
    (if a % 2 = 1 then p * w else p) = p * w ^ (a % 2) := by
  rcases Nat.mod_two_eq_zero_or_one a with h | h <;> simp [h]

/-- **The exponentiation loop is correct**: on an `l`-bit exponent it computes
`p · w^a`; the paper runs it with `p = 1`, `w = x`, giving `x^a (mod n)`. -/
theorem powBySquare_eq (n : ℕ) [NeZero n] (x p w : ZMod n) (l a : ℕ) (ha : a < 2 ^ l) :
    powBySquare n x l a p w = p * w ^ a := by
  induction l generalizing a p w with
  | zero =>
    have ha0 : a = 0 := by simpa using ha
    subst ha0
    simp [powBySquare]
  | succ l ih =>
    have hdiv : a / 2 < 2 ^ l := by
      have h : a < 2 * 2 ^ l := by simpa [pow_succ'] using ha
      exact Nat.div_lt_of_lt_mul h
    rw [powBySquare, ih (a := a / 2) (p := if a % 2 = 1 then p * w else p)
      (w := w * w) hdiv, powBySquare_bit, mul_pow]
    rw [mul_assoc, ← pow_add, ← pow_add]
    congr 2
    omega

/-- The register-level loop output for `(a, 1)` is the power `x^a`. -/
theorem powModArray_eq (n : ℕ) [NeZero n] (x : ZMod n) (l a : ℕ) (ha : a < 2 ^ l) :
    powBySquare n x l a 1 x = x ^ a := by
  rw [powBySquare_eq n x 1 x l a ha, one_mul]

/-- The exponentiation array is reversible whenever the base is a unit: the map
`(a, p) ↦ (a, p·x^a)` is a permutation of the register space, with inverse
`(a, p) ↦ (a, p·(x⁻¹)^a)`.  This is the paper's claim that the modular
exponentiation can be performed by a reversible gate array. -/
def powStageEquiv (n : ℕ) [NeZero n] (x : (ZMod n)ˣ) (l : ℕ) :
    Fin (2 ^ l) × ZMod n ≃ Fin (2 ^ l) × ZMod n where
  toFun y := (y.1, y.2 * ((x : ZMod n) ^ y.1.val))
  invFun y := (y.1, y.2 * (((x⁻¹ : (ZMod n)ˣ) : ZMod n) ^ y.1.val))
  left_inv y := by
    have h : (x : ZMod n) * ((x⁻¹ : (ZMod n)ˣ) : ZMod n) = 1 := by
      rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
    rcases y with ⟨a, p⟩
    simp only [Prod.mk.injEq, true_and]
    rw [mul_assoc, ← mul_pow, h, one_pow, mul_one]
  right_inv y := by
    have h : ((x⁻¹ : (ZMod n)ˣ) : ZMod n) * (x : ZMod n) = 1 := by
      rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
    rcases y with ⟨a, p⟩
    simp only [Prod.mk.injEq, true_and]
    rw [mul_assoc, ← mul_pow, h, one_pow, mul_one]

/-- The permutation implemented by the array is exactly the result of the
register-level loop `powBySquare`: the two presentations agree on every state. -/
theorem powStageEquiv_apply (n : ℕ) [NeZero n] (x : (ZMod n)ˣ) (l : ℕ)
    (a : Fin (2 ^ l)) (p : ZMod n) :
    powStageEquiv n x l (a, p) = (a, powBySquare n (x : ZMod n) l a.val p x) := by
  rw [powBySquare_eq n (x : ZMod n) p x l a.val a.isLt]
  rfl

/-- **The reversible array of the paper sends `(a, 1)` to `(a, x^a (mod n))`**: the
exponent register is untouched and the second register holds the power.  This is
the paper's headline statement for the modular-exponentiation gate array. -/
theorem powModArray_full (n : ℕ) [NeZero n] (x : (ZMod n)ˣ) (l : ℕ)
    (a : Fin (2 ^ l)) :
    powStageEquiv n x l (a, 1) = (a, (x : ZMod n) ^ a.val) := by
  rw [powStageEquiv_apply, powModArray_eq n (x : ZMod n) l a.val a.isLt]

end Qatlib.Papers.ShorFactoring97.OrderRecovery
